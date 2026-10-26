"""How much of the 7 to 8 point rating miss is the horse (ability not known well enough) and how much is the single run (how the race was run)?

The question (26 Oct 2026): if a horse's true level were known to 2 to 4 points, the rest of the miss would be that run's own noise, trip,
pace, the horse against the field on the day. Two checks on the results files and the Racing Victoria PDF widths:

  A. Lag structure of the within-race rating. w = a run's wpr minus the mean wpr of its race. If a horse's level were fixed, the covariance
     of its w across runs would be the variance of ability and var(w) minus that covariance would be per-run noise. Reported for lags 1 to 4.
     noise_upper = sqrt(var(w) - cov1) also contains any real one-run drift, so it is an upper bound on per-run noise. The error of an ability
     estimate from k runs is about noise / sqrt(k).
  B. What explains a run's w after the fact (VIC/SA runs with PDF widths, 29 Apr to 24 Oct 2026). R2 of w on: the horse's earlier level
     (mean of its last 3 w), then plus measured trip (ground lost, width at 800m, mid-race width, final width, position and margin at 800m,
     early speed vs the field, barrier), then plus the finishing margin (circular, the rating is built from it: a ceiling only).

  PYTHONPATH=. python research/rating_noise_decomposition.py
"""
import glob
import os
import sys

import numpy as np
import pandas as pd

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'analysis', 'trip_map'))
import build_trip_map as B  # noqa: E402

ROOT = B.ROOT
KEY = ['meet_code', 'race_no', 'tab_no']


def widths():
    fs = sorted(glob.glob(os.path.join(ROOT, 'data', 'gps', 'rc_pdf_rail_*.parquet')))
    d = pd.concat([pd.read_parquet(f) for f in fs], ignore_index=True)
    d['meet_code'] = d.meet_code.astype(str)
    p = d.pivot_table(index=KEY, columns='from_m', values='rail_m', aggfunc='first')
    out = pd.DataFrame(index=p.index)
    out['w_final'] = p[200] if 200 in p.columns else np.nan
    near = pd.concat([p[c] for c in (1000, 600) if c in p.columns], axis=1).mean(axis=1, skipna=False)
    out['w800'] = (p[800] if 800 in p.columns else pd.Series(np.nan, index=p.index)).fillna(near)
    mid_cols = [c for c in p.columns if 300 < c < max(p.columns) and c != 200]
    out['w_mid'] = p[mid_cols].mean(axis=1, skipna=True) if mid_cols else np.nan
    return out.reset_index()


def r2(df, cols, y='w'):
    z = df.dropna(subset=cols + [y])
    X = np.column_stack([np.ones(len(z))] + [z[c].values for c in cols])
    b, *_ = np.linalg.lstsq(X, z[y].values, rcond=None)
    res = z[y].values - X @ b
    return 1 - res.var() / z[y].var(), len(z)


def main():
    res = B.load_results()
    res = res[res.wpr.notna() & (res.date >= '2022-01-01')].copy()
    cnt = res.groupby('race_id').wpr.transform('count')
    res = res[cnt >= 8].copy()
    res['w'] = res.wpr - res.groupby('race_id').wpr.transform('mean')
    h = res.sort_values(['horse_id', 'date', 'race_id'])
    g = h.groupby('horse_id')
    print(f'A. within-race rating w: {len(h):,} runs, {h.horse_id.nunique():,} horses, 2022 to {h.date.max().date()}')
    var_w = h.w.var()
    print(f'   var(w) = {var_w:.1f}  (sd {np.sqrt(var_w):.2f})')
    covs = {}
    for k in (1, 2, 3, 4):
        z = pd.DataFrame({'a': h.w, 'b': g.w.shift(-k)}).dropna()
        covs[k] = float(np.cov(z.a, z.b)[0, 1])
        print(f'   lag {k}: cov {covs[k]:.1f}  corr {z.a.corr(z.b):.3f}  n {len(z):,}')
    noise2 = var_w - covs[1]
    print(f'   per-run noise upper bound sd = sqrt(var - cov1) = {np.sqrt(noise2):.2f}; ability sd (persistent part) = sqrt(cov1) = {np.sqrt(covs[1]):.2f}')
    for k in (3, 5, 8):
        print(f'   an ability estimate from {k} runs is off by about {np.sqrt(noise2 / k):.1f} points (noise / sqrt({k}))')
    # prediction error of a plain mean of earlier runs, and an oracle that also sees later runs
    e1 = (h.w - g.w.transform(lambda s: s.shift(1).rolling(4).mean())).dropna()
    both = pd.concat([g.w.shift(k) for k in (1, 2, 3, 4, -1, -2, -3, -4)], axis=1)
    e2 = (h.w - both.mean(axis=1, skipna=False)).dropna()
    print(f'   miss of the mean of the last 4 runs: rmse {np.sqrt((e1 ** 2).mean()):.2f};  with the next 4 runs also known (oracle): rmse {np.sqrt((e2 ** 2).mean()):.2f}')

    # ---- B. what explains a run after the fact
    a = B.vicsa_runs(B.load_results())
    a['meet_code'] = a.meet_code.astype(str)
    a = a.merge(widths(), on=KEY, how='inner')
    fin = pd.read_csv(os.path.join(ROOT, 'race_results_2026.csv.gz'), usecols=['race_id', 'horse_id', 'marginFinish', 'wpr'], low_memory=False)
    a = a.merge(fin, on=['race_id', 'horse_id'], how='left').rename(columns={'wpr': 'wpr_run'})
    a = a[a.wpr_run.notna()].copy()
    a['w'] = a.wpr_run - a.groupby('race_id').wpr_run.transform('mean')
    # the horse's earlier level: mean of its last 3 within-race ratings from the results files
    hh = h[['race_id', 'horse_id', 'w']].rename(columns={'w': 'w_hist'})
    full = h[['horse_id', 'date', 'race_id', 'w']].copy()
    full['lvl'] = pd.concat([full.groupby('horse_id').w.shift(k) for k in (1, 2, 3)], axis=1).mean(axis=1, skipna=False)
    a = a.merge(full[['race_id', 'horse_id', 'lvl']], on=['race_id', 'horse_id'], how='left')
    for c in ('extra', 'w800', 'w_mid', 'w_final', 'settle', 'gap800', 'early', 'barfrac', 'lvl'):
        a[c + '_r'] = a[c] - a.groupby('race_id')[c].transform('mean')
    a['fin_margin'] = a.marginFinish.clip(lower=0, upper=15)
    a['fin_margin_r'] = a.fin_margin - a.groupby('race_id').fin_margin.transform('mean')
    a = a[a.groupby('race_id').race_id.transform('size') >= 8]
    print(f'\nB. after-the-fact explanation of w, VIC/SA runs with PDF widths: {len(a):,} runs, {a.race_id.nunique():,} races')
    sets = [('horse level (mean of last 3 w)', ['lvl_r']),
            ('+ barrier', ['lvl_r', 'barfrac_r']),
            ('+ ground lost and widths (800m, mid, final)', ['lvl_r', 'barfrac_r', 'extra_r', 'w800_r', 'w_mid_r', 'w_final_r']),
            ('+ position, margin and early speed at 800m', ['lvl_r', 'barfrac_r', 'extra_r', 'w800_r', 'w_mid_r', 'w_final_r', 'settle_r', 'gap800_r', 'early_r']),
            ('+ finishing margin (circular ceiling)', ['lvl_r', 'barfrac_r', 'extra_r', 'w800_r', 'w_mid_r', 'w_final_r', 'settle_r', 'gap800_r', 'early_r', 'fin_margin_r'])]
    common = a.dropna(subset=sets[-1][1] + ['w'])
    print(f'   complete rows {len(common):,}; sd of w {common.w.std():.2f}')
    for name, cols in sets:
        r, n = r2(common, cols)
        print(f'   {name:50s} R2 {r:.3f}   remaining sd {common.w.std() * np.sqrt(1 - r):.2f}')
    # the race-level shared part
    rm = a.groupby('race_id').wpr_run.mean()
    print(f'\n   (the race-level shared part, between-race sd of mean wpr, is not in w: sd {rm.std():.2f})')


if __name__ == '__main__':
    main()
