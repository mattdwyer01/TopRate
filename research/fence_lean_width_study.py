"""Fence lean redone with the RIGHT width (26 Oct 2026).

racing.com's `rail_avg_m` is the distance off the rail in the FINAL 200m (corr 1.000 with the PDF's L200 reading), so the meeting
"fence lean" (meeting_lean.py: rank correlation of that width with the finishing order) and the earlier fence-line study measured the
finishing straight, where horses fan out looking for room. The Racing Victoria PDFs (rc_pdf_gps.py) give the width through the race,
so this redoes the question with the width at 800m and through the middle of the race:

  1. Race-level lean = Spearman(width, finishing order), + when horses nearer the fence finished better, for: final width (what the
     dashboard line used), width at 800m, width at 400m, mean of the middle sections.
  2. Carry-over inside a meeting: does the mean lean of EARLIER races at the meeting (3 or more) predict the lean of a later race?
  3. Does it matter for ratings: per runner, rating residual (the run's wpr minus the mean of its last 3, minus the race mean) against
     barrier fraction x the earlier-races lean (positive lean = the fence is good, so inside barriers should run above their rating).

  PYTHONPATH=. python research/fence_lean_width_study.py
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
    w800 = p[800] if 800 in p.columns else pd.Series(np.nan, index=p.index)
    near = pd.concat([p[c] for c in (1000, 600) if c in p.columns], axis=1).mean(axis=1, skipna=False)
    out['w800'] = w800.fillna(near)
    out['w400'] = p[400] if 400 in p.columns else np.nan
    mid_cols = [c for c in p.columns if 300 < c < max(p.columns) and c != 200]
    out['w_mid'] = p[mid_cols].mean(axis=1, skipna=True) if mid_cols else np.nan
    out['n_pts'] = p.notna().sum(axis=1)
    return out.reset_index()


def spear(a, b):
    d = pd.DataFrame({'a': a, 'b': b}).dropna()
    if len(d) < 6 or d.a.nunique() < 2 or d.b.nunique() < 2:
        return np.nan
    return d.a.rank().corr(d.b.rank())


def main():
    res = B.load_results()
    a = B.vicsa_runs(res)
    a['meet_code'] = a.meet_code.astype(str)
    runs = pd.concat([pd.read_parquet(f, columns=KEY + ['finish']) for f in sorted(glob.glob(os.path.join(ROOT, 'data', 'gps', 'rc_gps_runs_*.parquet')))])
    runs['meet_code'] = runs.meet_code.astype(str)
    runs = runs.drop_duplicates(KEY)
    runs = runs[(runs.finish >= 1) & (runs.finish < 100)]
    d = a.merge(widths(), on=KEY).merge(runs, on=KEY)
    d['fin'] = d.finish
    print('runs', len(d), 'races', d.groupby(['meet_code', 'race_no']).ngroups, 'meetings', d.meet_code.nunique(), d.date.min().date(), 'to', d.date.max().date())

    # ---- 1. race-level lean for each width measure
    measures = ['w_final', 'w800', 'w400', 'w_mid', 'barrier']
    rows = []
    for (m, r), z in d.groupby(['meet_code', 'race_no']):
        if len(z) < 8:
            continue
        rows.append(dict(meet_code=m, race_no=int(r), n=len(z), date=z.date.iloc[0], **{k: spear(z[k], z.fin) for k in measures}))
    L = pd.DataFrame(rows).sort_values(['meet_code', 'race_no'])
    print('\n=== 1. race-level lean (Spearman of width with finishing order; + = nearer the fence finished better), races with 8+ runners:', len(L))
    print(L[measures].describe().loc[['count', 'mean', 'std']].round(3).to_string())
    print('corr between race-level leans:'); print(L[measures].corr().round(2).to_string())
    print('share of races with lean >= +0.35:', {k: round(float((L[k] >= 0.35).mean()), 3) for k in measures[:4]})

    # ---- 2. carry-over inside the meeting
    print('\n=== 2. carry-over: lean of a race against the mean lean of the EARLIER races at the meeting (3+ earlier races)')
    for k in measures:
        L['prev_' + k] = L.groupby('meet_code')[k].transform(lambda s: s.shift(1).expanding().mean())
        L['nprev'] = L.groupby('meet_code')[k].transform(lambda s: s.shift(1).expanding().count())
        z = L[(L.nprev >= 3)].dropna(subset=[k, 'prev_' + k])
        if len(z) > 30:
            b = np.polyfit(z['prev_' + k], z[k], 1)
            c = z[[k, 'prev_' + k]].corr().iloc[0, 1]
            print(f'{k:8s} n={len(z):4d}  slope {b[0]:+.2f}  corr {c:+.2f}  (a slope of 0 means no carry-over)')

    # ---- 3. effect on ratings
    h = res[['horse_id', 'date', 'wpr', 'race_id']].dropna(subset=['wpr']).sort_values(['horse_id', 'date', 'race_id'])
    h['p123'] = pd.concat([h.groupby('horse_id').wpr.shift(k) for k in (1, 2, 3)], axis=1).mean(axis=1)
    d = d.merge(h[['race_id', 'horse_id', 'wpr', 'p123']], on=['race_id', 'horse_id'], how='left')
    d['y'] = d.wpr - d.p123
    d['y'] -= d.groupby(['meet_code', 'race_no']).y.transform('mean')
    d['bf'] = d.barfrac - d.groupby(['meet_code', 'race_no']).barfrac.transform('mean')
    print('\n=== 3. rating residual (run wpr minus last-3 mean, demeaned in race) on barrier fraction x earlier-races lean')
    print('   (a positive coefficient on bf x lean would mean wide barriers run ABOVE their rating when the fence is good: the sign is expected NEGATIVE)')
    for k in measures[:4]:
        L2 = L[['meet_code', 'race_no', 'prev_' + k, 'nprev']].rename(columns={'prev_' + k: 'prev'})
        z = d.merge(L2, on=['meet_code', 'race_no'])
        z = z[(z.nprev >= 3)].dropna(subset=['y', 'bf', 'prev'])
        z['x'] = z.bf * z.prev
        X = np.column_stack([np.ones(len(z)), z.x.values])
        yv = z.y.values
        beta, *_ = np.linalg.lstsq(X, yv, rcond=None)
        r_ = yv - X @ beta
        se = np.sqrt(r_.var(ddof=2) * np.linalg.inv(X.T @ X)[1, 1])
        hi = z[z.prev >= 0.2]
        print(f'{k:8s} n={len(z):5d} coef {beta[1]:+.2f} (t {beta[1] / se:+.1f}); races with earlier lean >= +0.2: {hi.groupby(["meet_code", "race_no"]).ngroups} races, '
              f'inside third vs wide third rating residual {hi[hi.bf < -0.15].y.mean():+.2f} vs {hi[hi.bf > 0.15].y.mean():+.2f}')

    # ---- 4. does the width lean carry anything beyond the draw lean? (the two are correlated: the fence is usually best when the inside draws are)
    print('\n=== 4. joint regression: bf x earlier BARRIER lean and bf x earlier WIDTH lean together (which one carries the rating effect?)')
    for k in ('w_final', 'w800', 'w_mid'):
        Lb = L[['meet_code', 'race_no', 'prev_barrier', 'prev_' + k, 'nprev']]
        z = d.merge(Lb, on=['meet_code', 'race_no'])
        z = z[z.nprev >= 3].dropna(subset=['y', 'bf', 'prev_barrier', 'prev_' + k])
        X = np.column_stack([np.ones(len(z)), (z.bf * z.prev_barrier).values, (z.bf * z['prev_' + k]).values])
        yv = z.y.values
        beta, *_ = np.linalg.lstsq(X, yv, rcond=None)
        r_ = yv - X @ beta
        cov = r_.var(ddof=3) * np.linalg.inv(X.T @ X)
        se = np.sqrt(np.diag(cov))
        print(f'{k:8s} n={len(z):5d}  barrier lean coef {beta[1]:+.2f} (t {beta[1] / se[1]:+.1f})   {k} lean coef {beta[2]:+.2f} (t {beta[2] / se[2]:+.1f})')


if __name__ == '__main__':
    main()
