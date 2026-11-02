"""What does a Melbourne Cup top-4 finisher look like going in? (2 Nov 2026)  Run with: PYTHONPATH=.:projection python research/cup_profile.py

Data: results files.  Cups = Flemington, 3200m, first Tuesday of November, field 15+, 2020-2025 (the files hold no 2018/2019 Cup and the 2017 Cup has no ratings,
so 6 Cups).  Pooled = every 2800m+ race with 8+ runners since 2019-07 (includes the Cups) for pointers that need more runners.
Ratings: results-file plain wpr put on the ATW scale of the race weight (wfa_scale.atw_offset, AR 168, a constant per horse and race, as TopRate's runner pages do),
so a 'going-in' figure is what the horse's page would have shown before the race.  Runs overseas are not in the results files (about 27% of Cup runners have no
rating), so those runners are excluded from rating tables and counted separately.
Outputs: A) what the placegetters ran in the Cup and what they had going in, B) top-4 rate by going-in rating (absolute and within the field), C) distance pointers,
D) other pointers (days since run, last start, age, weight, barrier, sex), E) the 2026 field on the same measures from the runner pages.  Read-only.
"""
import glob
import os
import sys

import numpy as np
import pandas as pd

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
sys.path.insert(0, ROOT)
sys.path.insert(0, os.path.join(ROOT, 'projection'))
os.environ.setdefault('PROJECTION_RATINGS', 'toprate')
import wfa_scale  # noqa: E402
import features as F  # noqa: E402

K = 8
COLS = ['race_id', 'date', 'track', 'distance', 'wpr', 'weightCarried', 'positionFinish', 'marginFinish', 'priceStarting', 'horse_id', 'horse', 'horse_age', 'horse_sex',
        'isBarrierTrial', 'race_class', 'field_size', 'horse_country', 'barrier']
pd.set_option('display.width', 250)
pd.set_option('display.max_columns', 40)


def load():
    fs = [f for f in sorted(glob.glob(os.path.join(ROOT, 'race_results_20*.csv.gz'))) if not f.endswith('_rc.csv.gz')]
    d = pd.concat([pd.read_csv(f, usecols=lambda c: c in COLS, low_memory=False) for f in fs], ignore_index=True)
    d['date'] = pd.to_datetime(d.date)
    d = d[d.isBarrierTrial.fillna(0) != 1]
    d = d[~F.is_jumps(d.race_class)]
    for c in ('wpr', 'weightCarried', 'positionFinish', 'marginFinish', 'priceStarting', 'distance', 'horse_age', 'field_size', 'barrier'):
        d[c] = pd.to_numeric(d[c], errors='coerce')
    d = d.dropna(subset=['horse_id', 'date']).drop_duplicates(['horse_id', 'date'], keep='last')
    return d.sort_values(['horse_id', 'date']).reset_index(drop=True)


def add_lags(d):
    """Previous K rated runs (newest first) of wpr, distance, date, positionFinish, field_size; n = how many."""
    rated = d.wpr.notna().values
    g = d.horse_id.values
    cum = pd.Series(rated.astype(int)).groupby(g).cumsum().values
    prior = cum - rated
    hp = np.flatnonzero(rated)
    first = pd.Series(np.arange(len(hp))).groupby(g[hp]).min()
    first_row = pd.Series(g).map(first).values
    for col in ('wpr', 'distance', 'positionFinish', 'field_size'):
        arr = d[col].values.astype(float)[hp]
        for k in range(1, K + 1):
            j = prior - k
            ok = (j >= 0) & ~np.isnan(first_row)
            out = np.full(len(d), np.nan)
            out[ok] = arr[(first_row[ok] + j[ok]).astype(int)]
            d[f'{col[:3]}{k}'] = out
    dt = d.date.values.astype('datetime64[D]').astype(float)[hp]
    for k in range(1, K + 1):
        j = prior - k
        ok = (j >= 0) & ~np.isnan(first_row)
        out = np.full(len(d), np.nan)
        out[ok] = dt[(first_row[ok] + j[ok]).astype(int)]
        d[f'dat{k}'] = out
    d['n'] = np.minimum(prior, K)
    return d


def features(t, off_col='off'):
    """Going-in measures from the lag columns (wpr lags already on the ATW scale of this race)."""
    W = t[[f'wpr{k}' for k in range(1, K + 1)]].values
    D = t[[f'dis{k}' for k in range(1, K + 1)]].values
    P = t[[f'pos{k}' for k in range(1, K + 1)]].values
    FS = t[[f'fie{k}' for k in range(1, K + 1)]].values
    t['last1'] = W[:, 0]
    t['last3'] = np.nanmean(W[:, :3], axis=1)
    t['peak8'] = np.nanmax(np.where(np.isnan(W), -np.inf, W), axis=1)
    t.loc[~np.isfinite(t.peak8), 'peak8'] = np.nan
    long_ = (D >= 2400)
    t['n24'] = np.nansum(long_, axis=1)
    t['n28'] = np.nansum(D >= 2800, axis=1)
    t['peak24'] = np.nanmax(np.where(long_ & ~np.isnan(W), W, -np.inf), axis=1)
    t.loc[~np.isfinite(t.peak24), 'peak24'] = np.nan
    t['placed24'] = np.nansum(long_ & (P <= 3), axis=1)
    t['last_dist'] = D[:, 0]
    t['max_dist'] = np.nanmax(np.where(np.isnan(D), -np.inf, D), axis=1)
    t['days_since'] = t.date.values.astype('datetime64[D]').astype(float) - t.dat1
    t['last_pos'] = P[:, 0]
    t['last_frac'] = P[:, 0] / FS[:, 0]
    return t


def band(s, edges, labels=None):
    return pd.cut(s, edges, labels=labels, right=False)


def toprate(x, col, edges, labels=None, minn=8):
    x = x[x[col].notna()].copy()
    x['b'] = band(x[col], edges, labels)
    r = x.groupby('b', observed=True).agg(n=('top4', 'size'), top4=('top4', 'mean'), win=('win', 'mean'))
    return r[r.n >= minn]


def show(title, r, base):
    print(f'-- {title}  (base top-4 rate {base * 100:.1f}%)')
    if r.empty:
        print('   (too few)')
        return
    for b, v in r.iterrows():
        print(f"   {str(b):16s} n={int(v.n):4d}  top-4 {v.top4 * 100:5.1f}%  (lift x{v.top4 / base:4.2f})  win {v.win * 100:4.1f}%")


def main():
    d = add_lags(load())
    print('results-file runs', len(d))
    d['off'] = [wfa_scale.atw_offset(int(a), s, dt.date().isoformat(), di, w) if pd.notna(a) and pd.notna(w) and pd.notna(di) else np.nan
                for a, s, dt, di, w in zip(d.horse_age.fillna(0), d.horse_sex, d.date, d.distance, d.weightCarried)]
    d['off'] = pd.to_numeric(d.off, errors='coerce')
    mask = (d.distance >= 2800) & (d.field_size >= 8) & (d.date >= '2019-07-01') & d.positionFinish.notna() & d.off.notna()
    t = d[mask].copy()
    for k in range(1, K + 1):
        t[f'wpr{k}'] = t[f'wpr{k}'] + t.off
    t = features(t)
    t['act'] = t.wpr + t.off
    t['top4'] = (t.positionFinish <= 4).astype(float)
    t['win'] = (t.positionFinish == 1).astype(float)
    cup = (t.track.astype(str).str.contains('Flemington')) & (t.distance == 3200) & (t.date.dt.month == 11) & (t.date.dt.weekday == 1) & (t.field_size >= 15) & (t.date >= '2020-01-01')
    t['cup'] = cup
    C = t[cup].copy()
    print('Cups', sorted(C.date.dt.strftime('%Y-%m-%d').unique()), 'runners', len(C), 'rated going-in (3+ earlier runs)', int((C.n >= 3).sum()), '| pooled 2800m+ runners', len(t))
    # within-field ranks and gaps
    for df in (C, t):
        grp = df.groupby('race_id')
        df['rk_last3'] = grp.last3.rank(ascending=False, method='min')
        df['rk_peak8'] = grp.peak8.rank(ascending=False, method='min')
        df['gap_last3'] = grp.last3.transform('max') - df.last3
        df['gap_peak8'] = grp.peak8.transform('max') - df.peak8
        df['wt_rel'] = df.weightCarried - grp.weightCarried.transform('mean')
        df['bar_frac'] = df.barrier / df.field_size

    print('\n=== A) What the Cup placegetters ran, and what they had going in (ATW scale, plain + weight offset) ===')
    rows = []
    for pos in (1, 2, 3, 4):
        x = C[C.positionFinish == pos]
        rows.append(dict(place=pos, runners=len(x), cup_run_rating=x.act.mean(), cup_run_min=x.act.min(), cup_run_max=x.act.max(), last3_in=x.last3.mean(), peak8_in=x.peak8.mean(),
                         last1_in=x.last1.mean(), rank_last3=x.rk_last3.mean(), unrated=int(x.last3.isna().sum())))
    x = C[C.positionFinish > 4]
    rows.append(dict(place='5+', runners=len(x), cup_run_rating=x.act.mean(), cup_run_min=x.act.min(), cup_run_max=x.act.max(), last3_in=x.last3.mean(), peak8_in=x.peak8.mean(),
                     last1_in=x.last1.mean(), rank_last3=x.rk_last3.mean(), unrated=int(x.last3.isna().sum())))
    print(pd.DataFrame(rows).round(1).to_string(index=False))
    print('\nBy Cup: field top-rated going-in (last3 / peak8) and the 1st..4th going-in last3 and peak8')
    for dt, g in C.groupby('date'):
        top = g[g.positionFinish <= 4].sort_values('positionFinish')
        print(f"  {dt.date()} field {len(g)}, rated {int(g.last3.notna().sum())}; field top last3 {g.last3.max():.1f} peak8 {g.peak8.max():.1f}; placegetters last3: "
              + ' '.join(f"{v:.0f}" if pd.notna(v) else '--' for v in top.last3) + ' | peak8: ' + ' '.join(f"{v:.0f}" if pd.notna(v) else '--' for v in top.peak8)
              + ' | Cup run: ' + ' '.join(f"{v:.0f}" if pd.notna(v) else '--' for v in top.act))
    base_c = C[C.n >= 3].top4.mean()
    base_p = t[t.n >= 3].top4.mean()
    Cr, Tr = C[C.n >= 3], t[t.n >= 3]

    print('\n=== B) Top-4 rate by going-in rating (runners with 3+ earlier rated runs) ===')
    show('Cups: last-3 average (ATW)', toprate(Cr, 'last3', [0, 90, 95, 98, 100, 102, 999], minn=5), base_c)
    show('Cups: peak of last 8 (ATW)', toprate(Cr, 'peak8', [0, 98, 101, 104, 107, 999], minn=5), base_c)
    show('Cups: rank in field by last-3', toprate(Cr, 'rk_last3', [1, 2, 4, 7, 11, 99], labels=['1', '2-3', '4-6', '7-10', '11+'], minn=5), base_c)
    show('Cups: points behind the field\'s best last-3', toprate(Cr, 'gap_last3', [0, 0.1, 3, 6, 10, 999], labels=['best', '0-3', '3-6', '6-10', '10+'], minn=5), base_c)
    show('Pooled 2800m+: points behind the field\'s best last-3', toprate(Tr, 'gap_last3', [0, 0.1, 3, 6, 10, 999], labels=['best', '0-3', '3-6', '6-10', '10+']), base_p)
    show('Pooled 2800m+: points behind the field\'s best peak8', toprate(Tr, 'gap_peak8', [0, 0.1, 3, 6, 10, 999], labels=['best', '0-3', '3-6', '6-10', '10+']), base_p)

    print('\n=== C) Distance pointers ===')
    for lab, df, b in (('Cups', Cr, base_c), ('Pooled 2800m+', Tr, base_p)):
        show(f'{lab}: distance of last start', toprate(df, 'last_dist', [0, 1800, 2200, 2600, 3000, 99999], labels=['<1800', '1800-2200', '2200-2600', '2600-3000', '3000+'], minn=5), b)
        show(f'{lab}: runs at 2400m+ in last 8', toprate(df, 'n24', [0, 1, 2, 4, 99], labels=['0', '1', '2-3', '4+'], minn=5), b)
        show(f'{lab}: runs at 2800m+ in last 8', toprate(df, 'n28', [0, 1, 2, 99], labels=['0', '1', '2+'], minn=5), b)
        show(f'{lab}: placed (top 3) at 2400m+ in last 8', toprate(df, 'placed24', [0, 1, 2, 99], labels=['0', '1', '2+'], minn=5), b)
        show(f'{lab}: longest distance run in last 8', toprate(df, 'max_dist', [0, 2200, 2600, 3000, 99999], labels=['<2200', '2200-2600', '2600-3000', '3000+'], minn=5), b)
    print('   peak rating at 2400m+ vs peak overall (gap = peak8 - peak24, when both exist):')
    Tr2 = Tr[Tr.peak24.notna() & Tr.peak8.notna()].copy()
    Tr2['p_gap'] = Tr2.peak8 - Tr2.peak24
    show('Pooled 2800m+: best 2400m+ rating is this far below best overall', toprate(Tr2, 'p_gap', [0, 0.1, 3, 6, 99], labels=['same', '0-3', '3-6', '6+']), base_p)

    print('\n=== D) Other pointers ===')
    for lab, df, b in (('Cups', Cr, base_c), ('Pooled 2800m+', Tr, base_p)):
        show(f'{lab}: days since last run', toprate(df, 'days_since', [0, 15, 29, 57, 120, 9999], labels=['<15', '15-28', '29-56', '57-119', '120+'], minn=5), b)
        show(f'{lab}: last start finish (place / field)', toprate(df, 'last_frac', [0, 0.01, 0.25, 0.5, 2], labels=['won/-', 'top quarter', 'mid', 'back half'], minn=5), b)
        show(f'{lab}: age', toprate(df, 'horse_age', [0, 5, 6, 7, 99], labels=['<=4', '5', '6', '7+'], minn=5), b)
        show(f'{lab}: weight relative to field mean (kg)', toprate(df, 'wt_rel', [-99, -2, -0.5, 1, 99], labels=['light', 'below', 'around', 'heavy'], minn=5), b)
        show(f'{lab}: barrier fraction', toprate(df, 'bar_frac', [0, 0.34, 0.67, 2], labels=['inside', 'middle', 'wide'], minn=5), b)
    for lab, df, b in (('Cups', Cr, base_c), ('Pooled 2800m+', Tr, base_p)):
        x = df.copy()
        x['sx'] = x.horse_sex.map(lambda s: 'horse/gelding' if s in ('H', 'G', 'C', 'R') else ('mare/filly' if s in ('M', 'F') else 'other'))
        r = x.groupby('sx').agg(n=('top4', 'size'), top4=('top4', 'mean'), win=('win', 'mean'))
        show(f'{lab}: sex', r[r.n >= 5].rename_axis('b'), b)

    # unrated runners in the Cups
    u = C[C.n < 3]
    print(f"\nCup runners with under 3 earlier rated runs in the results files (mostly internationals): {len(u)} of {len(C)}; top-4 finishers among them {int((u.positionFinish <= 4).sum())} "
          f"(top-4 rate {u.top4.mean() * 100:.1f}% against {base_c * 100:.1f}% for the rated runners); winners {int((u.positionFinish == 1).sum())}")
    print('   by horse_country (all Cup runners): top-4 rate / n')
    r = C.groupby(C.horse_country.fillna('?').map(lambda c: 'AUS' if c == 'AUS' else ('NZ' if c == 'NZ' else 'Other'))).agg(n=('top4', 'size'), top4=('top4', 'mean'), win=('win', 'mean'))
    print(r.round(3).to_string())

    C.to_csv(os.path.join(ROOT, 'research', 'cup_profile_cups.csv'), index=False) if os.environ.get('CUP_PROFILE_CSV') else None


if __name__ == '__main__':
    main()
