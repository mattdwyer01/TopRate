"""Does the formula Proj hold on Hong Kong runs? (21 Oct 2026)

For every rated run in the runner-page store (data/tr_form) with at least one earlier rated run of the same horse, predict the run's rating with
projection.features.formula_projection as of the day before and compare with the rating TopRate gave it. Reported by venue group (Hong Kong vs Australia),
overall and for the Hong Kong runs of horses whose earlier runs are also all in Hong Kong. Run with PYTHONPATH=. python research/hk_proj_backtest.py
"""
import numpy as np
import pandas as pd

from projection import features as F

HK = ('happy valley', 'sha tin')

t = F.runner_page_runs()
print('runs', len(t), t.columns.tolist())
t = t.sort_values(['horse_id', 'date']).reset_index(drop=True)
vcol = 'track' if 'track' in t.columns else 'venue'
t['hk'] = t[vcol].astype(str).str.lower().str.contains('|'.join(HK))
print('HK runs', int(t.hk.sum()), 'of', len(t))

t = t[t.date >= '2023-01-01'].copy() if False else t
proj, n, sd, l3 = F.formula_projection(t.horse_id.values, t.date.values)
t['proj'], t['n'], t['l3'] = proj, n, l3
x = t[t.proj.notna() & t.wpr.notna()].copy()
x['err'] = x.wpr - x.proj
x['err_l3'] = x.wpr - x.l3

# an earlier run's venue group, to tell horses that have only raced in HK from mixed careers
x['grp'] = np.where(x.hk, 'HK', 'AU/other')
def rep(z, label):
    if len(z) < 20:
        print(f'{label:34s} n={len(z)} (too few)')
        return
    print(f'{label:34s} n={len(z):6d} bias={z.err.mean():+.2f} rmse={np.sqrt((z.err**2).mean()):.2f} rmse_l3={np.sqrt((z.err_l3**2).mean()):.2f}')
rep(x, 'all')
rep(x[~x.hk], 'target AU/other')
rep(x[x.hk], 'target HK')
for lo, hi in [(1, 2), (3, 5), (6, 99)]:
    z = x[(x.n >= lo) & (x.n <= hi)]
    rep(z[~z.hk], f'AU/other, {lo}-{hi} earlier runs')
    rep(z[z.hk], f'HK, {lo}-{hi} earlier runs')
# within-race ordering: only races with 6+ rated runners that are all projected
rows = []
for rid, z in x.groupby('raceId' if 'raceId' in x.columns else 'race_id'):
    if len(z) >= 6:
        rows.append((z.hk.iloc[0], z.proj.corr(z.wpr), (z.proj.idxmax() == z.wpr.idxmax())))
r = pd.DataFrame(rows, columns=['hk', 'corr', 'top_hit'])
print(r.groupby('hk').agg(races=('corr', 'size'), mean_corr=('corr', 'mean'), top_pick_is_best_run=('top_hit', 'mean')))
