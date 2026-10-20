"""Does a closing profile (TOF or raw closing gain) say whether a horse suits stepping up or down in distance? (20 Oct 2026, analysis only)
Target = the next run's wpr minus the race mean. Control = last-3 wpr (demeaned in race). Question: after the control, does (profile x distance change) explain more?
Fit before 2025, score 2025+. Profiles are the horse's last-3 mean of: TOF (finish vs rating), closing gain over the last 400m from raw margins (no wpr), both demeaned in race.
usage: python analysis/horsetorque_edge/tof_distance.py"""
import os, sys
import numpy as np, pandas as pd
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from common import CACHE, asof_mean

F = pd.read_pickle(os.path.join(CACHE, 'features.pkl'))
w4 = F['margin400m'].where(F['win'] == 1).groupby(F['race_id']).transform('max')
F['cm400'] = ((F['margin400m'] - w4).clip(-25, 25) - F['marginFinish'].clip(lower=0, upper=25)).clip(-15, 15)
F.loc[w4.isna() | F['margin400m'].isna(), 'cm400'] = np.nan
F['cm400_m3'] = asof_mean(F, 'cm400', 3)
# the distance the profile was earned over: mean distance of the last 3 runs; change = today's distance minus that
F['dist_m3'] = asof_mean(F, 'distance', 3)
F['dchg'] = F['distance'] - F['dist_m3']
F = F[F.wpr.notna() & F.wpr_m3.notna() & F.TOF_m3.notna() & F.cm400_m3.notna() & F.dchg.notna() & (F.field_size >= 5)].copy()
dm = lambda c: F[c] - F.groupby('race_id')[c].transform('mean')
F['y'] = dm('wpr'); F['l3'] = dm('wpr_m3'); F['tof'] = dm('TOF_m3'); F['cl'] = dm('cm400_m3')
F['dk'] = F['dchg'] / 400.0                       # distance change in units of 400m
tr, te = F[F.date < '2025-01-01'], F[F.date >= '2025-01-01']
print(f'{len(tr):,} fit runs, {len(te):,} test runs')


def fit(cols, name):
    X = tr[cols].values; b = np.linalg.lstsq(X, tr.y.values, rcond=None)[0]
    r = te.y.values - te[cols].values @ b
    return np.sqrt(np.mean(r ** 2)), b


rows = []
base = ['l3']
for name, prof in (('TOF', 'tof'), ('closing gain (raw margins)', 'cl')):
    F[prof + '_dk'] = F[prof] * F['dk']; tr = F[F.date < '2025-01-01']; te = F[F.date >= '2025-01-01']
    r0, _ = fit(base + ['dk'], 'base'); r1, _ = fit(base + ['dk', prof], 'main'); r2, b = fit(base + ['dk', prof, prof + '_dk'], 'int')
    rows.append((name, r0, r1, r2, b[-1], (r1 - r2) / r0 * 100))
print('\nRMSE of next-run wpr (race-demeaned), test 2025+. Interaction = profile x distance change (per 400m).')
print(f"{'profile':30s} {'L3+dist':>8s} {'+profile':>9s} {'+interaction':>13s} {'interaction coef':>17s} {'gain from interaction %':>24s}")
for n, a, b_, c, k, g in rows:
    print(f'{n:30s} {a:8.4f} {b_:9.4f} {c:13.4f} {k:+17.3f} {g:24.3f}')

# table: mean residual after L3 by profile tercile and distance change bucket (test period)
tr = F[F.date < '2025-01-01']; te = F[F.date >= '2025-01-01'].copy()
b = np.linalg.lstsq(tr[['l3']].values, tr.y.values, rcond=None)[0]
te['res'] = te.y - te.l3 * b[0]
te['db'] = pd.cut(te.dchg, [-9999, -250, 250, 9999], labels=['down 250m+', 'same (+-250m)', 'up 250m+'])
for name, prof in (('TOF', 'tof'), ('Closing gain', 'cl')):
    te['pt'] = pd.qcut(te[prof], 3, labels=['faded (low)', 'middle', 'finished strong (high)'])
    t = te.pivot_table(index='pt', columns='db', values='res', aggfunc=['mean', 'size'], observed=True)
    print(f'\n{name}: mean next-run rating minus what L3 predicts (rating points), by profile tercile (rows) and distance change (cols)')
    print(t['mean'].round(2).to_string()); print('n:'); print(t['size'].to_string())
    for lab in ('down 250m+', 'up 250m+'):
        hi = te[(te.pt == 'finished strong (high)') & (te.db == lab)].res; lo = te[(te.pt == 'faded (low)') & (te.db == lab)].res
        d = hi.mean() - lo.mean(); se = np.sqrt(hi.var() / len(hi) + lo.var() / len(lo))
        print(f'  {lab}: strong minus faded = {d:+.2f} pts (se {se:.2f})')
