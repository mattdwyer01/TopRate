"""Ex-post look at the last 400m: what explains a runner's last-400m deficit once the race has been run? (26 Oct 2026)
Same VIC/SA population as closing_stage_study. Features known only after the race, added in steps (R2 on 2025 on, LightGBM fit before 2025):
  1 own early and mid deficits (E, M)   2 + position at 800m and margin of E-section speed vs field  3 + ground lost and rail width
  4 + speed profile (peak speed, where it peaked, early/mid/late speeds)   5 + field tempo (mean E of the race)
  PYTHONPATH=. python research/last400_expost_study.py
"""
import glob, os, sys
import lightgbm as lgb, numpy as np, pandas as pd
sys.path.insert(0, os.path.dirname(__file__))
import closing_stage_study as CS
P = dict(learning_rate=0.05, num_leaves=31, min_child_samples=100, subsample=0.8, subsample_freq=1, colsample_bytree=0.8, reg_lambda=5, verbose=-1, n_estimators=350)
d = CS.load()
r = pd.concat([pd.read_parquet(f, columns=['meet_code', 'race_no', 'tab_no', 'dist_vs_winner_m', 'rail_avg_m', 'speed_early_ms', 'speed_mid_ms', 'speed_late_ms', 'speed_peak_ms', 'peak_at', 'speed_avg_ms'])
               for f in sorted(glob.glob(os.path.join(CS.GPS, 'rc_gps_runs_*.parquet')))], ignore_index=True)
r['meet_code'] = r.meet_code.astype(str)
d = d.merge(r, on=['meet_code', 'race_no', 'tab_no'], how='left')
s = pd.concat([pd.read_parquet(f, columns=['meet_code', 'race_no', 'tab_no', 'from_m', 'pos']) for f in sorted(glob.glob(os.path.join(CS.GPS, 'rc_gps_sections_*.parquet')))], ignore_index=True)
s['meet_code'] = s.meet_code.astype(str)
s = s[(s.from_m >= 780) & (s.from_m <= 820)].groupby(['meet_code', 'race_no', 'tab_no']).pos.first().rename('pos800').reset_index()
d = d.merge(s, on=['meet_code', 'race_no', 'tab_no'], how='left')
d['pos800r'] = d.pos800 / d.nr
for c in ('speed_early_ms', 'speed_mid_ms', 'speed_late_ms', 'speed_peak_ms', 'peak_at', 'dist_vs_winner_m', 'rail_avg_m'):
    d[c] = pd.to_numeric(d[c], errors='coerce')
for c in ('speed_early_ms', 'speed_mid_ms', 'speed_late_ms', 'speed_peak_ms', 'peak_at', 'dist_vs_winner_m', 'rail_avg_m'):
    d[c + '_r'] = d[c] - d.groupby('key')[c].transform('mean')
d['f_E'] = d.groupby('key').d_E.transform('mean')
d['dist'] = d['dist']; d['barfrac'] = (d.barrier - 1) / (d.nr - 1)
steps = [('1 own early and mid deficits', ['d_E', 'd_M']),
         ('2 + position at 800m', ['pos800', 'pos800r']),
         ('3 + ground lost, rail width', ['dist_vs_winner_m_r', 'rail_avg_m_r']),
         ('4 + speed profile', ['speed_early_ms_r', 'speed_mid_ms_r', 'speed_peak_ms_r', 'peak_at_r']),
         ('5 + race tempo, distance, barrier', ['dist', 'barfrac', 'nr'])]
tr = d[d.date < '2025-01-01']; te = d[d.date >= '2025-01-01']
print(f'fit {len(tr):,} test {len(te):,}; sd of L {te.d_L.std():.3f}s')
cols = []
for nm, add in steps:
    cols += add
    m = lgb.LGBMRegressor(**P).fit(tr[cols], tr.d_L)
    pr = m.predict(te[cols]); y = te.d_L
    print(f'{nm:40s} R2 {1 - ((y - pr) ** 2).sum() / ((y - y.mean()) ** 2).sum():.3f}')
for c in ('d_E', 'd_M'):
    print(f'corr(d_L, {c}) = {te.d_L.corr(te[c]):+.2f}')
