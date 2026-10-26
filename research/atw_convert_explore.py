"""Explore: runner-page rating (ATW) minus results-file plain wpr per run, versus the weight carried. Run with PYTHONPATH=."""
import glob, gzip, json
import numpy as np, pandas as pd
rows = []
for f in sorted(glob.glob('data/tr_form/*.json.gz')):
    for r in json.load(gzip.open(f, 'rt'))['runs'].values():
        if r.get('isBarrierTrial') or r.get('isJumpout') or r.get('wpr') is None: continue
        rows.append((r['horse_id'], r['date'], r['wpr'], r.get('weightCarried'), r.get('distance')))
P = pd.DataFrame(rows, columns=['horse_id', 'date', 'pg', 'pw', 'pd_'])
R = pd.concat([pd.read_csv(f, usecols=['horse_id', 'date', 'wpr', 'weightCarried', 'horse_age', 'horse_sex', 'wprStatus', 'distance', 'race_class'], low_memory=False)
               for f in sorted(glob.glob('race_results_20[12]*.csv.gz')) if '_rc' not in f])
R = R.dropna(subset=['wpr']).drop_duplicates(['horse_id', 'date'])
M = P.merge(R, on=['horse_id', 'date'])
M['off'] = M.pg - M.wpr
print(len(P), len(M), M.date.min(), M.date.max())
print(M.off.describe()); print((M.pw - M.weightCarried).abs().describe())
print(M.groupby(M.date.str[:7]).off.agg(['count','mean','std']).tail(24))
# within-horse: offset constant?
g = M.groupby('horse_id').off
print('within-horse sd of offset', (M.off - g.transform('median')).abs().mean(), 'between-horse sd', g.median().std())
# slope of offset on own weight within horse
M['wd'] = M.weightCarried - M.groupby('horse_id').weightCarried.transform('mean')
M['od'] = M.off - g.transform('mean')
m = M.dropna(subset=['wd', 'od']); m = m[m.groupby('horse_id').horse_id.transform('size') >= 4]
print('within-horse slope of offset on own weight', np.polyfit(m.wd, m.od, 1), 'corr', np.corrcoef(m.wd, m.od)[0, 1], len(m))
M.to_pickle('/tmp/atw_explore.pkl')
