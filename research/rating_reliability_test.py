"""Is the run-to-run rating noise measurement noise or real performance variation? (26 Oct 2026)
Within-race demeaned wpr (w) vs within-race demeaned finishing margin (m = -clip(marginFinish,0,30), a pure outcome measure with no weight/going/class
adjustment). Reliability = correlation of a horse's consecutive runs (lag 1) and the share of variance that persists. If wpr were noisier than the margin
(construction noise) its lag-1 correlation would be LOWER than the margin's; if the same or higher, the noise is real performance variation.
  PYTHONPATH=. python research/rating_reliability_test.py
"""
import glob, os
import numpy as np, pandas as pd
ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..'))
cols = ['race_id', 'horse_id', 'date', 'wpr', 'marginFinish', 'isBarrierTrial', 'is_jumpout', 'weightCarried']
d = pd.concat([pd.read_csv(f, usecols=lambda c: c in cols, low_memory=False) for f in sorted(glob.glob(os.path.join(ROOT, 'race_results_202[2-6].csv.gz')))], ignore_index=True)
d = d[~d.isBarrierTrial.astype(bool) & ~d.is_jumpout.fillna(False).astype(bool)].drop_duplicates(['race_id', 'horse_id'])
d['date'] = pd.to_datetime(d.date)
d['m'] = -d.marginFinish.clip(0, 30)
# winners carry a negative margin (winning margin): treat as 0 lead is wrong for ranking, so use the winner's margin as +lead capped
d.loc[d.marginFinish < 0, 'm'] = d.marginFinish.abs().clip(0, 10)
d['rk'] = d.groupby('race_id').marginFinish.rank(pct=True)
d['n'] = d.groupby('race_id').horse_id.transform('size')
d = d[(d.n >= 8) & d.wpr.notna() & d.marginFinish.notna()].copy()
for c in ('wpr', 'm', 'rk'):
    d['w_' + c] = d[c] - d.groupby('race_id')[c].transform('mean')
d = d.sort_values(['horse_id', 'date', 'race_id'])
g = d.groupby('horse_id')
print(f'{len(d):,} runs')
for c, lab in (('w_wpr', 'rating (wpr)'), ('w_m', 'margin in lengths'), ('w_rk', 'finishing rank (percentile)')):
    nxt = g[c].shift(-1)
    z = pd.DataFrame({'a': d[c], 'b': nxt}).dropna()
    r1 = z.a.corr(z.b)
    r2 = d[c].corr(g[c].shift(-2))
    print(f'{lab:30s} lag-1 corr {r1:.3f}  lag-2 corr {r2:.3f}  -> persistent share of variance about {r1:.0%}')
# does adjusting for weight/going in the rating add or remove noise? corr of wpr with margin within race
print('within-race corr(wpr, margin) = %.3f, corr(wpr, rank) = %.3f' % (d.w_wpr.corr(d.w_m), d.w_wpr.corr(-d.w_rk)))
# reliability of an average of the two measures (rating z + rank z)
zs = lambda s: (s - s.mean()) / s.std()
d['w_mix'] = zs(d.w_wpr) - zs(d.w_rk)
nxt = d.groupby('horse_id').w_mix.shift(-1)
print('blend of rating and rank: lag-1 corr %.3f' % d.w_mix.corr(nxt))
