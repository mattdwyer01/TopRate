"""10-year test of 'lower-rated but forward' by track, distance, rail position and going (results files 2016 to 8 Oct 2026, no model training needed).
Rating = the current Proj formula weights (projection/models_tr/formula.json, with its low-run trim) on the horse's earlier PLAIN ratings (scale of ATW differs per runner by
0.8 x weight allowance, ignored here). Forward = the horse's average gap behind the leader at 800m over its last 3 runs with a position (margin800m clipped 0 to 30).
Prices = starting price, clean books (1.05 to 2.0), normalised.   Run: python research/fwd_map_10yr.py <out.pkl>"""
import glob, json, os, sys
import numpy as np, pandas as pd
sys.path.insert(0, '.')
from projection import features as F

COLS = ['race_id', 'horse_id', 'date', 'track', 'distance', 'going', 'rail_position', 'field_size', 'wpr', 'margin800m', 'position800m', 'isBarrierTrial',
        'is_jumpout', 'priceStarting', 'positionFinish', 'race_class']
fs = [f for f in sorted(glob.glob('race_results_20*.csv.gz')) if 'rc' not in f]
res = pd.concat([pd.read_csv(f, usecols=lambda c: c in set(COLS), low_memory=False) for f in fs]).drop_duplicates(['race_id', 'horse_id'])
res = res[(~res.isBarrierTrial.astype(bool)) & (~res.is_jumpout.fillna(False).astype(bool))]
res = res[~res.race_class.astype(str).str.contains('Hurdle|Steeple', case=False, na=False)].copy()
res['date'] = pd.to_datetime(res.date); res['race_id'] = res.race_id.astype(str)
res = res.sort_values(['horse_id', 'date', 'race_id']).reset_index(drop=True)
print('runs', len(res), res.date.min().date(), res.date.max().date(), flush=True)
g = res.groupby('horse_id')
L = np.column_stack([g.wpr.shift(k).values for k in range(1, 9)])      # most recent first
f = json.load(open('projection/models_tr/formula.json')); K = f['K']
n = np.isfinite(L).cumprod(axis=1).sum(axis=1)                        # consecutive earlier rated runs available
Lc = F.clip_low_lags(np.where(np.isfinite(L), L, np.nan), f.get('clip_low'))
proj = np.full(len(res), np.nan)
for k in range(1, K + 1):
    m = n == k if k < K else n >= K
    if not m.any(): continue
    c = np.array(f['coef'][str(k)]); proj[m] = c[0] + Lc[m, :k] @ c[1:]
res['rat'] = proj
res['gap800'] = res.margin800m.clip(0, 30)
g = res.groupby('horse_id')
res['gh3'] = g.gap800.transform(lambda s: s.shift(1).rolling(3, min_periods=2).mean())
d = res[res.rat.notna() & res.gh3.notna() & res.priceStarting.notna() & (res.priceStarting > 1)].copy()
cnt = d.groupby('race_id').horse_id.transform('size'); fsz = d.groupby('race_id').field_size.transform('max')
d = d[(cnt >= 6) & (cnt >= 0.9 * fsz)]
d['p'] = 1 / d.priceStarting; bk = d.groupby('race_id').p.transform('sum'); d = d[(bk >= 1.05) & (bk <= 2.0)]
d['imp'] = d.p / d.groupby('race_id').p.transform('sum')
d['won'] = (d.positionFinish == 1).astype(float); d = d[d.groupby('race_id').won.transform('sum') == 1]
d['top'] = d.rat == d.groupby('race_id').rat.transform('max'); d = d[d.groupby('race_id').top.transform('sum') == 1].copy()
d['gap'] = d.groupby('race_id').rat.transform('max') - d.rat
d['topgap'] = d.race_id.map(d[d.top].set_index('race_id').gh3); d['fwd'] = d.topgap - d.gh3
d['price'] = d.priceStarting
r = d.rail_position.astype(str)
d['rail_m'] = np.where(r.str.contains('True'), 0.0, pd.to_numeric(r.str.extract(r'(\d+)\s*m')[0], errors='coerce'))
d.to_pickle(sys.argv[1]); print('races', d.race_id.nunique(), 'runners', len(d), d.date.min().date(), d.date.max().date(), flush=True)
