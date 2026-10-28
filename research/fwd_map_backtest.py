"""Long backtest of the 'lower-rated but forward on the map' idea on the results files (no dashboard history needed).

Everything is out of sample: the gap forecast (nongps.py method: LightGBM on track, distance, going, rail, barrier, field size and the horse's last
3 / 8 positions and gaps at 800m, spread-placed like a real field) and the rating stand-in (Huber LightGBM on the horse's last 8 plain ratings) are
fitted on runs before 2025-01-01 and scored on 2025-01-01 to the last day the results files hold 800m positions. Prices: starting price, clean
books only (sum of 1/SP between 1.05 and 2.0), normalised to a win chance.   Run: PYTHONPATH=. python research/fwd_map_backtest.py
"""
import glob, os, sys
import numpy as np, pandas as pd, lightgbm as lgb
sys.path.insert(0, 'analysis/trip_map')
import build_trip_map as B
import nongps as N

COLS = ['race_id', 'horse_id', 'horse', 'date', 'track', 'distance', 'going', 'barrier', 'field_size', 'position800m', 'margin800m', 'rail_position',
        'wpr', 'isBarrierTrial', 'is_jumpout', 'priceStarting', 'winner', 'positionFinish', 'race_class']
fs = [f for f in sorted(glob.glob('race_results_20*.csv.gz')) if 'rc' not in f and int(os.path.basename(f)[13:17]) >= 2019]
res = pd.concat([pd.read_csv(f, usecols=lambda c: c in set(COLS), low_memory=False) for f in fs]).drop_duplicates(['race_id', 'horse_id'])
res = res[(~res.isBarrierTrial.astype(bool)) & (~res.is_jumpout.fillna(False).astype(bool))].copy()
res['date'] = pd.to_datetime(res.date); res['race_id'] = res.race_id.astype(str)
res = res[~res.race_class.astype(str).str.contains('Hurdle|Steeple', case=False, na=False)]
print('runs', len(res), res.date.min().date(), res.date.max().date(), flush=True)

# ---- gap forecast (out of sample from 2025)
R = N.result_runs(res.assign(race_id=res.race_id))
R['trk'] = pd.Categorical(R.track, categories=sorted(R.track.unique()))
R = N.add_hist(R)
tr = R[R.date < '2025-01-01']; te = R[R.date >= '2025-01-01'].copy()
m, ms, tab = N.fit(tr)
sc = N.place(te, m, ms, tab)
sc = sc[['race_id', 'horse_id', 'gap', 'raw_gap', 'gap800', 'n_hist']].rename(columns={'gap': 'fgap', 'gap800': 'agap'})
print('forecast rows', len(sc), flush=True)

# ---- rating stand-in
r = res.sort_values(['horse_id', 'date', 'race_id']).copy()
g = r.groupby('horse_id').wpr
for k in range(1, 9): r[f'l{k}'] = g.shift(k)
r['n'] = r.groupby('horse_id').cumcount()
r['dsl'] = (r.date - r.groupby('horse_id').date.shift(1)).dt.days
F = [f'l{k}' for k in range(1, 9)] + ['n', 'dsl', 'distance', 'field_size']
r['d_wpr'] = r.wpr - r.groupby('race_id').wpr.transform('mean')
a = r[r.wpr.notna() & r.l1.notna()]
trn = a[a.date < '2025-01-01']
mdl = lgb.train(dict(objective='huber', alpha=4.0, learning_rate=0.05, num_leaves=31, min_data_in_leaf=100, verbose=-1, num_threads=4),
                lgb.Dataset(trn[F], trn.wpr), 400)
r['rat'] = np.where(r.l1.notna(), mdl.predict(r[F]), np.nan)
print('rating stand-in fitted', flush=True)

d = sc.merge(r[['race_id', 'horse_id', 'date', 'track', 'distance', 'going', 'priceStarting', 'winner', 'rat', 'field_size']], on=['race_id', 'horse_id'])
d = d[d.priceStarting.notna() & (d.priceStarting > 1) & d.rat.notna()]
cnt = d.groupby('race_id').horse_id.transform('size'); fsz = d.groupby('race_id').field_size.transform('max')
d = d[(cnt >= 6) & (cnt >= 0.95 * fsz)]
d['p'] = 1 / d.priceStarting; bk = d.groupby('race_id').p.transform('sum'); d = d[(bk >= 1.05) & (bk <= 2.0)]
d['imp'] = d.p / d.groupby('race_id').p.transform('sum')
win = d.groupby('race_id').winner.transform('sum'); d = d[win == 1]
d['won'] = d.winner.astype(float)
d['top'] = d.rat == d.groupby('race_id').rat.transform('max')
d = d[d.groupby('race_id').top.transform('sum') == 1].copy()
d['gap'] = d.groupby('race_id').rat.transform('max') - d.rat
tg = d[d.top].set_index('race_id').fgap; d['topgap'] = d.race_id.map(tg); d['fwd'] = d.topgap - d.fgap
d['price'] = d.priceStarting
d['q'] = d.date.dt.to_period('Q').astype(str)
d.to_pickle('/tmp/claude-0/-home-user-TopRate/19004a06-2236-59f2-9ed8-08b3c680d418/scratchpad/bt.pkl')
print('races', d.race_id.nunique(), 'runners', len(d), d.date.min().date(), d.date.max().date(), flush=True)
