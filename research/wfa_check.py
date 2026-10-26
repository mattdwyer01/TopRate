"""Check wfa_scale.py against the offsets measured on runner pages fetched for known races (atw_offset_exact.py output /tmp/atw_exact.pkl). Run with PYTHONPATH=."""
import numpy as np, pandas as pd
import wfa_scale as W
M = pd.read_pickle('/tmp/atw_exact.pkl')
M['wc'] = pd.to_numeric(M.weight_carried, errors='coerce')
M = M.dropna(subset=['wc', 'distance', 'foaled'])
M['age'] = [W.racing_age(f, d) for f, d in zip(M.foaled, M.date)]
M['sex'] = M.horse_sex.astype(str).str.upper().str[:1]
M['pred'] = [W.atw_offset(a, s, d, dist, w) for a, s, d, dist, w in zip(M.age, M.sex, M.date, M.distance, M.wc)]
M = M.dropna(subset=['pred'])
M['err'] = M.off - M.pred
M['a'] = M.age.clip(upper=5).astype(int)
M['blk'] = M.distance.map(W.block_index)
print(len(M), 'runners; error (measured - predicted offset, rating points)')
print('all: median %.2f, within 0.15: %.1f%%, within 0.5: %.1f%%, rmse %.2f' % (M.err.median(), 100 * (M.err.abs() < .15).mean(), 100 * (M.err.abs() < .5).mean(), np.sqrt((M.err ** 2).mean())))
t = M.groupby(['a', 'blk']).err.agg(['count', 'median', lambda x: (x.abs() < .15).mean()]).round(2)
t.columns = ['n', 'median_err', 'share_within_0.15']
print(t.to_string())
