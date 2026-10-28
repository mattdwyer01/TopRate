"""12-month backtest of 'forward on the map' using the CURRENT Proj formula (projection/models_tr/formula.json weights and low-run trim) on history
put on the page ATW scale per target race (wfa_scale AR 168, as research/conv_history.py per_row). Backtest only: the live Proj reads page ratings.
Uses the out-of-sample gap forecast and prices in the pickle written by research/fwd_map_backtest.py.   Run: PYTHONPATH=. python research/fwd_map_formula12m.py <bt.pkl> <out.pkl>"""
import sys, json
import numpy as np, pandas as pd
sys.path.insert(0, 'research')
import conv_history as C
from projection import features as F

bt, out = sys.argv[1], sys.argv[2]
d = pd.read_pickle(bt); d = d[(d.date >= '2025-10-09') & d.fgap.notna()].copy()
h = C.build(first_year=2024, last_date='2026-10-08', per_row=True)
h = h[['horse_id', 'date', 'wpr_plain', 'c_t']].sort_values(['horse_id', 'date'])
f = json.load(open('projection/models_tr/formula.json')); K = f['K']
byh = {k: (g.date.values, g.wpr_plain.values, g.c_t.values) for k, g in h.groupby('horse_id')}
proj = np.full(len(d), np.nan)
for i, (hid, dt) in enumerate(zip(d.horse_id.values, d.date.values)):
    t = byh.get(hid)
    if t is None: continue
    dd, ww, cc = t
    j = np.searchsorted(dd, dt)           # runs strictly before dt
    if j == 0: continue
    # shift for this target race: the run on this date
    k = np.searchsorted(dd, dt, side='left')
    if k < len(dd) and dd[k] == dt and not np.isnan(cc[k]): cT = cc[k]
    else: continue
    r = ww[:j][::-1][:K] + cT
    kk = len(r)
    r = F.clip_low_lags(r[None, :], f.get('clip_low'))[0]
    c = f['coef'][str(kk)]
    proj[i] = c[0] + float(np.dot(c[1:], r))
d['fproj'] = proj
cov = d.groupby('race_id').fproj.apply(lambda s: s.notna().mean())
print('races', len(cov), 'coverage>=90%', (cov >= .9).sum(), '>=80%', (cov >= .8).sum())
d.to_pickle(out)
