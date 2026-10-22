"""Step 1 of the contention test: do field-specific contention features (rivals inside with similar or better early
position, drawn inside this horse) improve the forecast of WHERE a horse settles (800m position share, gap) over the
horse-history + barrier model? Results-based history (position800m, margin800m), all tracks, train 2019-2024, score 2025+."""
import os, sys
import numpy as np, pandas as pd, lightgbm as lgb
sys.path.insert(0, os.path.dirname(__file__))
import build_trip_map as B
res = B.add_result_features(B.load_results())
res = res[(res.fs >= 5) & (res.date >= '2018-01-01')].copy()
res = res[res.settle.notna() & res.barrier.notna()]
res['trk'] = res.track.astype('category')
m = res.sort_values(['horse_id', 'date', 'race_id']).reset_index(drop=True)
g = m.groupby('horse_id')
for t in ('settle', 'gap800'):
    m[t + '_h3'] = g[t].transform(lambda s: s.shift(1).rolling(3, min_periods=1).mean())
    m[t + '_h8'] = g[t].transform(lambda s: s.shift(1).rolling(8, min_periods=2).mean())
m['s_lead'] = g['settle'].transform(lambda s: (s.shift(1) <= 0.15).rolling(8, min_periods=2).mean())   # share of last 8 runs led / near lead
m['n_lead'] = m.groupby('race_id').settle_h3.transform(lambda s: (s <= 0.25).sum())
m['own_rel'] = m.settle_h3 - m.groupby('race_id').settle_h3.transform('mean')
m = m.sort_values(['race_id']).reset_index(drop=True)

# ---- contention features, one pass per race
cols = ['c_in_fwd', 'c_in_fwd_w', 'c_out_fwd', 'c_in_close', 'c_in_lead', 'c_gap_close', 'c_fwd_rank', 'c_fwd_share', 'c_cost']
out = np.full((len(m), len(cols)), np.nan)
s_all = m.settle_h3.fillna(m.settle_h8).values; b_all = m.barrier.values.astype(float); fs_all = m.fs.values
starts = np.flatnonzero(np.r_[True, m.race_id.values[1:] != m.race_id.values[:-1]]); ends = np.r_[starts[1:], len(m)]
for a0, a1 in zip(starts, ends):
    s = s_all[a0:a1]; b = b_all[a0:a1]; n = a1 - a0
    ok = ~np.isnan(s)
    if ok.sum() < 5: continue
    for i in range(n):
        if not ok[i]: continue
        si, bi = s[i], b[i]
        inside = ok & (b < bi); outside = ok & (b > bi)
        fwd = s <= si + 0.05
        close = np.abs(s - si) < 0.10
        w = np.clip(1 - (s - si) / 0.4, 0, 1) * (s <= si + 0.05)           # weight: the more forward the rival, the more it matters
        out[a0 + i, 0] = (inside & fwd).sum()
        out[a0 + i, 1] = (w * inside).sum()
        out[a0 + i, 2] = (outside & fwd).sum()
        out[a0 + i, 3] = (inside & close).sum()
        out[a0 + i, 4] = (inside & (s < 0.2)).sum()
        cb = np.flatnonzero(inside & close)
        out[a0 + i, 5] = (bi - b[cb].max()) if len(cb) else np.nan         # barriers between me and the nearest similar rival inside
        out[a0 + i, 6] = (ok & (s < si)).sum() / ok.sum()
        out[a0 + i, 7] = (ok & (s < 0.25)).sum() / ok.sum()
        # crude cost to hold a position: width of the draw I must cross times how many inside rivals want it
        out[a0 + i, 8] = (bi - 1) * (inside & fwd).sum() / max(n - 1, 1)
m[cols] = out
base = ['trk', 'distance', 'barrier', 'barfrac', 'fs', 'rail_m', 'going_s', 'settle_h3', 'settle_h8', 'gap800_h3', 'gap800_h8', 's_lead', 'n_lead', 'own_rel']
cand = base + cols
tr = m[(m.date < '2025-01-01') & (m.date >= '2019-01-01')]
te = m[(m.date >= '2025-01-01') & (m.fs >= 8)]
te = te[te.race_id.map(te.groupby('race_id').size()) >= 6]
print('train', len(tr), 'test', len(te), 'races', te.race_id.nunique(), flush=True)
def evalt(y):
    t1 = tr[tr[y].notna()]; t2 = te[te[y].notna()]
    ps = {}
    for lab, f in (('base', base), ('+contention', cand)):
        ps[lab] = np.mean([lgb.train(dict(B.PARAMS, seed=k, bagging_seed=k, feature_fraction_seed=k), lgb.Dataset(t1[f], t1[y]), B.ROUNDS).predict(t2[f]) for k in range(3)], 0)
    d = t2[['race_id', 'barfrac', 'state' if 'state' in t2 else 'track', y, 'c_in_close', 'c_in_fwd']].copy()
    for k, v in ps.items(): d[k] = v
    for c in ('base', '+contention', y):
        d[c + '_c'] = d[c] - d.groupby('race_id')[c].transform('mean')
    print(f'--- target {y}')
    for lab in ('base', '+contention'):
        e = d[lab + '_c'] - d[y + '_c']
        print(lab, 'rmse', round(float(np.sqrt((e ** 2).mean())), 4), 'corr', round(float(np.corrcoef(d[lab + '_c'], d[y + '_c'])[0, 1]), 4))
    dse = (d['base_c'] - d[y + '_c']) ** 2 - (d['+contention_c'] - d[y + '_c']) ** 2
    rs = dse.groupby(d.race_id).mean()
    print('sq-err gain', round(rs.mean(), 5), 'se', round(rs.std() / np.sqrt(len(rs)), 5), 'relative', round(rs.mean() / ((d['base_c'] - d[y + '_c']) ** 2).mean(), 4))
    for lab, msk in (('wide draw (top third) with 1+ similar rival inside', (d.barfrac > 0.66) & (d.c_in_close >= 1)), ('wide draw, no similar rival inside', (d.barfrac > 0.66) & (d.c_in_close == 0)), ('3+ forward rivals inside', d.c_in_fwd >= 3), ('inside third', d.barfrac < 0.33)):
        s = dse[msk.values]; print('  ', lab, 'n', int(msk.sum()), 'sq-err gain', round(float(s.mean()), 5), 'relative', round(float(s.mean() / ((d['base_c'][msk.values] - d[y + '_c'][msk.values]) ** 2).mean()), 4))
for y in ('settle', 'gap800'): evalt(y)
m[['race_id', 'horse_id', 'date'] + cols].to_parquet(os.environ.get('CONT_OUT', '/tmp/contention_feats.parquet'))
