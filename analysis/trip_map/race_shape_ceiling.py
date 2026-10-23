"""Ceiling for any race-shape projection (23 Oct 2026). If we knew EXACTLY where each horse would settle, how fast the early pace would be and what trip it would get,
how much better would we predict its rating (against the Huber-4 Proj) and pick winners? Hindsight shape in tiers, second stage fitted on 2025 (out-of-sample Proj),
scored on 2026. A forecast of race shape can only recover part of this. Needs /tmp/train_ctx_gps_oos.parquet (analysis/trip_map/train_ctx_gps.py) and /tmp/contention_feats.parquet.
Run: PYTHONPATH=. python analysis/trip_map/race_shape_ceiling.py"""
import os, sys
import numpy as np, pandas as pd, lightgbm as lgb
from scipy.optimize import minimize
sys.path.insert(0, os.path.dirname(__file__)); sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'projection'))
import gps_feats as GF
import build_trip_map as B

rr, FL, HIST, CONT = GF.build()
pg = pd.read_parquet('/tmp/train_ctx_gps_oos.parquet'); pg['date'] = pd.to_datetime(pg.date)
new = rr[['hn', 'date', 'extra_rel', 'lane_rel', 'early_z', 'pace', 'settle', 'gap800', 'gap600', 'gap400', 'gps']].rename(columns={c: 'h_' + c for c in ['extra_rel', 'lane_rel', 'early_z', 'pace', 'settle', 'gap800', 'gap600', 'gap400', 'gps']})
pg = pg.merge(new, on=['hn', 'date'], how='left')
pg['miss'] = pg.wpr - pg.proj0
pg['gps_run'] = pg.h_gps.fillna(False).astype(bool)
pg['surp_settle'] = pg.h_settle - pg.settle_h3; pg['surp_gap'] = pg.h_gap800 - pg.gap800_h3; pg['surp_early'] = pg.h_early_z - pg.early_z_h3
pg['settle_x_pace'] = pg.h_settle * pg.h_pace
pg['leader_hot'] = (pg.h_settle <= 0.2).astype(float) * pg.h_pace
BASE = ['proj0', 'n', 'std4', 'ldays', 'distance', 'field_size', 'barr_f', 'going_n']
T1 = ['h_settle', 'h_gap800', 'surp_settle', 'surp_gap']
T2 = T1 + ['h_early_z', 'h_pace', 'surp_early', 'settle_x_pace', 'leader_hot']
T3 = T2 + ['h_lane_rel', 'h_extra_rel']
T4 = T3 + ['h_gap600', 'h_gap400']
TIERS = [('Proj + context only', BASE), ('+ settle and gap at 800m (results)', BASE + T1), ('+ GPS early speed and race pace', BASE + T2), ('+ lane and ground lost', BASE + T3), ('+ position to 400m (reference)', BASE + T4)]
tr = pg[(pg.date < '2026-01-01') & (pg.n >= 3) & pg.gps_run & pg.h_settle.notna()]
te = pg[(pg.date >= '2026-01-01') & (pg.n >= 3) & pg.gps_run & pg.h_settle.notna()].copy()
print('GPS-covered runs: train (2025)', len(tr), 'test (2026)', len(te), flush=True)
PH = dict(B.PARAMS, objective='huber', alpha=4.0, num_threads=4)
def st(e): return f'MAE {np.abs(e).mean():.3f} within3 {100 * (np.abs(e) <= 3).mean():.1f}% rmse {np.sqrt((e ** 2).mean()):.3f}'
sub = {'all GPS runs': np.ones(len(te), bool), 'top half by prior': (te.half == True).values}
preds = {}
for k, f in TIERS:
    m = lgb.train(PH, lgb.Dataset(tr[f], tr.miss), 300); preds[k] = m.predict(te[f])
    print(f'{k:38s}' + ' | '.join(f'{lab}: {st(te.miss.values[msk] - preds[k][msk])}' for lab, msk in sub.items()))
print('Proj as is'.ljust(38) + ' | '.join(f'{lab}: {st(te.miss.values[msk])}' for lab, msk in sub.items()))
# winner test, partial fields, conditional logit on Proj + shape-adjusted direction, cross-fit by date halves
w = te[te.rid.notna() & te.priceStarting.notna() & (te.priceStarting > 1)].copy()
for k, _ in TIERS: w['pd_' + k] = pd.Series(preds[k], index=te.index).reindex(w.index)
w['win'] = (w.positionFinish == 1).astype(int); w['lp'] = -np.log(w.priceStarting)
gb = w.groupby('rid'); w = w[(gb.win.transform('sum') == 1) & (gb.win.transform('size') >= 5)].copy()
def cen(c): return w[c] - w.groupby('rid')[c].transform('mean')
w['x_proj'] = cen('proj0'); w['x_lp'] = cen('lp')
for k, _ in TIERS: w['x_' + k] = cen('proj0') + cen('pd_' + k)
d0 = w.date.sort_values().iloc[len(w) // 2]
def nll(par, d, cols):
    e = pd.Series(sum(p * d[c].values for p, c in zip(par, cols)), index=d.index)
    mx = e.groupby(d.rid).transform('max'); ex = np.exp(e - mx); den = ex.groupby(d.rid).transform('sum')
    return -np.log(ex / den)[d.win == 1].sum(), np.log(ex / den)[d.win == 1]
def cross(cols):
    out = []
    for a, b in ((w[w.date < d0], w[w.date >= d0]), (w[w.date >= d0], w[w.date < d0])):
        r = minimize(lambda p: nll(p, a, cols)[0], np.full(len(cols), 0.1), method='Nelder-Mead'); out.append(nll(r.x, b, cols)[1])
    return pd.concat(out)
print('\nWINNERS (hindsight shape, GPS-covered runners, races with >= 5 such runners): races', w.rid.nunique(), 'runners', len(w))
b0 = cross(['x_proj']); bm = cross(['x_lp', 'x_proj'])
print(f'  Proj alone {b0.mean():.4f} | market + Proj {bm.mean():.4f}')
for k, _ in TIERS[1:]:
    l = cross(['x_' + k]); d = (l - b0).dropna(); l2 = cross(['x_lp', 'x_' + k]); d2 = (l2 - bm).dropna()
    print(f'  {k:38s} gain over Proj alone {d.mean():+.4f} (se {d.std() / np.sqrt(len(d)):.4f}) | over market + Proj {d2.mean():+.4f} (se {d2.std() / np.sqrt(len(d2)):.4f})')
