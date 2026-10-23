"""Race-shape projection pipeline (23 Oct 2026). Stage A forecasts each runner's trip from pre-race information only: settle (800m position share), gap behind the leader at 800m,
early speed vs the field, lane and ground lost (GPS). Stage B maps a trip to a rating effect: a second stage on the Huber-4 Proj's miss, fitted on the ACTUAL trips of 2025 runs.
Applied to 2026 with (i) the actual trip (ceiling), (ii) the forecast trip, (iii) a Monte Carlo of trips drawn around the forecast (shared race-level pace shock + runner noise).
Judged on MAE of the miss, winner log-likelihood over Proj alone and over market + Proj (partial fields), all out of sample.
Run (after race_shape_ceiling.py has been run once, caches nothing; needs /tmp/train_ctx_gps_oos.parquet): PYTHONPATH=. python analysis/trip_map/race_shape_forecast.py"""
import os, sys
import numpy as np, pandas as pd, lightgbm as lgb
from scipy.optimize import minimize
sys.path.insert(0, os.path.dirname(__file__)); sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'projection'))
import gps_feats as GF
import build_trip_map as B
rng = np.random.default_rng(7)
rr, FL, HIST, CONT = GF.build()
pg = pd.read_parquet('/tmp/train_ctx_gps_oos.parquet'); pg['date'] = pd.to_datetime(pg.date)
cols = ['extra_rel', 'lane_rel', 'early_z', 'pace', 'settle', 'gap800', 'gps']
pg = pg.merge(rr[['hn', 'date'] + cols].rename(columns={c: 'h_' + c for c in cols}), on=['hn', 'date'], how='left')
pg['miss'] = pg.wpr - pg.proj0; pg['gps_run'] = pg.h_gps.fillna(False).astype(bool)
PRE = ['proj0', 'n', 'std4', 'ldays', 'distance', 'field_size', 'barr_f', 'going_n', 'bf', 'settle_h3', 'gap800_h3', 'early_z_h3', 'early_z_h8', 'extra_rel_h3', 'extra_rel_h8', 'lane_rel_h3', 'lane_rel_h8', 'n_gps', 'burn_h', 'bar_x_early'] + [c for c in CONT if c.startswith('c_')]
PRE = [c for c in dict.fromkeys(PRE) if c in pg.columns]
TGT = {'h_settle': False, 'h_gap800': False, 'h_early_z': True, 'h_lane_rel': True, 'h_extra_rel': True}
tr_all = pg[(pg.date < '2026-01-01') & (pg.n >= 3)]
te_all = pg[(pg.date >= '2026-01-01') & (pg.n >= 3)].copy()
PR = dict(B.PARAMS, objective='regression', num_threads=4, learning_rate=0.04)
fc, resid = {}, {}
for t, needs_gps in TGT.items():
    a = tr_all[tr_all[t].notna() & (tr_all.gps_run if needs_gps else True)]
    m = lgb.train(PR, lgb.Dataset(a[PRE], a[t]), 300)
    te_all['f_' + t] = m.predict(te_all[PRE])
    resid[t] = (a[t] - m.predict(a[PRE])).values       # in-sample residuals (slightly narrow), used for the Monte Carlo spread
    ok = te_all[t].notna() & (te_all.gps_run if needs_gps else True)
    r = np.corrcoef(te_all.loc[ok, 'f_' + t], te_all.loc[ok, t])[0, 1]
    print(f'forecast {t:12s} held-out corr {r:.3f} (R2 {r * r:.3f}), n={int(ok.sum())}, residual sd {resid[t].std():.3f}', flush=True)
# stage B: trip -> rating effect, fitted on actual 2025 trips (GPS-covered)
BASE = ['proj0', 'n', 'std4', 'ldays', 'distance', 'field_size', 'barr_f', 'going_n']
def shape_feats(d, s, e, l, x):
    out = d[BASE].copy()
    out['h_settle'], out['h_gap800'], out['h_early_z'], out['h_lane_rel'], out['h_extra_rel'] = s, None, e, l, x
    return out
SH = ['h_settle', 'h_gap800', 'h_early_z', 'h_lane_rel', 'h_extra_rel', 'surp_settle', 'surp_gap', 'surp_early']
def build(d, s, g, e, l, x):
    o = d[BASE].copy(); o['h_settle'], o['h_gap800'], o['h_early_z'], o['h_lane_rel'], o['h_extra_rel'] = s, g, e, l, x
    o['surp_settle'] = s - d.settle_h3.values; o['surp_gap'] = g - d.gap800_h3.values; o['surp_early'] = e - d.early_z_h3.values
    return o
trg = tr_all[tr_all.gps_run & tr_all.h_settle.notna() & tr_all.h_early_z.notna() & tr_all.h_lane_rel.notna()]
XB = build(trg, trg.h_settle.values, trg.h_gap800.values, trg.h_early_z.values, trg.h_lane_rel.values, trg.h_extra_rel.values)
PH = dict(B.PARAMS, objective='huber', alpha=4.0, num_threads=4)
gB = lgb.train(PH, lgb.Dataset(XB, trg.miss), 300)
tg = te_all[te_all.gps_run & te_all.h_settle.notna() & te_all.h_early_z.notna() & te_all.h_lane_rel.notna()].copy()
print('stage B train', len(trg), 'test', len(tg), flush=True)
act = gB.predict(build(tg, tg.h_settle.values, tg.h_gap800.values, tg.h_early_z.values, tg.h_lane_rel.values, tg.h_extra_rel.values))
pt = gB.predict(build(tg, tg.f_h_settle.values, tg.f_h_gap800.values, tg.f_h_early_z.values, tg.f_h_lane_rel.values, tg.f_h_extra_rel.values))
# Monte Carlo: runner noise + one shared pace shock per race (early speed and settle shift together)
K = 24
mc = np.zeros(len(tg)); race_idx = pd.factorize(tg.rid)[0]; nr = race_idx.max() + 1
sd = {t: resid[t].std() for t in TGT}
for _ in range(K):
    shock = rng.normal(0, 0.5, nr)[race_idx]            # shared pace shock in early-speed sd units
    s = tg.f_h_settle.values + rng.normal(0, sd['h_settle'], len(tg)) - 0.04 * shock
    g = np.clip(tg.f_h_gap800.values + rng.normal(0, sd['h_gap800'], len(tg)) - 0.5 * shock, 0, 30)
    e = tg.f_h_early_z.values + rng.normal(0, sd['h_early_z'], len(tg)) + 0.5 * shock
    l = tg.f_h_lane_rel.values + rng.normal(0, sd['h_lane_rel'], len(tg)); x = tg.f_h_extra_rel.values + rng.normal(0, sd['h_extra_rel'], len(tg))
    mc += gB.predict(build(tg, np.clip(s, 0, 1), g, e, l, x))
mc /= K
# direct baseline: second stage on the same pre-race inputs, no structure
gD = lgb.train(PH, lgb.Dataset(tr_all[PRE], tr_all.miss), 300); direct = gD.predict(tg[PRE])
def st(e): return f'MAE {np.abs(e).mean():.3f} within3 {100 * (np.abs(e) <= 3).mean():.1f}% rmse {np.sqrt((e ** 2).mean()):.3f}'
V = {'Proj as is': np.zeros(len(tg)), 'direct (pre-race inputs, no structure)': direct, 'forecast trip -> effect': pt, 'Monte Carlo trips -> effect': mc, 'ACTUAL trip -> effect (ceiling)': act}
print('\nMISS (actual rating - Proj) on 2026 GPS-covered runs, n=%d' % len(tg))
for k, v in V.items():
    print(f'  {k:40s} all: {st(tg.miss.values - v)} | top half: {st((tg.miss.values - v)[(tg.half == True).values])}')
# winners
w = tg[tg.rid.notna() & tg.priceStarting.notna() & (tg.priceStarting > 1)].copy()
for k, v in V.items(): w['adj_' + k] = pd.Series(v, index=tg.index).reindex(w.index)
w['win'] = (w.positionFinish == 1).astype(int); w['lp'] = -np.log(w.priceStarting)
gb = w.groupby('rid'); w = w[(gb.win.transform('sum') == 1) & (gb.win.transform('size') >= 5)].copy()
def cen(c): return w[c] - w.groupby('rid')[c].transform('mean')
w['x_proj'] = cen('proj0'); w['x_lp'] = cen('lp')
for k in V: w['x_' + k] = cen('proj0') + cen('adj_' + k)
d0 = w.date.sort_values().iloc[len(w) // 2]
def nll(par, d, cs):
    e = pd.Series(sum(p * d[c].values for p, c in zip(par, cs)), index=d.index)
    mx = e.groupby(d.rid).transform('max'); ex = np.exp(e - mx); den = ex.groupby(d.rid).transform('sum')
    return -np.log(ex / den)[d.win == 1].sum(), np.log(ex / den)[d.win == 1]
def cross(cs):
    out = []
    for a, b in ((w[w.date < d0], w[w.date >= d0]), (w[w.date >= d0], w[w.date < d0])):
        r = minimize(lambda p: nll(p, a, cs)[0], np.full(len(cs), 0.1), method='Nelder-Mead'); out.append(nll(r.x, b, cs)[1])
    return pd.concat(out)
print('\nWINNERS (races with >= 5 GPS-covered Proj runners): races', w.rid.nunique(), 'runners', len(w))
b0 = cross(['x_proj']); bm = cross(['x_lp', 'x_proj']); print(f'  Proj alone {b0.mean():.4f} | market + Proj {bm.mean():.4f}')
for k in list(V)[1:]:
    l = cross(['x_' + k]); d = (l - b0).dropna(); l2 = cross(['x_lp', 'x_' + k]); d2 = (l2 - bm).dropna()
    print(f'  {k:40s} gain over Proj alone {d.mean():+.4f} (se {d.std() / np.sqrt(len(d)):.4f}) | over market + Proj {d2.mean():+.4f} (se {d2.std() / np.sqrt(len(d2)):.4f})')
