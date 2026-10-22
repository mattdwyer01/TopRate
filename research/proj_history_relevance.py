"""Horse-by-horse, run-by-run: judge each earlier run for how relevant it is to TODAY'S race, instead of one fixed weighting of the last eight ratings (22 Oct 2026).
Runner-page ATW ratings only; models fit before 2026-01-01 (early stop 2025-10..12), scored on 35k held-out 2026 runs, paired squared-error gain per run.
Added to the live context inputs, one family at a time then together:
 lag context  : for each of the last 4 runs, how today differs from that run (distance, going, same track, same jockey, same class, weight, days between) and how that run went
                (margin, finish place, its rating relative to the horse's last-8 mean)
 career       : all earlier runs, not just eight: mean, max, sd, EWM (half-life 3 runs), count of runs at 95% of career best
 similarity   : average of the last eight ratings weighted by closeness of distance, going, track, jockey, class and recency (fixed kernels), shown as the gap to the formula
 own history  : the horse's own earlier misses under the same conditions (shrunk), as before
Run: PYTHONPATH=. python research/proj_history_relevance.py"""
import os, sys
import lightgbm as lgb, numpy as np, pandas as pd
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'projection'))
import ctx as C

rp = C.training_frame()
pg = rp[rp.f.notna()].copy().sort_values(['horse_id', 'date']).reset_index(drop=True)
classes = sorted(pg.cls.dropna().unique().tolist()); pg['cls_c'] = C._cls(pg.cls, classes)
g = pg.groupby('horse_id')
Kmax = 8
R = np.column_stack([pg[f'r{k}'].values for k in range(1, Kmax + 1)])
def lag(col): return np.column_stack([g[col].shift(k).values for k in range(1, Kmax + 1)])
dist, going, wt, mgn = lag('distance'), lag('going_n'), lag('weightCarried'), lag('marginFinish')
posf = lag('positionFinish') / lag('field_size')
trk = np.column_stack([(g['track'].shift(k) == pg.track).values for k in range(1, Kmax + 1)]).astype(float)
jk = np.column_stack([(g['jockey'].shift(k) == pg.jockey).values for k in range(1, Kmax + 1)]).astype(float)
cl = np.column_stack([(g['cls'].shift(k) == pg.cls).values for k in range(1, Kmax + 1)]).astype(float)
dts = np.column_stack([(pg.date - g['date'].shift(k)).dt.days.values for k in range(1, Kmax + 1)]).astype(float)
dd, gd, wd = pg.distance.values[:, None] - dist, pg.going_n.values[:, None] - going, pg.weightCarried.values[:, None] - wt
avail = ~np.isnan(R)
rmean = np.nanmean(np.where(avail, R, np.nan), axis=1)
LAG = {}
for k in range(4):
    for nm, a in (('dd', dd), ('gd', gd), ('trk', trk), ('jk', jk), ('cl', cl), ('wd', wd), ('dg', dts), ('mg', mgn), ('pf', posf)):
        LAG[f'{nm}{k+1}'] = a[:, k]
    LAG[f'dev{k+1}'] = R[:, k] - rmean
LAGF = list(LAG)
pg = pd.concat([pg, pd.DataFrame(LAG, index=pg.index)], axis=1)
# career summaries over ALL earlier runs
gw = pg.groupby('horse_id').wpr
pg['c_mean'] = gw.transform(lambda s: s.shift(1).expanding().mean())
pg['c_max'] = gw.transform(lambda s: s.shift(1).expanding().max())
pg['c_sd'] = gw.transform(lambda s: s.shift(1).expanding().std())
pg['c_ewm3'] = gw.transform(lambda s: s.shift(1).ewm(halflife=3, min_periods=1).mean())
pg['c_near'] = gw.transform(lambda s: (s.shift(1) >= 0.95 * s.shift(1).expanding().max()).astype(float).where(s.shift(1).notna()).expanding().sum())
pg['c_vs_f'] = pg.c_ewm3 - pg.f; pg['cmax_vs_f'] = pg.c_max - pg.f
CAR = ['c_mean', 'c_max', 'c_sd', 'c_ewm3', 'c_near', 'c_vs_f', 'cmax_vs_f']
# similarity-weighted averages of the last eight ratings
rec = np.exp(-(np.arange(Kmax)[None, :]) / 4.0)
def wavg(w):
    w = np.where(avail, w * rec, 0.0); s = w.sum(axis=1)
    with np.errstate(all='ignore'): return np.where(s > 0, (w * np.nan_to_num(R)).sum(axis=1) / s, np.nan)
SIM = {'sim_dist': wavg(np.exp(-np.abs(np.nan_to_num(dd, nan=1e4)) / 300.0)), 'sim_going': wavg(np.exp(-np.abs(np.nan_to_num(gd, nan=1e4)) / 1.5)),
       'sim_track': wavg(1.0 + 3.0 * np.nan_to_num(trk)), 'sim_jock': wavg(1.0 + 3.0 * np.nan_to_num(jk)), 'sim_class': wavg(1.0 + 3.0 * np.nan_to_num(cl)),
       'sim_days': wavg(np.exp(-np.nan_to_num(dts, nan=1e4) / 120.0))}
SIM['sim_all'] = wavg(np.exp(-np.abs(np.nan_to_num(dd, nan=1e4)) / 400.0) * np.exp(-np.abs(np.nan_to_num(gd, nan=1e4)) / 2.0) * (1 + 1.5 * np.nan_to_num(trk)) * (1 + 1.0 * np.nan_to_num(jk)) * (1 + 1.0 * np.nan_to_num(cl)))
for k, v in list(SIM.items()): pg[k] = v - pg.f.values; 
SIMF = list(SIM)
# own earlier misses under the same conditions (as before)
pg['gg'] = pd.cut(pg.going_n, [-1, 3, 4, 7, 99], labels=False); pg['db'] = (pg.distance / 200).round(); pg['fu'] = (pg.d_last > 60).astype(int)
for key, nm in ((['db'], 'h_dist'), (['gg'], 'h_going'), (['track'], 'h_track'), (['fu'], 'h_spell'), (['jockey'], 'h_jock')):
    gg_ = pg.groupby(['horse_id'] + key).resid
    pg[nm] = (gg_.cumsum() - pg.resid) / (gg_.cumcount() + 5.0); pg[nm + '_n'] = gg_.cumcount()
OWN = ['h_dist', 'h_dist_n', 'h_going', 'h_going_n', 'h_track', 'h_track_n', 'h_spell', 'h_spell_n', 'h_jock', 'h_jock_n']

cut, es = pd.Timestamp('2026-01-01'), pd.Timestamp('2025-10-01')
tr, va, te = pg[pg.date < es], pg[(pg.date >= es) & (pg.date < cut)], pg[pg.date >= cut].copy()
P = dict(learning_rate=0.03, num_leaves=31, min_child_samples=100, subsample=0.8, subsample_freq=1, colsample_bytree=0.8, reg_lambda=5, verbose=-1)
te['race'] = te.date.astype(str) + '|' + te.track.astype(str) + '|' + te.distance.astype(str) + '|' + te.field_size.astype(str) + '|' + te.race_class.astype(str)
big = te.groupby('race').resid.transform('size') >= 4
def run(feats):
    m = lgb.LGBMRegressor(n_estimators=4000, **P).fit(tr[feats], tr.resid, eval_set=[(va[feats], va.resid)], callbacks=[lgb.early_stopping(100, verbose=False)])
    return te.resid - m.predict(te[feats]), m
def within(e): te['_e'] = e; return np.sqrt(((e - te.groupby('race')._e.transform('mean'))[big] ** 2).mean())
b, _ = run(C.FEATS)
print(f"held-out runs {len(te):,}\n{'inputs added':30s} {'RMSE':>7s} {'within-race':>12s} {'gain pts^2/run':>15s} {'se':>6s}  {'%RMSE':>6s}")
print(f"{'live context':30s} {np.sqrt((b**2).mean()):7.4f} {within(b):12.4f}")
res = {}
for lab, f in (('+ lag context (4 runs)', LAGF), ('+ career (all runs)', CAR), ('+ similarity-weighted', SIMF), ('+ own misses by condition', OWN), ('+ all of the above', LAGF + CAR + SIMF + OWN)):
    e, m = run(C.FEATS + f); d = b ** 2 - e ** 2; res[lab] = (e, m, f)
    print(f"{lab:30s} {np.sqrt((e**2).mean()):7.4f} {within(e):12.4f} {d.mean():+15.3f} {d.std()/np.sqrt(len(d)):6.3f}  {100*(1-np.sqrt((e**2).mean())/np.sqrt((b**2).mean())):5.2f}%")
e, m, f = res['+ all of the above']
imp = pd.Series(m.booster_.feature_importance('gain'), index=C.FEATS + f).sort_values(ascending=False); imp /= imp.sum()
print('top inputs in the full model (gain share):', {k: round(float(v), 3) for k, v in imp.head(12).items()})
te['e_all'] = e; te['e_base'] = b
for lab, s in (('1-2 runs', te.n <= 2), ('3-5', (te.n >= 3) & (te.n <= 5)), ('6-8', (te.n >= 6) & (te.n <= 8)), ('9-15', (te.n >= 9) & (te.n <= 15)), ('16+', te.n >= 16)):
    print(f"   earlier runs {lab:9s} n={int(s.sum()):6d} live {np.sqrt((b[s]**2).mean()):.3f} all {np.sqrt((e[s]**2).mean()):.3f}")
te.to_pickle(os.environ.get('HR_OUT', 'hr.pkl'))
