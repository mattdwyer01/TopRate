"""Run-by-run look at where the live Proj (formula + context correction) misses (22 Oct 2026). Held-out runs from 2026-01-01 (model fit before it, same as
projection/train_ctx.py), runner-page ATW ratings only. For every run: error = actual rating minus Proj as it would have been before the race. Questions: how much of the
error is the whole race moving together, how heavy are the tails, does a horse's last miss carry into the next, which pre-race facts the error still leans on, and (ex-post and
market, as diagnostics only) how much the run's own result and starting price explain. Run: PYTHONPATH=. python research/proj_run_residuals.py"""
import os, sys
import lightgbm as lgb, numpy as np, pandas as pd
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'projection'))
import ctx as C

rp = C.training_frame()
pg = rp[rp.f.notna()].copy()
classes = sorted(pg.cls.dropna().unique().tolist())
pg['cls_c'] = C._cls(pg.cls, classes)
cut, es = pd.Timestamp('2026-01-01'), pd.Timestamp('2025-10-01')
tr, va = pg[pg.date < es], pg[(pg.date >= es) & (pg.date < cut)]
m = lgb.LGBMRegressor(n_estimators=3000, learning_rate=0.03, num_leaves=31, min_child_samples=100, subsample=0.8, subsample_freq=1, colsample_bytree=0.8, reg_lambda=5, verbose=-1)
m.fit(tr[C.FEATS], tr.resid, eval_set=[(va[C.FEATS], va.resid)], callbacks=[lgb.early_stopping(100, verbose=False)])
pg['proj'] = pg.f + m.predict(pg[C.FEATS])
pg['e'] = pg.wpr - pg.proj
# race_id in the page frame is a per-row placeholder, so a race is identified by date, track, distance, field size and class (the store holds only some runners per race)
pg['race_id'] = pg.date.astype(str) + '|' + pg.track.astype(str) + '|' + pg.distance.astype(str) + '|' + pg.field_size.astype(str) + '|' + pg.race_class.astype(str)
te = pg[pg.date >= cut].copy()
print(f"held-out runs {len(te):,}  RMSE {np.sqrt((te.e**2).mean()):.3f}  bias {te.e.mean():+.3f}")

print("\n[A] how much of the miss is the whole race moving together")
g = te.groupby('race_id').e
te['nr'] = g.transform('size'); te['rm'] = g.transform('mean')
b = te[te.nr >= 4].copy()
b['loo'] = (b.rm * b.nr - b.e) / (b.nr - 1)          # mean miss of the OTHER runners in the race
b['w'] = b.e - b.rm
print(f"runs in races with 4+ runs in the store: {len(b):,}  RMSE raw {np.sqrt((b.e**2).mean()):.2f}  after removing the race mean {np.sqrt((b.w**2).mean()):.2f}")
print(f"corr of a run's miss with the average miss of the other runners in its race: {b.e.corr(b.loo):.3f}  (slope {np.polyfit(b.loo, b.e, 1)[0]:.2f})")
print("   -> if this is high, part of the error is the race's own standard (field strength, pace, track) and is shared; it does not hurt ranking inside the race")

print("\n[B] tails")
e = te.e
print(f"sd {e.std():.2f}  |e|>8 {100*(e.abs()>8).mean():.1f}%  >12 {100*(e.abs()>12).mean():.1f}%  >16 {100*(e.abs()>16).mean():.1f}%  excess kurtosis {e.kurt():.2f}")
big = te[te.e.abs() > 12]
print(f"share of squared error from |e|>12 runs: {100*(big.e**2).sum()/(te.e**2).sum():.0f}%  (those are {100*len(big)/len(te):.1f}% of runs)")
print("big misses by direction:", f"actual far ABOVE proj {int((big.e>0).sum())}, far BELOW {int((big.e<0).sum())}")
for lab, s in (('earlier runs 1-2', te.n <= 2), ('3-5', (te.n >= 3) & (te.n <= 5)), ('6-8', (te.n >= 6) & (te.n <= 8)), ('9+', te.n >= 9)):
    z = te[s]; print(f"   {lab:18s} n={len(z):6d} RMSE {np.sqrt((z.e**2).mean()):.2f}  big-miss rate {100*(z.e.abs()>12).mean():.1f}%")

print("\n[C] does a horse's last miss carry into its next run (held-out runs only, chronological)")
te = te.sort_values(['horse_id', 'date'])
te['prev_e'] = te.groupby('horse_id').e.shift(1)
te['prev_gap'] = (te.date - te.groupby('horse_id').date.shift(1)).dt.days
z = te[te.prev_e.notna()]
print(f"pairs {len(z):,}  corr(last miss, this miss) {z.e.corr(z.prev_e):.3f}  slope {np.polyfit(z.prev_e, z.e, 1)[0]:.3f}")
zz = z[z.prev_gap <= 42]; print(f"   back within 6 weeks: n={len(zz):,} corr {zz.e.corr(zz.prev_e):.3f}")
h = te.groupby('horse_id').e.agg(['mean', 'count']); h = h[h['count'] >= 5]
print(f"horses with 5+ held-out runs: {len(h):,}  sd of horse-average miss {h['mean'].std():.2f}  vs {te.e.std()/np.sqrt(h['count'].mean()):.2f} expected if there were no horse effect")

print("\n[D] pre-race facts the miss still leans on (mean miss = actual minus Proj, by bin)")
te['trend'] = te.r1 - te[['r2', 'r3', 'r4']].mean(axis=1)
te['off_best'] = te.r1 - te.max4
te['wtc'] = te.wt_chg
def bins(col, edges, labels=None):
    s = pd.cut(te[col], edges, labels=labels)
    t = te.groupby(s, observed=True).e.agg(['mean', 'count', 'std']); t['se'] = t['std'] / np.sqrt(t['count'])
    print(f"  {col}:"); [print(f"     {str(k):18s} n={int(r['count']):6d} mean miss {r['mean']:+.2f} (se {r['se']:.2f})") for k, r in t.iterrows()]
bins('trend', [-99, -10, -4, 4, 10, 99])
bins('off_best', [-99, -15, -8, -3, 0.01, 99])
bins('d_last', [0, 10, 18, 28, 42, 70, 120, 9999])
bins('wtc', [-99, -3, -1, 1, 3, 99])
bins('dist_chg', [-9999, -400, -1, 1, 400, 9999])
bins('l_posf', [-1, .2, .5, .8, 2])
bins('field_size', [0, 8, 10, 12, 14, 99])
bins('cn', [-1, 20, 100, 400, 1e9])

print("\n[E] diagnostics: what the run's own result and the market explain (not usable pre-race except the price)")
te['pf'] = te.positionFinish / te.field_size
te['lsp'] = np.log(pd.to_numeric(te.priceStarting, errors='coerce').where(lambda s: s > 1))
for c in ('pf', 'marginFinish', 'lsp'):
    zz = te[[c, 'e']].dropna(); print(f"  corr(miss, {c}) {zz.e.corr(zz[c]):+.3f}  n={len(zz):,}")
zz = te.dropna(subset=['lsp']).copy()
zz['lsp_w'] = zz.lsp - zz.groupby('race_id').lsp.transform('mean'); zz['e_w'] = zz.e - zz.groupby('race_id').e.transform('mean')
zz = zz[zz.groupby('race_id').e.transform('size') >= 4]
print(f"  within-race: corr(miss, log SP) {zz.e_w.corr(zz.lsp_w):+.3f} on {len(zz):,} runs -> a lower-priced runner than Proj expects tends to rate higher; slope {np.polyfit(zz.lsp_w, zz.e_w, 1)[0]:+.2f} points per ln-price")
r2 = 1 - ((zz.e_w - np.polyval(np.polyfit(zz.lsp_w, zz.e_w, 1), zz.lsp_w)) ** 2).sum() / (zz.e_w ** 2).sum()
print(f"  share of within-race miss variance the price explains: {100*r2:.1f}%")
te.to_pickle(os.environ.get('RES_OUT', 'res.pkl'))
