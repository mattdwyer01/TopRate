"""A/B of the momentum inputs (ctx.MOM_FEATS) in the context Proj, 6 Nov 2026. Page store only (no converted history), fit before 2026-01 with early stopping on 2025-10..12, scored on 2026.
Reports held-out error overall and for rising, lightly raced horses (the Defiantly profile), where the old model was thought too cautious.
Run: PYTHONPATH=.:projection PROJECTION_RATINGS=toprate python research/momentum_ab.py"""
import sys, os
import lightgbm as lgb, numpy as np, pandas as pd
sys.path.insert(0, 'projection')
import ctx as C

P = dict(n_estimators=4000, learning_rate=0.03, num_leaves=31, min_child_samples=100, subsample=0.8, subsample_freq=1, colsample_bytree=0.8, reg_lambda=5, verbose=-1, objective='huber', alpha=4.0)
rp = C.training_frame_rel(True)
pg = rp[rp.f.notna()].copy()
classes = sorted(pg.cls.dropna().unique().tolist())
pg['cls_c'] = C._cls(pg.cls, classes)
cut, es = pd.Timestamp('2026-01-01'), pd.Timestamp('2025-10-01')
tr, va, te = pg[pg.date < es], pg[(pg.date >= es) & (pg.date < cut)], pg[pg.date >= cut].copy()
MOM = ['rise3', 'rise_old', 'up3', 'step1']
base = list(C.FEATS2)
F = {'old': base, 'mom': base + MOM}
FR = {'old': base + C.REL_FEATS2, 'mom': base + MOM + C.REL_FEATS2}
rel = lambda d: d[d.n >= C.REL_MIN_RUNS]
r = lambda x: float(np.sqrt((x ** 2).mean()))
use = (te.n >= C.REL_MIN_RUNS).values
for k in ('old', 'mom'):
    m0 = lgb.LGBMRegressor(**P).fit(tr[F[k]], tr.resid, eval_set=[(va[F[k]], va.resid)], callbacks=[lgb.early_stopping(100, verbose=False)])
    m1 = lgb.LGBMRegressor(**P).fit(rel(tr)[FR[k]], rel(tr).resid, eval_set=[(rel(va)[FR[k]], rel(va).resid)], callbacks=[lgb.early_stopping(100, verbose=False)])
    c = m0.predict(te[F[k]]); c1 = np.full(len(te), np.nan); c1[use] = m1.predict(te.loc[use, FR[k]])
    te['e_' + k] = te.resid - np.where(use, c1, c)
    print(k, 'trees', m0.best_iteration_, m1.best_iteration_, flush=True)
te['e_f'] = te.resid
sub = {'all': te.n > 0, 'all 3+ runs': use,
       'rising 3, rise>=5': (te.up3 == 1) & (te.rise3 >= 5),
       'rising 3, rise>=5, n<=11 (light)': (te.up3 == 1) & (te.rise3 >= 5) & (te.n <= 11),
       'rising, light, mean3 90-105': (te.up3 == 1) & (te.rise3 >= 5) & (te.n <= 11) & te.mean3.between(90, 105),
       'last run >= 5 above runs 4-8': te.rise_old >= 5, 'last run >= 5 below runs 4-8': te.rise_old <= -5}
print(f"{'group':36s} {'n':>6s} | RMSE formula old mom | MAE old mom | mean miss old mom | median old mom")
for nme, m in sub.items():
    a = te[m]
    print(f"{nme:36s} {len(a):6d} | {r(a.e_f):.3f} {r(a.e_old):.3f} {r(a.e_mom):.3f} | {a.e_old.abs().mean():.3f} {a.e_mom.abs().mean():.3f} | {a.e_old.mean():+.2f} {a.e_mom.mean():+.2f} | {a.e_old.median():+.2f} {a.e_mom.median():+.2f}")
d = te.e_old ** 2 - te.e_mom ** 2
print('paired squared-error gain overall', round(d.mean(), 3), 'se', round(d.std() / np.sqrt(len(d)), 3))
