"""6 Nov 2026 (owner: if the model is good I should not need manual adjustments; horses whose Base/last run sits far above the Proj run above it). The context model has no direct input for the last run's
rating (r1) or its gap to the formula figure (only the deviation of each of the last four runs from the mean of the last eight). Adds r1, r1_vs_f (= r1 - f) and r1_vs_mean3 as inputs and checks, on
held-out 2026 runs (page store, fit before 2026-01, early stop 2025-10..12), whether the median and mean miss against the Proj still rise with how far the last run sits above the Proj, and whether error improves.
Run: PYTHONPATH=.:projection PROJECTION_RATINGS=toprate python research/last_run_gap_ab.py"""
import sys, warnings
warnings.filterwarnings('ignore')
import lightgbm as lgb, numpy as np, pandas as pd
sys.path.insert(0, 'projection')
import ctx as C

P = dict(n_estimators=4000, learning_rate=0.03, num_leaves=31, min_child_samples=100, subsample=0.8, subsample_freq=1, colsample_bytree=0.8, reg_lambda=5, verbose=-1, objective='huber', alpha=4.0)
rp = C.training_frame_rel(True)
rp['r1_vs_f'] = rp.r1 - rp.f; rp['r1_vs_mean3'] = rp.r1 - rp.mean3
pg = rp[rp.f.notna()].copy()
classes = sorted(pg.cls.dropna().unique().tolist()); pg['cls_c'] = C._cls(pg.cls, classes)
cut, es = pd.Timestamp('2026-01-01'), pd.Timestamp('2025-10-01')
tr, va, te = pg[pg.date < es], pg[(pg.date >= es) & (pg.date < cut)], pg[pg.date >= cut].copy()
EXTRA = ['r1', 'r1_vs_f', 'r1_vs_mean3']
rel = lambda d: d[d.n >= C.REL_MIN_RUNS]
use = (te.n >= C.REL_MIN_RUNS).values
for k, extra in (('A', []), ('B', EXTRA)):
    F0 = list(C.FEATS2) + extra; F1 = F0 + list(C.REL_FEATS2)
    m0 = lgb.LGBMRegressor(**P).fit(tr[F0], tr.resid, eval_set=[(va[F0], va.resid)], callbacks=[lgb.early_stopping(100, verbose=False)])
    m1 = lgb.LGBMRegressor(**P).fit(rel(tr)[F1], rel(tr).resid, eval_set=[(rel(va)[F1], rel(va).resid)], callbacks=[lgb.early_stopping(100, verbose=False)])
    c = m0.predict(te[F0]); c1 = np.full(len(te), np.nan); c1[use] = m1.predict(te.loc[use, F1])
    cc = np.where(use, c1, c); te['proj' + k] = te.f + cc; te['e' + k] = te.resid - cc
    print(k, 'trees', m0.best_iteration_, m1.best_iteration_, flush=True)
r = lambda x: float(np.sqrt((x ** 2).mean()))
t = te[(te.n >= 3) & te.r1.notna()].copy()
print(f"\nheld-out 2026, 3+ earlier runs n={len(t)}: RMSE A {r(t.eA):.3f} B {r(t.eB):.3f} | MAE A {t.eA.abs().mean():.3f} B {t.eB.abs().mean():.3f} | median miss A {t.eA.median():+.2f} B {t.eB.median():+.2f}")
d = t.eA ** 2 - t.eB ** 2; print('paired squared-error gain B over A', round(d.mean(), 3), 'se', round(d.std() / np.sqrt(len(d)), 3))
t['gA'] = t.r1 - t.projA; t['gB'] = t.r1 - t.projB
print('\nmiss against the Proj by how far the LAST RUN sits above the Proj (gap = last run - Proj):')
print(f"{'gap bucket':>14s} {'n':>6s} | A mean median | B mean median")
for lo, hi in ((-99, -5), (-5, 0), (0, 5), (5, 8), (8, 12), (12, 99)):
    a = t[t.gA.between(lo, hi, inclusive='left')]; b = t[t.gB.between(lo, hi, inclusive='left')]
    print(f'[{lo:>4d},{hi:>3d}) {len(a):6d} | {a.eA.mean():+5.2f} {a.eA.median():+5.2f} | {b.eB.mean():+5.2f} {b.eB.median():+5.2f}   (B bucket n={len(b)})')
