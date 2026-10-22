"""Is the Proj spread realistic? (22 Oct 2026) Held-out 2026 runs (models fit before 2026-01, early stop 2025-10..12, as train_ctx.py): within-race spread of the predicted rating against the spread of the actual ratings, and the
calibration slope of the actual rating on the prediction inside a race (slope 1 = the spread is right as an expectation; above 1 = predictions are too compressed). Pseudo-race = date, venue, distance, class, field size, kept when
3+ runners are in the store. Also by size of the predicted gap to the race mean.
Run: PYTHONPATH=. python research/proj_spread_check.py"""
import os, sys, warnings
warnings.filterwarnings('ignore')
import numpy as np, pandas as pd, lightgbm as lgb
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'projection'))
import ctx as C
rp = C.training_frame_rel()
classes = sorted(rp.cls.dropna().unique().tolist()); rp['cls_c'] = C._cls(rp.cls, classes)
pg = rp[rp.f.notna()].copy()
cut, es = pd.Timestamp('2026-01-01'), pd.Timestamp('2025-10-01')
F0, F1 = C.FEATS, C.FEATS + C.REL_FEATS
P = dict(learning_rate=0.03, num_leaves=31, min_child_samples=100, subsample=0.8, subsample_freq=1, colsample_bytree=0.8, reg_lambda=5, verbose=-1, n_jobs=4)
if os.environ.get('HUBER'): P.update(objective='huber', alpha=float(os.environ['HUBER']))   # live models: Huber alpha 4 since 22 Oct 2026
def fit(feats, a, b):
    return lgb.LGBMRegressor(n_estimators=4000, **P).fit(a[feats], a.resid, eval_set=[(b[feats], b.resid)], callbacks=[lgb.early_stopping(100, verbose=False)])
sp = lambda d_: (d_[d_.date < es], d_[(d_.date >= es) & (d_.date < cut)])
m0 = fit(F0, *sp(pg)); m1 = fit(F1, *sp(pg[pg.n >= C.REL_MIN_RUNS]))
te = pg[pg.date >= cut].copy()
te['pred'] = te.f + m0.predict(te[F0])
r3 = te.n >= C.REL_MIN_RUNS
te.loc[r3, 'pred'] = te.f[r3] + m1.predict(te.loc[r3, F1])
te['miss'] = te.wpr - te.pred
print(f"all held-out runs: mean miss {te.miss.mean():+.2f}, median miss {te.miss.median():+.2f}, RMSE {np.sqrt((te.miss**2).mean()):.3f}, within 3 {100*(te.miss.abs()<=3).mean():.1f}%, within 6 {100*(te.miss.abs()<=6).mean():.1f}%")
te['rk'] = te.date.astype(str) + '|' + te.venue.astype(str) + '|' + te.distance.astype(str) + '|' + te.race_class.astype(str) + '|' + te.field_size.astype(str)
g = te.groupby('rk'); te = te[g.pred.transform('size') >= 3].copy()
te['dp'] = te.pred - te.groupby('rk').pred.transform('mean'); te['da'] = te.wpr - te.groupby('rk').wpr.transform('mean')
te['df'] = te.f - te.groupby('rk').f.transform('mean')
print(f"{len(te):,} held-out runs in {te.rk.nunique():,} pseudo-races (3+ runners in the store)")
for lab, c in (('formula', 'df'), ('Proj (deployed)', 'dp')):
    sd_p = te[c].std(); sd_a = te.da.std(); slope = (te[c] * te.da).sum() / (te[c] ** 2).sum()
    print(f"{lab:16s} within-race sd predicted {sd_p:5.2f}  actual {sd_a:5.2f}  corr {np.corrcoef(te[c], te.da)[0,1]:.3f}  slope of actual on predicted {slope:.3f}")
print('\nby predicted gap to the race mean (Proj): n, mean predicted, mean actual, slope')
te['b'] = pd.cut(te.dp, [-99, -10, -6, -3, -1, 1, 3, 6, 10, 99])
for b_, x in te.groupby('b', observed=True):
    print(f"{str(b_):12s} n={len(x):6d}  pred {x.dp.mean():+6.2f}  actual {x.da.mean():+6.2f}  ratio {x.da.mean() / x.dp.mean() if abs(x.dp.mean()) > .05 else float('nan'):.2f}")
print('\nby earlier runs: slope')
for lab, s in (('1-2', te.n <= 2), ('3-5', te.n.between(3, 5)), ('6-8', te.n.between(6, 8)), ('9+', te.n >= 9)):
    x = te[s]; print(f"{lab:5s} n={len(x):6d} sd pred {x.dp.std():.2f} actual {x.da.std():.2f} slope {(x.dp * x.da).sum() / (x.dp ** 2).sum():.3f}")
# the top of each field: gap from top predicted vs actual
top = te.loc[te.groupby('rk').pred.idxmax()]
print(f"\nTop predicted runner of each pseudo-race: predicted lead over the field mean {top.dp.mean():+.2f}, actual {top.da.mean():+.2f}")
