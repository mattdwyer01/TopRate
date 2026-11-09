"""Winner and rating test for ctx.FIT_FEATS (9 Nov 2026): prep position against the horse's usual prep length, distance and going against its best runs, usual running position.
Same structure as the live Proj (projection/train_ctx.py --v2 --conv-frac 1.0: runner-page ATW ratings plus converted results-file history for TRAINING rows, option 2 inputs, Huber 4),
the relevance model fitted with and without FIT_FEATS on runs before 2026-01-01 (early stop 2025-10..12), the plain context model shared. Scored on the 2026 page runs:
rating error (all runs, 3+ earlier runs) and winner log-likelihood in races as the page store holds them (4+ runners with a Proj, winner among them, softmax scale cross-fitted on date halves).
Run: PYTHONPATH=.:projection:research PROJECTION_RATINGS=toprate python research/proj_fit_feats_test.py [--conv-frac 1.0]"""
import argparse, os, sys, json
import numpy as np, pandas as pd, lightgbm as lgb
sys.path.insert(0, 'projection'); sys.path.insert(0, 'research')
import ctx as C

ap = argparse.ArgumentParser(); ap.add_argument('--conv-frac', type=float, default=1.0); ap.add_argument('--out', default='research/proj_fit_feats_test.json'); a = ap.parse_args()
conv = None
if a.conv_frac > 0:
    import conv_history as CH, features as FT
    real = FT.runner_page_runs().copy()
    FT._TR_CACHE['rows'] = CH.build(2020, '2025-12-31', a.conv_frac)
    conv = C.training_frame_rel(True); conv = conv[conv.f.notna()].copy()
    FT._TR_CACHE['rows'] = real
    print('converted training rows', len(conv), flush=True)
rp = C.training_frame_rel(True)
pg = rp[rp.f.notna()].copy()
classes = sorted(pg.cls.dropna().unique().tolist()); pg['cls_c'] = C._cls(pg.cls, classes)
cut, es = pd.Timestamp('2026-01-01'), pd.Timestamp('2025-10-01')
te = pg[pg.date >= cut].copy()
if conv is not None:
    conv['cls_c'] = C._cls(conv.cls, classes); pa = pd.concat([conv, pg], ignore_index=True)
else:
    pa = pg
tr, va = pa[pa.date < es], pa[(pa.date >= es) & (pa.date < cut)]
P = dict(n_estimators=4000, learning_rate=0.03, num_leaves=31, min_child_samples=100, subsample=0.8, subsample_freq=1, colsample_bytree=0.8, reg_lambda=5, verbose=-1, objective='huber', alpha=4.0)
fit = lambda F, t, v: lgb.LGBMRegressor(**P).fit(t[F], t.resid, eval_set=[(v[F], v.resid)], callbacks=[lgb.early_stopping(100, verbose=False)])
F0 = C.FEATS2; F1 = F0 + C.REL_FEATS2; F2 = F1 + C.FIT_FEATS
rel = lambda d: d[d.n >= C.REL_MIN_RUNS]
m0 = fit(F0, tr, va)
use = (te.n >= C.REL_MIN_RUNS).values
base = m0.predict(te[F0])
res = {}
for name, F in (('live', F1), ('fit', F2)):
    m = fit(F, rel(tr), rel(va))
    c = base.copy(); c[use] = m.predict(te.loc[use, F])
    te['p_' + name] = te.f + c
    imp = pd.Series(m.booster_.feature_importance('gain'), index=F)
    res[name] = dict(trees=int(m.best_iteration_), new_gain_share=round(float(imp[[x for x in F if x in C.FIT_FEATS]].sum() / imp.sum()), 4) if name == 'fit' else 0.0)
    if name == 'fit':
        print('new-input gain shares:', (imp[C.FIT_FEATS] / imp.sum()).sort_values(ascending=False).round(4).to_dict())
te['rk'] = C._race_key(te)
def wll(col, t):
    t = t[t.positionFinish.notna()].copy()
    t = t[t.groupby('rk')[col].transform('size') >= 4]
    t = t[t.groupby('rk').positionFinish.transform(lambda s: (s == 1).sum()) == 1]
    t['half'] = (t.date >= t.date.median()).astype(int)
    def ll(df, b):
        z = b * (df[col] - df.groupby('rk')[col].transform('max')); return (z - np.log(np.exp(z).groupby(df.rk).transform('sum')))[df.positionFinish == 1]
    out = []
    for h in (0, 1):
        bs = np.arange(0.05, 0.6, 0.005); b = bs[np.argmax([ll(t[t.half != h], b).mean() for b in bs])]; out.append(ll(t[t.half == h], b))
    s = pd.concat(out).sort_index()
    top = t.loc[t.groupby('rk')[col].idxmax()]
    return s, float((top.positionFinish == 1).mean()), t.rk.nunique()
r = lambda e: float(np.sqrt((e ** 2).mean()))
out = {}
for name in ('live', 'fit'):
    e = te.wpr - te['p_' + name]; s, tp, nr = wll('p_' + name, te)
    out[name] = dict(rmse=round(r(e), 4), mae=round(float(e.abs().mean()), 4), within3=round(float((e.abs() <= 3).mean()), 4), rmse_3plus=round(r(e[use]), 4),
                     win_ll=round(float(s.mean()), 5), top_pick=round(tp, 4), races=nr, **res[name])
    print(name, out[name], flush=True)
eA, eB = te.wpr - te.p_live, te.wpr - te.p_fit
dq = eA ** 2 - eB ** 2
sA, _, _ = wll('p_live', te); sB, _, _ = wll('p_fit', te)
ds = (sB - sA).dropna()
out['paired'] = dict(sq_gain=round(float(dq.mean()), 4), sq_se=round(float(dq.std() / np.sqrt(len(dq))), 4), win_ll_gain=round(float(ds.mean()), 5), win_ll_se=round(float(ds.std() / np.sqrt(len(ds))), 5),
                     runs=int(len(te)), conv_frac=a.conv_frac)
for lab, m in (('2026-01..06', te.date < '2026-07-01'), ('2026-07..', te.date >= '2026-07-01')):
    out['paired'][lab] = round(float(dq[m].mean()), 4)
print('paired', out['paired'])
json.dump(out, open(a.out, 'w'), indent=1)
