"""Proj trained on converted plain-rating history (26 Oct 2026). Plain results-file ratings 2020-2025 are shifted onto the runner-page ATW scale
(research/conv_history.py, wfa_scale offset of each horse's final run), the same formula + context + relevance Huber models as projection/train_ctx.py
are trained on that frame (prize blank), and both that model and the live (page-store trained) models are scored on the SAME held-out 2026 page-store runs.
Run: PYTHONPATH=.:research python research/proj_converted_history.py [--frac 0.3]"""
import argparse, json, os, sys
import numpy as np, pandas as pd, lightgbm as lgb
sys.path.insert(0, 'projection'); sys.path.insert(0, 'research')
import ctx as C
import features as F
import conv_history as CH

ap = argparse.ArgumentParser(); ap.add_argument('--frac', type=float, default=0.3); ap.add_argument('--first', type=int, default=2020)
a = ap.parse_args()
PRIZE = ['lprize', 'prize_chg']
r = lambda x: float(np.sqrt((np.asarray(x) ** 2).mean()))

real = F.runner_page_runs().copy()
F._TR_CACHE['rows'] = CH.build(a.first, '2025-12-31', a.frac)
conv = C.training_frame_rel(); conv = conv[conv.f.notna()].copy()
print('converted training rows', len(conv), flush=True)
classes = json.load(open(os.path.join(C.M, 'ctx.json')))['classes']
conv['cls_c'] = C._cls(conv.cls, classes)
for k in ('rp',):
    F._TR_CACHE.pop(k, None)
F._TR_CACHE['rows'] = real
allr = C.training_frame_rel(); allr = allr[allr.f.notna()].copy(); allr['cls_c'] = C._cls(allr.cls, classes)
te = allr[allr.date >= '2026-01-01'].copy()
page_tr = allr[allr.date < '2026-01-01']
print('held-out page runs', len(te), flush=True)

es = pd.Timestamp('2025-10-01')
tr, va = conv[conv.date < es], conv[(conv.date >= es) & (conv.date < '2026-01-01')]
params = dict(n_estimators=4000, learning_rate=0.03, num_leaves=31, min_child_samples=100, subsample=0.8, subsample_freq=1, colsample_bytree=0.8, reg_lambda=5, verbose=-1, objective='huber', alpha=4.0)
F0, F1 = C.FEATS, C.FEATS + C.REL_FEATS
def fit(feats, t, v):
    m = lgb.LGBMRegressor(**params); m.fit(t[feats], t.resid, eval_set=[(v[feats], v.resid)], callbacks=[lgb.early_stopping(100, verbose=False)]); return m
m0 = fit(F0, tr, va); rel = lambda d: d[d.n >= C.REL_MIN_RUNS]; m1 = fit(F1, rel(tr), rel(va))
print('converted trees', m0.best_iteration_, m1.best_iteration_, flush=True)

pt, pv = page_tr[page_tr.date < es], page_tr[page_tr.date >= es]
p0 = fit(F0, pt, pv); p1 = fit(F1, rel(pt), rel(pv)); print('page-trained trees', p0.best_iteration_, p1.best_iteration_, flush=True)
# converted + page together
both = pd.concat([conv, page_tr]); bt, bv = both[both.date < es], both[both.date >= es]
b0 = fit(F0, bt, bv); b1 = fit(F1, rel(bt), rel(bv))
live0 = lgb.Booster(model_file=os.path.join(C.M, 'ctx_model.txt')); live1 = lgb.Booster(model_file=os.path.join(C.M, 'ctx_rel_model.txt'))
use = (te.n >= C.REL_MIN_RUNS).values
def deployed(p0, p1):
    c = p0.copy(); c[use] = p1[use]; return c
Xb = te.copy(); Xb[PRIZE] = np.nan
cl = deployed(live0.predict(te[F0]), live1.predict(te[F1]))
cl_np = deployed(live0.predict(Xb[F0]), live1.predict(Xb[F1]))
cc = deployed(m0.predict(Xb[F0]), m1.predict(Xb[F1]))
cp = deployed(p0.predict(Xb[F0]), p1.predict(Xb[F1])); cb = deployed(b0.predict(Xb[F0]), b1.predict(Xb[F1]))
res = {'page-trained (fit<2026)': te.resid - cp, 'converted+page (fit<2026)': te.resid - cb, 'formula': te.resid, 'live (prize)': te.resid - cl, 'live prize blanked': te.resid - cl_np, 'converted-trained': te.resid - cc, 'average live+converted': te.resid - (cl + cc) / 2}
wr = te.groupby(['date', 'vn', 'distance', 'field_size', 'cls'], dropna=False).ngroup()
for k, e in res.items():
    e = pd.Series(np.asarray(e), index=te.index)
    wi = e - e.groupby(wr).transform('mean')
    sub = e[use]
    print(f'{k:24s} RMSE {r(e):.3f}  MAE {e.abs().mean():.3f}  within-race {r(wi):.3f}  3+runs RMSE {r(sub):.3f}  under3 RMSE {r(e[~use]):.3f}  bias {e.mean():+.2f}  within3 {100*(e.abs()<=3).mean():.1f}%')
te['p_live'], te['p_page'], te['p_conv'], te['p_both'] = te.f + cl, te.f + cp, te.f + cc, te.f + cb
te['p_formula'] = te.f
out = '/tmp/proj_conv_row_%s.pkl' % a.frac
te[['date', 'horse_id', 'vn', 'distance', 'field_size', 'cls', 'n', 'wpr', 'f', 'marginFinish', 'positionFinish', 'p_live', 'p_page', 'p_conv', 'p_both', 'p_formula']].to_pickle(out)
print('saved', out)
