"""Does the live Proj (formula + context correction) hold on Hong Kong runs? (21 Oct 2026)
Same fit as projection/train_ctx.py (before 2026-01-01, early stop 2025-10..12), scored on the held-out runs from 2026-01-01, Hong Kong tracks against the rest.
Also reports the Hong Kong runs up to 2025 that the model WAS trained on (in-sample, for scale). Runner-page ATW ratings only.
Run: PYTHONPATH=. python research/hk_ctx_backtest.py"""
import os
import sys

import lightgbm as lgb
import numpy as np
import pandas as pd

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'projection'))
import ctx as C  # noqa: E402

HK = 'happy valley|sha tin'
rp = C.training_frame()
pg = rp[rp.f.notna()].copy()
classes = sorted(pg.cls.dropna().unique().tolist())
pg['cls_c'] = C._cls(pg.cls, classes)
pg['hk'] = pg.track.astype(str).str.lower().str.contains(HK)
cut, es = pd.Timestamp('2026-01-01'), pd.Timestamp('2025-10-01')
tr, va = pg[pg.date < es], pg[(pg.date >= es) & (pg.date < cut)]
params = dict(n_estimators=3000, learning_rate=0.03, num_leaves=31, min_child_samples=100, subsample=0.8, subsample_freq=1, colsample_bytree=0.8, reg_lambda=5, verbose=-1)
m = lgb.LGBMRegressor(**params)
m.fit(tr[C.FEATS], tr.resid, eval_set=[(va[C.FEATS], va.resid)], callbacks=[lgb.early_stopping(100, verbose=False)])
print('trees', int(m.best_iteration_), 'HK runs in training (before 2025-10):', int(tr.hk.sum()), 'of', len(tr))
pg['corr'] = m.predict(pg[C.FEATS])
pg['e0'] = pg.resid
pg['e1'] = pg.resid - pg['corr']


def rep(z, label):
    if len(z) < 30:
        print(f'{label:34s} n={len(z)} (too few)')
        return
    print(f"{label:34s} n={len(z):6d} formula rmse {np.sqrt((z.e0**2).mean()):.2f} bias {z.e0.mean():+.2f} | with context rmse {np.sqrt((z.e1**2).mean()):.2f} bias {z.e1.mean():+.2f} | correction mean {z['corr'].mean():+.2f} sd {z['corr'].std():.2f}")


te = pg[pg.date >= cut]
print('--- held out, 2026-01-01 on ---')
rep(te[~te.hk], 'Australia / other')
rep(te[te.hk], 'Hong Kong')
for lo, hi in [(1, 2), (3, 5), (6, 99)]:
    z = te[(te.n >= lo) & (te.n <= hi)]
    rep(z[z.hk], f'  HK, {lo}-{hi} earlier runs')
    rep(z[~z.hk], f'  other, {lo}-{hi} earlier runs')
print('--- Hong Kong, how the context inputs look ---')
h = te[te.hk]
print('class codes (top):', h.cls.value_counts().head(6).to_dict(), '| unseen by the model:', int((~h.cls.isin(classes)).sum()))
print('jockey effect: share with no earlier page runs for the jockey', round(float((h.cn == 0).mean()), 3), 'vs other', round(float((te[~te.hk].cn == 0).mean()), 3))
print('weight carried mean HK', round(float(h.weightCarried.mean()), 1), 'vs other', round(float(te[~te.hk].weightCarried.mean()), 1))
hk_all = pg[pg.hk]
print('HK all years: bias formula', round(float(hk_all.e0.mean()), 2), 'context', round(float(hk_all.e1.mean()), 2), 'n', len(hk_all))
