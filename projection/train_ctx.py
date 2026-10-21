"""Train the context correction for the formula Proj (21 Oct 2026, projection/ctx.py). Runner-page ATW ratings only.
Fit on runs before --fit-end with early stopping on the last three months before it, report held-out rating error against the plain formula on the months after,
then refit on every run with the tree count found and write models_tr/ctx_model.txt and ctx.json (feature list, class codes, error sd by earlier-run count).
Run: PYTHONPATH=. python projection/train_ctx.py"""
import argparse
import json
import os
import sys

import lightgbm as lgb
import numpy as np
import pandas as pd

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ctx as C  # noqa: E402


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--fit-end', default='2026-01-01')
    ap.add_argument('--es-from', default='2025-10-01')
    a = ap.parse_args()
    rp = C.training_frame()
    pg = rp[rp.f.notna()].copy()
    classes = sorted(pg.cls.dropna().unique().tolist())
    pg['cls_c'] = C._cls(pg.cls, classes)
    cut, es = pd.Timestamp(a.fit_end), pd.Timestamp(a.es_from)
    tr, va = pg[pg.date < es], pg[(pg.date >= es) & (pg.date < cut)]
    params = dict(n_estimators=3000, learning_rate=0.03, num_leaves=31, min_child_samples=100, subsample=0.8, subsample_freq=1, colsample_bytree=0.8, reg_lambda=5, verbose=-1)
    m = lgb.LGBMRegressor(**params)
    m.fit(tr[C.FEATS], tr.resid, eval_set=[(va[C.FEATS], va.resid)], callbacks=[lgb.early_stopping(100, verbose=False)])
    best = int(m.best_iteration_)
    print('trees', best, 'train', len(tr), 'valid', len(va))
    te = pg[pg.date >= cut].copy()
    te['corr'] = m.predict(te[C.FEATS])
    te['e0'] = te.resid
    te['e1'] = te.resid - te['corr']
    for lab, a_ in (('held out', te), ('2026-01..06', te[te.date < '2026-07-01']), ('2026-07..', te[te.date >= '2026-07-01'])):
        print(f"{lab:12s} n={len(a_):6d} formula {np.sqrt((a_.e0 ** 2).mean()):.3f}  with context {np.sqrt((a_.e1 ** 2).mean()):.3f}   correction mean {a_['corr'].mean():+.3f} sd {a_['corr'].std():.3f}")
    kk = te.n.clip(upper=C.K).astype(int)
    sd = {str(k): round(float(np.sqrt((te.e1[kk == k] ** 2).mean())), 2) for k in range(1, C.K + 1)}
    sd0 = {str(k): round(float(np.sqrt((te.e0[kk == k] ** 2).mean())), 2) for k in range(1, C.K + 1)}
    print('error sd by earlier runs (context):', sd, ' formula:', sd0)
    # final fit on every run
    pg['cls_c'] = C._cls(pg.cls, classes)
    fin = lgb.LGBMRegressor(**{**params, 'n_estimators': int(best * 1.15)})
    fin.fit(pg[C.FEATS], pg.resid)
    fin.booster_.save_model(os.path.join(C.M, 'ctx_model.txt'))
    json.dump({'feats': C.FEATS, 'classes': classes, 'sd': sd, 'sd_formula': sd0, 'n_trees': int(best * 1.15), 'trained_to': str(pg.date.max().date()), 'n_train': int(len(pg)),
               'held_out_rmse': {'formula': round(float(np.sqrt((te.e0 ** 2).mean())), 3), 'context': round(float(np.sqrt((te.e1 ** 2).mean())), 3), 'n': int(len(te))}},
              open(os.path.join(C.M, 'ctx.json'), 'w'), indent=1)
    print('written', os.path.join(C.M, 'ctx_model.txt'))


if __name__ == '__main__':
    main()
