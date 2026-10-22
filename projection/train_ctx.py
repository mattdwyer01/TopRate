"""Train the context correction for the formula Proj (21 Oct 2026, projection/ctx.py). Runner-page ATW ratings only.
Fit on runs before --fit-end with early stopping on the last three months before it, report held-out rating error against the plain formula on the months after,
then refit on every run with the tree count found and write models_tr/ctx_model.txt and ctx.json (feature list, class codes, error sd by earlier-run count).
Since 22 Oct 2026 a second, relevance model (ctx.REL_FEATS: each earlier run judged against today's race, career summaries, similarity-weighted averages, the horse's own misses under the same
conditions) is trained on horses with ctx.REL_MIN_RUNS or more earlier runs and written to models_tr/ctx_rel_model.txt; horses with fewer keep the plain context model.
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
    rp = C.training_frame_rel()
    pg = rp[rp.f.notna()].copy()
    classes = sorted(pg.cls.dropna().unique().tolist())
    pg['cls_c'] = C._cls(pg.cls, classes)
    cut, es = pd.Timestamp(a.fit_end), pd.Timestamp(a.es_from)
    tr, va = pg[pg.date < es], pg[(pg.date >= es) & (pg.date < cut)]
    te = pg[pg.date >= cut].copy()
    params = dict(n_estimators=4000, learning_rate=0.03, num_leaves=31, min_child_samples=100, subsample=0.8, subsample_freq=1, colsample_bytree=0.8, reg_lambda=5, verbose=-1)
    F0, F1 = C.FEATS, C.FEATS + C.REL_FEATS

    def fit(feats, tr_, va_):
        m = lgb.LGBMRegressor(**params)
        m.fit(tr_[feats], tr_.resid, eval_set=[(va_[feats], va_.resid)], callbacks=[lgb.early_stopping(100, verbose=False)])
        return m, int(m.best_iteration_)

    m0, b0 = fit(F0, tr, va)
    rel = lambda d: d[d.n >= C.REL_MIN_RUNS]
    m1, b1 = fit(F1, rel(tr), rel(va))
    print('plain context trees', b0, 'train', len(tr), '| relevance trees', b1, 'train', len(rel(tr)), 'valid', len(rel(va)))
    te['corr0'] = m0.predict(te[F0])
    te['corr1'] = np.nan
    use = (te.n >= C.REL_MIN_RUNS).values
    te.loc[use, 'corr1'] = m1.predict(te.loc[use, F1])
    te['corr'] = np.where(use, te.corr1, te.corr0)
    te['e0'] = te.resid
    te['e_ctx'] = te.resid - te.corr0
    te['e1'] = te.resid - te['corr']
    r = lambda x: float(np.sqrt((x ** 2).mean()))
    for lab, a_ in (('held out', te), ('2026-01..06', te[te.date < '2026-07-01']), ('2026-07..', te[te.date >= '2026-07-01']), (f'{C.REL_MIN_RUNS}+ earlier runs', te[use]), (f'under {C.REL_MIN_RUNS}', te[~use])):
        print(f"{lab:16s} n={len(a_):6d} formula {r(a_.e0):.3f}  plain context {r(a_.e_ctx):.3f}  deployed {r(a_.e1):.3f}   correction mean {a_['corr'].mean():+.3f} sd {a_['corr'].std():.3f}")
    kk = te.n.clip(upper=C.K).astype(int)
    sd = {str(k): round(r(te.e1[kk == k]), 2) for k in range(1, C.K + 1)}
    sd0 = {str(k): round(r(te.e0[kk == k]), 2) for k in range(1, C.K + 1)}
    print('error sd by earlier runs (deployed):', sd, ' formula:', sd0)
    # final fits on every run
    n0, n1 = int(b0 * 1.15), int(b1 * 1.15)
    fin0 = lgb.LGBMRegressor(**{**params, 'n_estimators': n0}).fit(pg[F0], pg.resid)
    pr = rel(pg)
    fin1 = lgb.LGBMRegressor(**{**params, 'n_estimators': n1}).fit(pr[F1], pr.resid)
    fin0.booster_.save_model(os.path.join(C.M, 'ctx_model.txt'))
    fin1.booster_.save_model(os.path.join(C.M, 'ctx_rel_model.txt'))
    json.dump({'feats': C.FEATS, 'rel_feats': F1, 'rel_min_runs': C.REL_MIN_RUNS, 'classes': classes, 'sd': sd, 'sd_formula': sd0, 'n_trees': n0, 'n_trees_rel': n1,
               'trained_to': str(pg.date.max().date()), 'n_train': int(len(pg)), 'n_train_rel': int(len(pr)),
               'held_out_rmse': {'formula': round(r(te.e0), 3), 'context': round(r(te.e_ctx), 3), 'deployed': round(r(te.e1), 3), 'n': int(len(te))}},
              open(os.path.join(C.M, 'ctx.json'), 'w'), indent=1)
    print('written', os.path.join(C.M, 'ctx_model.txt'), 'and ctx_rel_model.txt')


if __name__ == '__main__':
    main()
