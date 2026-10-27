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


HUBER_ALPHA = 4.0   # 22 Oct 2026: robust loss so Proj tracks the most likely rating, not the mean the bad-run tail drags down (research/proj_mode.py)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--fit-end', default='2026-01-01')
    ap.add_argument('--es-from', default='2025-10-01')
    ap.add_argument('--v2', action='store_true', help='option 2 inputs: jockey/trainer rates and the field-relative block (ctx.FEATS2 / REL_FEATS2)')
    ap.add_argument('--conv-frac', type=float, default=0.0, help='also train on results-file history put on the ATW scale per target race (research/conv_history.py, AR 168); fraction of horses, 0 = page store only')
    a = ap.parse_args()
    conv = None
    if a.conv_frac > 0:
        # TRAINING history only (27 Oct 2026): converted rows are never inputs to a live projection
        sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'research'))
        import conv_history as CH
        import features as FT
        real = FT.runner_page_runs().copy()
        FT._TR_CACHE['rows'] = CH.build(2020, '2025-12-31', a.conv_frac)
        conv = C.training_frame_rel(a.v2)
        conv = conv[conv.f.notna()].copy()
        FT._TR_CACHE['rows'] = real
        print('converted training rows', len(conv), flush=True)
    rp = C.training_frame_rel(a.v2)
    pg = rp[rp.f.notna()].copy()
    classes = sorted(pg.cls.dropna().unique().tolist())
    pg['cls_c'] = C._cls(pg.cls, classes)
    cut, es = pd.Timestamp(a.fit_end), pd.Timestamp(a.es_from)
    te = pg[pg.date >= cut].copy()
    if conv is not None:
        conv['cls_c'] = C._cls(conv.cls, classes)
        pg_all = pd.concat([conv, pg], ignore_index=True)
    else:
        pg_all = pg
    tr, va = pg_all[pg_all.date < es], pg_all[(pg_all.date >= es) & (pg_all.date < cut)]
    params = dict(n_estimators=4000, learning_rate=0.03, num_leaves=31, min_child_samples=100, subsample=0.8, subsample_freq=1, colsample_bytree=0.8, reg_lambda=5, verbose=-1, objective='huber', alpha=HUBER_ALPHA)
    F0 = C.FEATS2 if a.v2 else C.FEATS
    F1 = F0 + (C.REL_FEATS2 if a.v2 else C.REL_FEATS)

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
        print(f"{lab:16s} n={len(a_):6d} formula {r(a_.e0):.3f}  plain context {r(a_.e_ctx):.3f}  deployed {r(a_.e1):.3f}   correction mean {a_['corr'].mean():+.3f} sd {a_['corr'].std():.3f}  median miss {a_.e1.median():+.2f}  within 3 {100*(a_.e1.abs() <= 3).mean():.1f}%")
    fw = te[~use]
    for cap in (1.0, 2.0, 3.0, 99.0):
        e = fw.resid - fw.corr0.clip(-cap, cap)
        print(f'under {C.REL_MIN_RUNS} earlier runs, correction capped at +-{cap}: RMSE {r(e):.3f} MAE {e.abs().mean():.3f} (n={len(fw)})')
    kk = te.n.clip(upper=C.K).astype(int)
    sd = {str(k): round(r(te.e1[kk == k]), 2) for k in range(1, C.K + 1)}
    sd0 = {str(k): round(r(te.e0[kk == k]), 2) for k in range(1, C.K + 1)}
    print('error sd by earlier runs (deployed):', sd, ' formula:', sd0)
    # final fits on every run
    n0, n1 = int(b0 * 1.15), int(b1 * 1.15)
    fin0 = lgb.LGBMRegressor(**{**params, 'n_estimators': n0}).fit(pg_all[F0], pg_all.resid)
    pr = rel(pg_all)
    fin1 = lgb.LGBMRegressor(**{**params, 'n_estimators': n1}).fit(pr[F1], pr.resid)
    fin0.booster_.save_model(os.path.join(C.M, 'ctx_model.txt'))
    fin1.booster_.save_model(os.path.join(C.M, 'ctx_rel_model.txt'))
    json.dump({'feats': F0, 'rel_feats': F1, 'v2': bool(a.v2), 'conv_frac': a.conv_frac, 'rel_min_runs': C.REL_MIN_RUNS, 'classes': classes, 'sd': sd, 'sd_formula': sd0, 'n_trees': n0, 'n_trees_rel': n1,
               'trained_to': str(pg.date.max().date()), 'n_train': int(len(pg_all)), 'n_train_rel': int(len(pr)),
               'held_out_rmse': {'formula': round(r(te.e0), 3), 'context': round(r(te.e_ctx), 3), 'deployed': round(r(te.e1), 3), 'n': int(len(te))}},
              open(os.path.join(C.M, 'ctx.json'), 'w'), indent=1)
    print('written', os.path.join(C.M, 'ctx_model.txt'), 'and ctx_rel_model.txt')


if __name__ == '__main__':
    main()
