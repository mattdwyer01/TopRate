"""Trains the main model (horses with 3 or more prior rated runs): a linear anchor on the recent-form columns plus a gradient-boosted
correction, 5 seeds. Features are the 139 original ones plus the ladder-review block (features.LADDER_FEATURES).

Validation: train through 2024, early-stop on 2025-01..06, report RMSE on 2025-07 onward; the shipped models are then refit on all rated runs
with the stopping round scaled by 1.1. Writes projection/models/main_seed{1..5}.txt.gz and main_info.json.

usage: python projection/train_main.py [--no-ladder]    (--no-ladder reproduces the previous 139-feature model for comparison; writes nothing)
"""
import gzip
import json
import os
import sys

import lightgbm as lgb
import numpy as np
import pandas as pd

sys.path.insert(0, os.path.dirname(__file__))
import features as F  # noqa: E402

MODELS = F.MODELS
OLD = json.load(open(os.path.join(MODELS, 'main_info.json')))
BASE = OLD['base_cols']
ORIGINAL = OLD['features'][:139] if not any(f.startswith('lad_') for f in OLD['features']) else [f for f in OLD['features'] if not f.startswith('lad_')]
PARAMS = dict(OLD['params'])


def assemble():
    levels = json.load(open(os.path.join(MODELS, 'levels.json')))
    H = F.load_history()
    r = F.build_main(H, levels)
    ph = F.build_pos_hist(r)
    tf, svd = F.load_text(os.path.join(MODELS, 'text_svd.joblib'))
    parts = [r, F.build_field(r), F.build_trials(r), F.build_trials3(r), F.text_features(r, pd.Series(True, index=r.index), tf, svd), F.build_ladder(r, ph=ph)]
    L = pd.concat(parts, axis=1)
    L = L.loc[:, ~L.columns.duplicated()]
    L['sex'] = pd.Categorical(L.horse_sex, categories=levels['sex'])
    return L


def fit(tr, feats, rounds, seed, valid=None):
    A = np.c_[np.ones(len(tr)), tr[BASE].values]
    coef = np.linalg.lstsq(A, tr.wpr.values, rcond=None)[0]
    P = dict(PARAMS, seed=seed, bagging_seed=seed, feature_fraction_seed=seed)
    dtr = lgb.Dataset(tr[feats], tr.wpr.values - A @ coef)
    if valid is not None:
        Av = np.c_[np.ones(len(valid)), valid[BASE].values]
        dv = lgb.Dataset(valid[feats], valid.wpr.values - Av @ coef)
        m = lgb.train(P, dtr, 6000, valid_sets=[dv], callbacks=[lgb.early_stopping(100, verbose=False)])
    else:
        m = lgb.train(P, dtr, rounds)
    return m, coef


def main():
    ladder = '--no-ladder' not in sys.argv
    feats = ORIGINAL + (F.LADDER_FEATURES if ladder else [])
    L = assemble()
    L = L[(L.nruns >= 3) & L[BASE].notna().all(axis=1) & L.wpr.notna() & (L.date >= '2018-01-01')].copy()
    tr, va, te = L[L.date < '2025-01-01'], L[(L.date >= '2025-01-01') & (L.date < '2025-07-01')], L[L.date >= '2025-07-01']
    print('rows', len(L), 'features', len(feats), 'train/valid/test', len(tr), len(va), len(te), flush=True)
    m, coef = fit(tr, feats, None, 1, valid=va)
    rounds = int(m.best_iteration * 1.1)
    pred = np.c_[np.ones(len(te)), te[BASE].values] @ coef + m.predict(te[feats], num_iteration=m.best_iteration)
    err = te.wpr.values - pred
    print(f'holdout 2025-07+ (trained through 2024): RMSE {np.sqrt((err ** 2).mean()):.4f} MAE {np.abs(err).mean():.4f} bias {err.mean():+.3f} best_iter {m.best_iteration}', flush=True)
    for lo, hi in [(0, 60), (60, 70), (70, 200)]:
        s = (pred >= lo) & (pred < hi)
        print(f'  projected {lo}-{hi}: n {s.sum()} rmse {np.sqrt((err[s] ** 2).mean()):.3f} bias {err[s].mean():+.3f}')
    if not ladder:
        return
    A = np.c_[np.ones(len(L)), L[BASE].values]
    coef = np.linalg.lstsq(A, L.wpr.values, rcond=None)[0]
    for s in (1, 2, 3, 4, 5):
        mm, _ = fit(L, feats, rounds, s)
        with gzip.open(os.path.join(MODELS, f'main_seed{s}.txt.gz'), 'wt') as f:
            f.write(mm.model_to_string())
        print('seed', s, 'saved', flush=True)
    info = dict(features=feats, base_cols=BASE, linear_coefs=[float(c) for c in coef], rounds=rounds, params=PARAMS, train_rows=int(len(L)), train_through=str(L.date.max().date()),
                holdout_rmse=round(float(np.sqrt((err ** 2).mean())), 4))
    json.dump(info, open(os.path.join(MODELS, 'main_info.json'), 'w'))


if __name__ == '__main__':
    main()
