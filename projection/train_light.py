"""Trains the light-history model (horses with 0-2 prior rated runs: debut, second and third starters).

Features: own WPR history, race context, trainer/jockey level effects (own-history-free), normalised typed trial and jump-out
features. Breeding (sire/dam) is left out: it added nothing in testing.

Two sets are trained (Oct 2026, Factor Ladder Review rung R24): light_seed* also reads the log of the runner's win price (starting price in
training, the live fixed price when projecting; held-out RMSE 10.82 -> 10.51, debut 11.90 -> 11.46), and light_np_seed* is the same model
without it, used when a runner has no price yet.

Validation: train through 2025-06, score 2025-07 onward for the stage-wise bias; the shipped models are then refit on all runs.
Writes projection/models/light_seed{1..5}.txt.gz and light_info.json.
"""
import glob
import gzip
import json
import os
import sys

import lightgbm as lgb
import numpy as np
import pandas as pd

sys.path.insert(0, os.path.dirname(__file__))
import features as F  # noqa: E402

HIST = ['w1', 'w2', 'mean_prev', 'best_prev', 'ff1', 'mg1', 'gap']
CTX = ['nruns', 'cls_level', 'grade', 'dist', 'field_size', 'barrier', 'bf', 'going_num', 'track_level', 'horse_age', 'sex', 'wt', 'wt_rel',
       'f_exp', 'top_exp', 'exp_rel', 'exp_rank', 'is_maiden']
TJ = ['trn_lvl', 'trn_lvl_n', 'trn_early_lvl', 'trn_early_lvl_n', 'trn_debut_lvl', 'trn_debut_lvl_n', 'jock_lvl', 'jock_lvl_n', 'jock_early_lvl',
      'jock_early_lvl_n', 'jock_debut_lvl', 'jock_debut_lvl_n']
TRI = ['trial_days', 'trial_fin_frac', 'trial_margin', 'trial_n90', 'trial_since_run']
PARAMS = dict(objective='regression', metric='l2', learning_rate=0.03, num_leaves=15, min_child_samples=100, feature_fraction=0.7, bagging_fraction=0.8,
              bagging_freq=1, lambda_l2=30, num_threads=4, verbose=-1)


def light_features(t3_cols, price=False):
    return HIST + CTX + TJ + TRI + [c for c in t3_cols if c.startswith('t3_') or c.startswith('bt_')] + (['lp'] if price else [])


def assemble(H, levels):
    r = F.build_main(H, levels)
    lt = F.build_light(r)
    tri = F.build_trials(r)
    t3 = F.build_trials3(r)
    L = pd.concat([r, lt, tri, t3], axis=1)
    return L, list(t3.columns)


def main():
    models = os.path.join(os.path.dirname(__file__), 'models')
    H = F.load_history()
    levels = json.load(open(os.path.join(models, 'levels.json')))
    L, t3cols = assemble(H, levels)
    L['lp'] = np.log(L.priceStarting.where(L.priceStarting > 1))
    L = L[(L.nruns <= 2) & (L.date >= '2019-01-01')].copy()
    L['sex'] = pd.Categorical(L.horse_sex, categories=levels['sex'])
    print('light rows', len(L), L.nruns.value_counts().sort_index().to_dict(), flush=True)
    tr = L[L.date < '2025-01-01']
    va = L[(L.date >= '2025-01-01') & (L.date < '2025-07-01')]
    te = L[L.date >= '2025-07-01']
    info = {}
    for price, prefix in [(True, 'light'), (False, 'light_np')]:
        feats = light_features(t3cols, price)
        m = lgb.train(dict(PARAMS, seed=1), lgb.Dataset(tr[feats], tr.wpr), 3000, valid_sets=[lgb.Dataset(va[feats], va.wpr)], callbacks=[lgb.early_stopping(60, verbose=False)])
        rounds = int(m.best_iteration * 1.1)
        err = te.wpr.values - m.predict(te[feats], num_iteration=m.best_iteration)
        bias = {int(s): round(float(err[(te.nruns == s).values].mean()), 3) for s in (0, 1, 2)}
        rmse = {int(s): round(float(np.sqrt((err[(te.nruns == s).values] ** 2).mean())), 3) for s in (0, 1, 2)}
        print(prefix, 'holdout 2025-07+ (model trained through 2024): RMSE by stage', rmse, 'bias by stage', bias, 'rounds', rounds, flush=True)
        for s in (1, 2, 3, 4, 5):
            mm = lgb.train(dict(PARAMS, seed=s, bagging_seed=s, feature_fraction_seed=s), lgb.Dataset(L[feats], L.wpr), rounds)
            with gzip.open(os.path.join(models, f'{prefix}_seed{s}.txt.gz'), 'wt') as f:
                f.write(mm.model_to_string())
            print(prefix, 'seed', s, 'saved', flush=True)
        sd = {int(s): round(float(np.sqrt((err[(te.nruns == s).values] ** 2).mean())), 2) for s in (0, 1, 2)}
        info[prefix] = dict(features=feats, rounds=rounds, stage_bias=bias, stage_sd=sd)
    top = info['light']
    json.dump(dict(features=top['features'], rounds=top['rounds'], stage_bias=top['stage_bias'], stage_sd=top['stage_sd'], np=info['light_np'],
                   train_rows=int(len(L)), train_through=str(L.date.max().date())), open(os.path.join(models, 'light_info.json'), 'w'), indent=1)


if __name__ == '__main__':
    main()
