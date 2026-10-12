"""Trains the suitability model (13 Oct 2026 refit on our own ratings): a small gradient-boosted correction on the main model's out-of-sample
residual, from the run's tactical suitability (comments, finishing profile from raw margins, settle history, jockey and trainer tendencies, draw
and day-of track bias). Writes projection/models/suitability_model.txt and suitability_features.json.

Residuals: the main model is fitted through 2024 with 2025-01..06 for early stopping, and its predictions for 2025-01 onward are out of sample.
The suitability model is fitted on 2025-01..2026-04 residuals, checked on 2026-05 onward, then refitted on everything with the same settings.
Settings are those of the model it replaces (300 rounds, learning rate 0.04, 15 leaves, 500 minimum rows per leaf, L2 50, 0.8 feature fraction).

usage: python projection/train_suit.py
"""
import json
import os
import sys

import lightgbm as lgb
import numpy as np
import pandas as pd

sys.path.insert(0, os.path.dirname(__file__))
import features as F  # noqa: E402
import train_main as T  # noqa: E402

M = F.MODELS
PARAMS = dict(objective='regression', learning_rate=0.04, num_leaves=15, min_data_in_leaf=500, feature_fraction=0.8, lambda_l2=50, num_threads=4,
              verbosity=-1, seed=0)
ROUNDS = 300


def main():
    sfeats = json.load(open(os.path.join(M, 'suitability_features.json')))
    L = T.assemble()
    r_ph = L  # assemble() returns the main frame with all columns
    ph = F.build_pos_hist(L)
    L = L[(L.nruns >= 3) & L[T.BASE].notna().all(axis=1) & L.wpr.notna() & (L.date >= '2018-01-01')].copy()
    feats = T.ORIGINAL + F.LADDER_FEATURES
    tr, va = L[L.date < '2025-01-01'], L[(L.date >= '2025-01-01') & (L.date < '2025-07-01')]
    m, coef = T.fit(tr, feats, None, 1, valid=va)
    oos = L[L.date >= '2025-01-01'].copy()
    oos['base'] = np.c_[np.ones(len(oos)), oos[T.BASE].values] @ coef + m.predict(oos[feats], num_iteration=m.best_iteration)
    oos['res'] = oos.wpr - oos.base
    print('main out-of-sample rows', len(oos), 'rmse', round(float(np.sqrt((oos.res ** 2).mean())), 4), flush=True)
    # suitability inputs for the whole history (the tendency tables are as-of), then keep the out-of-sample rows
    Y = F.load_results_all()
    S = F.build_suit(Y, ph)
    S = S.drop_duplicates(['race_id', 'horse_id'])
    Z = oos[['race_id', 'horse_id', 'date', 'res', 'base', 'bf', 'field_size', 'dist', 'going_num']].merge(S.drop(columns=['date']), on=['race_id', 'horse_id'], how='left', suffixes=('', '_s'))
    Z = Z.merge(ph[['race_id', 'horse_id', 'm800_hist3', 'own_rel']], on=['race_id', 'horse_id'], how='left')
    Z['sty'] = Z.pos_hist3 - 0.5
    Z['i_front'], Z['i_front2'] = Z.fa_cum * Z.sty, Z.fa_last * Z.sty
    Z['i_out'], Z['i_out2'] = Z.oa_cum * (Z.bf - 0.5), Z.oa_last * (Z.bf - 0.5)
    Z['j_style'], Z['j_p8_x'] = Z.j_dev * Z.sty, Z.j_p8 - Z.pos_hist3
    for c in sfeats:
        if c not in Z.columns:
            Z[c] = np.nan
    print('inputs filled share', {c: round(float(Z[c].notna().mean()), 2) for c in sfeats if Z[c].notna().mean() < 0.9}, flush=True)
    fit_, chk = Z[Z.date < '2026-05-01'], Z[Z.date >= '2026-05-01']
    mod = lgb.train(PARAMS, lgb.Dataset(fit_[sfeats], fit_.res.values), ROUNDS)
    adj = mod.predict(chk[sfeats])
    e0, e1 = chk.res.values, chk.res.values - adj
    slope = np.polyfit(adj, e0, 1)[0]
    print(f'check 2026-05+: n {len(chk)} rmse without {np.sqrt((e0 ** 2).mean()):.4f} with {np.sqrt((e1 ** 2).mean()):.4f} adj sd {adj.std():.3f} slope of residual on adj {slope:.2f}', flush=True)
    for k in (0.5, 0.75, 1.0, 1.25, 1.5):
        print(f'  scale {k}: rmse {np.sqrt(((e0 - k * adj) ** 2).mean()):.4f}')
    final = lgb.train(PARAMS, lgb.Dataset(Z[sfeats], Z.res.values), ROUNDS)
    final.save_model(os.path.join(M, 'suitability_model.txt'))
    json.dump(sfeats, open(os.path.join(M, 'suitability_features.json'), 'w'))
    print('saved suitability model; adj sd on all', round(float(final.predict(Z[sfeats]).std()), 3))


if __name__ == '__main__':
    main()
