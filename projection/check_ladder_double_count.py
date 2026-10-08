"""Does the suitability adjustment double count the ladder features? (Oct 2026)

The suitability model (models/suitability_model.txt) was fitted against the residuals of the OLD 139-feature main model, and the main model has
since gained the ladder block (settle map, sectional speed, race shape ...) which overlaps with what the suitability inputs read. Test: train the
main model twice on data before 2025 (139 features, then 179), predict 2025-07 onward, compute the suitability adjustment for the same runs, and
regress the residual (actual - main prediction) on the adjustment. A slope near 1 means the adjustment still carries information the base lacks;
a slope clearly below 1 on the ladder model (and not on the old one) means part of it is now counted twice.

usage: python projection/check_ladder_double_count.py     (about 40 minutes, 4 cores)
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


def main():
    levels = json.load(open(os.path.join(M, 'levels.json')))
    H = F.load_history()
    r = F.build_main(H, levels)
    ph = F.build_pos_hist(r)
    tf, svd = F.load_text(os.path.join(M, 'text_svd.joblib'))
    L = pd.concat([r, F.build_field(r), F.build_trials(r), F.build_trials3(r), F.text_features(r, pd.Series(True, index=r.index), tf, svd), F.build_ladder(r, ph=ph)], axis=1)
    L = L.loc[:, ~L.columns.duplicated()]
    L['sex'] = pd.Categorical(L.horse_sex, categories=levels['sex'])
    L = L[(L.nruns >= 3) & L[T.BASE].notna().all(axis=1) & L.wpr.notna() & (L.date >= '2018-01-01')].copy()
    tr, va, te = L[L.date < '2025-01-01'], L[(L.date >= '2025-01-01') & (L.date < '2025-07-01')], L[L.date >= '2025-07-01'].copy()
    preds = {}
    for name, feats in [('old139', T.ORIGINAL), ('ladder179', T.ORIGINAL + F.LADDER_FEATURES)]:
        m, coef = T.fit(tr, feats, None, 1, valid=va)
        preds[name] = np.c_[np.ones(len(te)), te[T.BASE].values] @ coef + m.predict(te[feats], num_iteration=m.best_iteration)
        print(name, 'rounds', m.best_iteration, 'test RMSE %.4f' % np.sqrt(((te.wpr.values - preds[name]) ** 2).mean()), flush=True)
    # suitability adjustment for the same runs (as run.py does it)
    Y = F.load_results_all()
    S = F.build_suit(Y, ph, bias_since='2025-06-28').query("date >= '2025-07-01'").drop_duplicates(['race_id', 'horse_id'])
    Z = te[['race_id', 'horse_id', 'bf', 'field_size', 'dist', 'going_num']].merge(S, on=['race_id', 'horse_id'], how='left', suffixes=('', '_s'))
    Z = Z.merge(ph[['race_id', 'horse_id', 'm800_hist3', 'own_rel']], on=['race_id', 'horse_id'], how='left')
    Z['sty'] = Z.pos_hist3 - 0.5
    Z['i_front'], Z['i_front2'] = Z.fa_cum * Z.sty, Z.fa_last * Z.sty
    Z['i_out'], Z['i_out2'] = Z.oa_cum * (Z.bf - 0.5), Z.oa_last * (Z.bf - 0.5)
    Z['j_style'], Z['j_p8_x'] = Z.j_dev * Z.sty, Z.j_p8 - Z.pos_hist3
    sfeats = json.load(open(os.path.join(M, 'suitability_features.json')))
    sm = lgb.Booster(model_file=os.path.join(M, 'suitability_model.txt'))
    for c in sfeats:
        if c not in Z.columns:
            Z[c] = np.nan
    Z['adj'] = sm.predict(Z[sfeats])
    adj = te[['race_id', 'horse_id']].merge(Z[['race_id', 'horse_id', 'adj']].drop_duplicates(['race_id', 'horse_id']), on=['race_id', 'horse_id'], how='left').adj.values
    for name, p in preds.items():
        res = te.wpr.values - p
        ok = ~np.isnan(adj)
        a, y = adj[ok], res[ok]
        b = (np.c_[np.ones(ok.sum()), a].T @ np.c_[np.ones(ok.sum()), a])
        coef = np.linalg.solve(b, np.c_[np.ones(ok.sum()), a].T @ y)
        se = np.sqrt(((y - np.c_[np.ones(ok.sum()), a] @ coef).var()) / ((a - a.mean()) ** 2).sum())
        print(f'{name}: n {ok.sum()} slope of residual on adj {coef[1]:.3f} (se {se:.3f})', end=' | ')
        print(' '.join(f'k={k}: RMSE {np.sqrt(((y - k * a) ** 2).mean()):.4f}' for k in (0, 0.5, 0.75, 1, 1.25)), flush=True)


if __name__ == '__main__':
    main()
