"""Light-history model: should the market price be an input for every stage or only debutants? (15 Oct 2026, read-only, writes nothing.)

Same data, split and single seed as train_light.validation (train before 2025, early-stop 2025-01..06, score 2025-07 onward). Three arms:
  A price for every stage (0 to 2 prior runs)   B no price   C price for debutants only (the price column is blank for 1 and 2 prior runs)
Reports RMSE and bias by stage. Price is the starting price (as in training); live uses the fixed price.
usage: PROJECTION_RATINGS=toprate python projection/light_price_stage_ab.py
"""
import json
import os
import sys

import lightgbm as lgb
import numpy as np

sys.path.insert(0, os.path.dirname(__file__))
import features as F  # noqa: E402
import train_light as T  # noqa: E402


def main():
    H = F.load_history()
    levels = json.load(open(os.path.join(F.MODELS, 'levels.json')))
    L, t3cols = T.assemble(H, levels)
    L['lp'] = np.log(L.priceStarting.where(L.priceStarting > 1))
    L = L[(L.nruns <= 2) & (L.date >= '2019-01-01')].copy()
    L['sex'] = __import__('pandas').Categorical(L.horse_sex, categories=levels['sex'])
    L['lp_debut'] = L.lp.where(L.nruns == 0)
    tr, va, te = L[L.date < '2025-01-01'], L[(L.date >= '2025-01-01') & (L.date < '2025-07-01')], L[L.date >= '2025-07-01']
    base = T.light_features(t3cols, False)
    arms = {'A price all stages': base + ['lp'], 'B no price': base, 'C price debut only': base + ['lp_debut']}
    for name, feats in arms.items():
        m = lgb.train(dict(T.PARAMS, seed=1), lgb.Dataset(tr[feats], tr.wpr), 3000, valid_sets=[lgb.Dataset(va[feats], va.wpr)],
                      callbacks=[lgb.early_stopping(60, verbose=False)])
        err = te.wpr.values - m.predict(te[feats], num_iteration=m.best_iteration)
        rm = {s: round(float(np.sqrt((err[(te.nruns == s).values] ** 2).mean())), 3) for s in (0, 1, 2)}
        allr = round(float(np.sqrt((err ** 2).mean())), 3)
        print(f'{name:22} RMSE by stage (debut / 2nd / 3rd start) {rm}  all {allr}  rounds {m.best_iteration}', flush=True)


if __name__ == '__main__':
    main()
