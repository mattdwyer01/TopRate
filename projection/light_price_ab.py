"""A/B for the light-history model (0-2 prior runs): with the runner's own price vs without, on the current rating source.

Same split as train_light.py (train before 2025, early-stop 2025-01..06, score 2025-07 onward), one seed, nothing is written to the models folder.
Prints holdout RMSE by stage and how closely each arm's within-race ordering follows the starting-price ordering.
usage: PROJECTION_RATINGS=toprate python projection/light_price_ab.py
"""
import json
import os
import sys

import lightgbm as lgb
import numpy as np
import pandas as pd

sys.path.insert(0, os.path.dirname(__file__))
import features as F  # noqa: E402
import train_light as T  # noqa: E402


def main():
    H = F.load_history()
    levels = json.load(open(os.path.join(F.MODELS, 'levels.json')))
    L, t3 = T.assemble(H, levels)
    L['lp'] = np.log(L.priceStarting.where(L.priceStarting > 1))
    L = L[(L.nruns <= 2) & (L.date >= '2019-01-01')].copy()
    L['sex'] = pd.Categorical(L.horse_sex, categories=levels['sex'])
    tr, va, te = L[L.date < '2025-01-01'], L[(L.date >= '2025-01-01') & (L.date < '2025-07-01')], L[L.date >= '2025-07-01'].copy()
    te = te[te.lp.notna() & te.wpr.notna()]
    print('rows', len(L), 'test rows with price', len(te), flush=True)
    for price, name in ((False, 'no price'), (True, 'price')):
        feats = T.light_features(t3, price)
        m = lgb.train(dict(T.PARAMS, seed=1), lgb.Dataset(tr[feats], tr.wpr), 3000, valid_sets=[lgb.Dataset(va[feats], va.wpr)],
                      callbacks=[lgb.early_stopping(60, verbose=False)])
        te['p_' + str(price)] = m.predict(te[feats], num_iteration=m.best_iteration)
        err = te.wpr - te['p_' + str(price)]
        rm = {s: round(float(np.sqrt((err[te.nruns == s] ** 2).mean())), 3) for s in (0, 1, 2)}
        # within-race rank correlation with the market, light runners only (races with 4+ of them are rare, so use all test rows grouped by race)
        rc = []
        for _, g in te.groupby('race_id'):
            if len(g) >= 3:
                rc.append(pd.Series(g['p_' + str(price)].values).corr(pd.Series(-g.lp.values), method='spearman'))
        print(f'{name}: RMSE by stage {rm}, overall {np.sqrt((err ** 2).mean()):.3f}, mean within-race rank corr with market {np.nanmean(rc):.3f} ({len(rc)} races)', flush=True)


if __name__ == '__main__':
    main()
