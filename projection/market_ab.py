"""A/B: does adding the horse's own market price to the MAIN model (3+ prior runs) help, and how much does it turn the projection into the market?

Same features and split as train_main.py / ab_ratings.py (train before 2025, early-stop 2025-01..06, score 2025-07 onward, one seed). Arm A is the
current feature set, arm B adds log(starting price) and the race-normalised log implied probability. Starting price stands in for the live price
(training has no earlier price), so the gain is an upper bound for a live fixed price taken hours out. Run with PROJECTION_RATINGS=toprate.
usage: PROJECTION_RATINGS=toprate python projection/market_ab.py
"""
import os
import sys

import numpy as np
import pandas as pd

sys.path.insert(0, os.path.dirname(__file__))
import features as F  # noqa: E402
import train_main as T  # noqa: E402
from ab_ratings import score  # noqa: E402


def main():
    L = T.assemble()
    feats = T.ORIGINAL + F.LADDER_FEATURES
    L = L[(L.nruns >= 3) & L[T.BASE].notna().all(axis=1) & L.wpr.notna() & (L.date >= '2018-01-01')].copy()
    L['sp'] = pd.to_numeric(L.priceStarting, errors='coerce')
    L.loc[L.sp <= 1, 'sp'] = np.nan
    L['mk_lp'] = np.log(L.sp)
    ip = 1 / L.sp
    L['mk_p'] = np.log(ip / ip.groupby(L.race_id).transform('sum'))
    book = ip.groupby(L.race_id).transform('sum')
    n_ok = L.sp.notna().groupby(L.race_id).transform('all')
    L = L[n_ok & (book > 1.05) & (book < 2.0)].copy()   # complete priced races with a sane book
    tr, va, te = L[L.date < '2025-01-01'], L[(L.date >= '2025-01-01') & (L.date < '2025-07-01')], L[L.date >= '2025-07-01'].copy()
    print('rows', len(L), 'train/valid/test', len(tr), len(va), len(te), flush=True)
    for arm, fs in (('A base', feats), ('B +market', feats + ['mk_lp', 'mk_p'])):
        m, coef = T.fit(tr, fs, None, 1, valid=va)
        te['pred_' + arm[0]] = np.c_[np.ones(len(te)), te[T.BASE].values] @ coef + m.predict(te[fs], num_iteration=m.best_iteration)
        err = te.wpr - te['pred_' + arm[0]]
        print(arm, f'RMSE {np.sqrt((err ** 2).mean()):.4f} iters {m.best_iteration}', flush=True)
    te['positionFinish'] = te.positionFinish
    te['mk'] = -te.mk_lp
    for col in ('pred_A', 'pred_B', 'mk'):
        ll, top, n, beta = score(te, col, betas=(1.0,) if col == 'mk' else (0.05, 0.08, 0.1, 0.12, 0.15, 0.2, 0.25, 0.3))
        print(f'{col}: winner log-lik {ll:.4f} top pick wins {top:.2%} races {n} beta {beta}')
    # how often the top pick is the market favourite, and within-race rank correlation with the market
    for col in ('pred_A', 'pred_B'):
        fav = tot = 0
        rc = []
        for _, g in te.groupby('race_id'):
            if len(g) < 4:
                continue
            tot += 1
            fav += g[col].values.argmax() == g.sp.values.argmin()
            rc.append(pd.Series(g[col].values).corr(pd.Series(-g.sp.values), method='spearman'))
        print(f'{col}: top pick is favourite {fav / tot:.1%}, mean rank corr with market {np.nanmean(rc):.3f}')
    te[['race_id', 'horse_id', 'pred_A', 'pred_B', 'wpr', 'sp', 'positionFinish']].to_pickle('/tmp/market_ab.pkl')


if __name__ == '__main__':
    main()
