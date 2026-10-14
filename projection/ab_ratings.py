"""A/B: the main model trained on our own ratings vs on TopRate's raw ratings in the results files (14 Oct 2026).

Same features, same split as train_main.py (train before 2025, early-stop on 2025-01..06, score 2025-07 onward), one seed, nothing written to
projection/models. TopRate-authored sectional / race-shape columns stay blank in both arms so only the rating source differs. Arms are compared on
the (race, horse) pairs both can score, by winner log-likelihood of a within-race softmax (beta fitted per arm) and top-pick strike rate; rating
RMSE is on each arm's own scale so it is not comparable between arms.

usage: python projection/ab_ratings.py [own|toprate|both]
"""
import os
import sys

import numpy as np
import pandas as pd

sys.path.insert(0, os.path.dirname(__file__))
import features as F  # noqa: E402
import train_main as T  # noqa: E402


def toprate_overlay(df):
    for c in df.columns:
        if c.startswith(F.TOPRATE_AUTHORED):
            df[c] = np.nan
    return df


def run(arm):
    if arm == 'toprate':
        F.own_overlay = toprate_overlay
    L = T.assemble()
    feats = T.ORIGINAL + F.LADDER_FEATURES
    L = L[(L.nruns >= 3) & L[T.BASE].notna().all(axis=1) & L.wpr.notna() & (L.date >= '2018-01-01')].copy()
    tr, va, te = L[L.date < '2025-01-01'], L[(L.date >= '2025-01-01') & (L.date < '2025-07-01')], L[L.date >= '2025-07-01'].copy()
    print(arm, 'rows', len(L), 'train/valid/test', len(tr), len(va), len(te), flush=True)
    m, coef = T.fit(tr, feats, None, 1, valid=va)
    te['pred'] = np.c_[np.ones(len(te)), te[T.BASE].values] @ coef + m.predict(te[feats], num_iteration=m.best_iteration)
    err = te.wpr - te.pred
    print(arm, f'RMSE {np.sqrt((err ** 2).mean()):.4f} best_iter {m.best_iteration}', flush=True)
    out = te[['race_id', 'horse_id', 'pred', 'wpr', 'positionFinish', 'priceStarting', 'date']].copy()
    out.to_pickle(f'/tmp/ab_{arm}.pkl')
    return out


def score(x, col, betas=(0.05, 0.08, 0.1, 0.12, 0.15, 0.2, 0.25, 0.3)):
    best = None
    for b in betas:
        ll, top, n = [], [], 0
        for _, g in x.groupby('race_id'):
            w = (g.positionFinish == 1).values
            if w.sum() != 1 or len(g) < 4:
                continue
            s = g[col].values
            p = np.exp(b * (s - s.max()))
            p /= p.sum()
            ll.append(np.log(p[w][0]))
            top.append(w[s.argmax()])
        r = (np.mean(ll), np.mean(top), len(ll), b)
        if best is None or r[0] > best[0]:
            best = r
    return best


def compare():
    a, b = pd.read_pickle('/tmp/ab_own.pkl'), pd.read_pickle('/tmp/ab_toprate.pkl')
    m = a.merge(b, on=['race_id', 'horse_id'], suffixes=('_own', '_tr'))
    m['positionFinish'] = m.positionFinish_own
    print('common pairs', len(m), 'races', m.race_id.nunique())
    for col in ('pred_own', 'pred_tr'):
        ll, top, n, beta = score(m, col)
        print(f'{col}: winner log-lik {ll:.4f}  top pick wins {top:.3%}  races {n}  beta {beta}')
    m['avg'] = (m.pred_own - m.pred_own.mean()) + (m.pred_tr - m.pred_tr.mean())
    ll, top, n, beta = score(m, 'avg')
    print(f'average of both: winner log-lik {ll:.4f}  top pick wins {top:.3%}  beta {beta}')
    m['_p'] = 1 / m.priceStarting_own.replace(0, np.nan)
    m['mk'] = -np.log(m.priceStarting_own)
    mm = m.dropna(subset=['mk'])
    ll, top, n, beta = score(mm, 'mk', betas=(1.0,))
    print(f'market (SP) same pairs: winner log-lik {ll:.4f}  favourite wins {top:.3%}')


if __name__ == '__main__':
    arm = sys.argv[1] if len(sys.argv) > 1 else 'both'
    if arm in ('own', 'toprate'):
        run(arm)
    else:
        compare()
