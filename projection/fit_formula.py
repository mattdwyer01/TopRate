"""Fit the Proj formula (16 Oct 2026, owner: no model for Proj, a formula on the runner pages' data).

Proj = intercept + sum of weight_k x (rating of the k-th last run), the ratings as given on TopRate's runner pages (weight adjusted to the horse's next start,
overseas runs included, trials and jumps out). One set of weights for each count of earlier runs (1 to 7, then 8 or more use the last 8), fitted by least
squares on every page run that has that many earlier runs. Writes projection/models_tr/formula.json (coefficients and the error sd for each count).
Run: PROJECTION_RATINGS=toprate python projection/fit_formula.py"""
import json
import os
import sys

import numpy as np
import pandas as pd

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from projection import features as F

K = 8
CLIP_LOW = 10.0     # outlier trim (22 Oct 2026, research/proj_outlier_test.py): an earlier run is lifted to at most this far below the median of the last six; None = off
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'models_tr', 'formula.json')


def main():
    rp = F.runner_page_runs().sort_values(['horse_id', 'date']).reset_index(drop=True)
    g = rp.groupby('horse_id')
    for k in range(1, K + 1):
        rp[f'r{k}'] = g.wpr.shift(k)
    rp['n'] = g.cumcount()
    lags = [f'r{k}' for k in range(1, K + 1)]
    rp[lags] = F.clip_low_lags(rp[lags].values, CLIP_LOW)
    out = {'K': K, 'clip_low': CLIP_LOW, 'coef': {}, 'sd': {}, 'n_fit': {}}
    for n in range(1, K + 1):
        m = rp.n.clip(upper=K) == n
        cols = [f'r{k}' for k in range(1, n + 1)]
        a = rp[m]
        X = np.c_[np.ones(len(a)), a[cols].values]
        w = np.linalg.lstsq(X, a.wpr.values, rcond=None)[0]
        out['coef'][str(n)] = [round(float(x), 5) for x in w]
        out['sd'][str(n)] = round(float(np.std(a.wpr.values - X @ w)), 2)
        out['n_fit'][str(n)] = int(len(a))
        print(n, len(a), np.round(w, 3), out['sd'][str(n)])
    json.dump(out, open(OUT, 'w'), indent=1)


if __name__ == '__main__':
    main()
