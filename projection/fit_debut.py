"""Fit the first-starter rating (21 Oct 2026, owner rule: Proj is built on ATW figures only, so no results-file rating anywhere).

A first starter has no form, so its rating is the race's level plus its price against the field:
    proj = mean(Proj of the race's runners with 3+ runs) + a + b x (ln price - mean ln price of the field)
Fitted here on the runner pages' ratings only (data/tr_form, as TopRate gives them): the debut run's page rating minus the mean formula projection of the
same race's experienced runners (3+ earlier runs). The price is market data (starting price from the results files, which also give the whole field so the
field mean is exact); no results-file rating is read. A debut = the earliest rated run of a horse whose page lists 18 runs or fewer (the page lists about
19, so a shorter list is a whole career). Writes the 'debut' key of projection/models_tr/formula.json.
Run: PYTHONPATH=. PROJECTION_RATINGS=toprate python projection/fit_debut.py"""
import glob
import json
import os
import sys

import numpy as np
import pandas as pd

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from projection import features as F

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
FJ = os.path.join(ROOT, 'projection', 'models_tr', 'formula.json')
MIN_EXP = 3          # the live rule: a race needs this many runners with 3+ runs to take a level from
FIT_MIN_EXP = int(os.environ.get('FIT_MIN_EXP', MIN_EXP))   # sensitivity check only: fewer experienced runners in the store (it holds part of each field)
FIRST_TEST = '2026-01-01'


def main():
    fj = json.load(open(FJ))
    K = fj['K']
    rp = F.runner_page_runs().sort_values(['horse_id', 'date']).reset_index(drop=True)
    g = rp.groupby('horse_id')
    for k in range(1, K + 1):
        rp[f'r{k}'] = g.wpr.shift(k)
    rp['n'] = g.cumcount()
    rp['tot'] = g.wpr.transform('size')
    pred = np.full(len(rp), np.nan)
    for n in range(1, K + 1):
        m = (rp.n.clip(upper=K) == n).values
        cols = [f'r{k}' for k in range(1, n + 1)]
        w = np.array(fj['coef'][str(n)])
        pred[m] = w[0] + rp.loc[m, cols].values @ w[1:]
    rp['pred'] = pred
    # race id and the whole field's starting prices from the results files (no rating column is read)
    res = []
    for f in sorted(glob.glob(os.path.join(ROOT, 'race_results_20*.csv.gz'))):
        res.append(pd.read_csv(f, usecols=['race_id', 'date', 'horse_id', 'priceStarting', 'isBarrierTrial'], low_memory=False))
    res = pd.concat(res, ignore_index=True)
    res = res[res.isBarrierTrial.fillna(0).astype(int) == 0]
    res['date'] = pd.to_datetime(res.date)
    res['horse_id'] = pd.to_numeric(res.horse_id, errors='coerce')
    res['lp'] = np.log(pd.to_numeric(res.priceStarting, errors='coerce').where(lambda s: s > 1))
    fld = res.dropna(subset=['lp']).groupby('race_id').lp.agg(['mean', 'count']).rename(columns={'mean': 'lpm', 'count': 'lpn'})
    rid = res.drop_duplicates(['horse_id', 'date'])[['horse_id', 'date', 'race_id', 'lp']].rename(columns={'race_id': 'rrid'})
    rp = rp.merge(rid, on=['horse_id', 'date'], how='left')
    rp = rp.merge(fld, left_on='rrid', right_index=True, how='left')
    exp = rp[(rp.n >= MIN_EXP) & rp.pred.notna() & rp.rrid.notna()].groupby('rrid').pred.agg(['mean', 'count']).rename(columns={'mean': 'exm', 'count': 'exn'})
    rp = rp.merge(exp, left_on='rrid', right_index=True, how='left')
    d = rp[(rp.n == 0) & (rp.tot <= 18) & rp.lp.notna() & rp.exm.notna() & (rp.exn >= FIT_MIN_EXP) & (rp.lpn >= 5)].copy()
    d['y'] = d.wpr - d.exm
    d['x'] = d.lp - d.lpm
    print(len(d), 'debut runs;', d.date.min().date(), 'to', d.date.max().date())
    def fit(a):
        X = np.c_[np.ones(len(a)), a.x.values]
        w = np.linalg.lstsq(X, a.y.values, rcond=None)[0]
        return w, float(np.std(a.y.values - X @ w))
    tr, te = d[d.date < FIRST_TEST], d[d.date >= FIRST_TEST]
    if len(tr) > 100 and len(te) > 100:
        w, _ = fit(tr)
        rm = lambda e: float(np.sqrt(np.mean(e ** 2)))
        print(f'held out {len(te)} runs (from {FIRST_TEST}): a={w[0]:.3f} b={w[1]:.3f}  RMSE price model {rm(te.y.values - (w[0] + w[1] * te.x.values)):.2f}  constant {rm(te.y.values - tr.y.mean()):.2f}')
    w, sd = fit(d)
    print(f'all: a={w[0]:.4f} b={w[1]:.4f} sd={sd:.2f}  (old fit on results-file ratings: a=-1.4487 b=-5.3436 sd=8.66)')
    fj['debut'] = {'a': round(float(w[0]), 4), 'b': round(float(w[1]), 4), 'sd': round(sd, 2), 'min_experienced': MIN_EXP,
                   'basis': f'{len(d)} debut runs on the runner pages (ATW ratings as given, no results-file rating), rating minus mean formula Proj of the race\'s 3+-run runners on ln(starting price) minus field mean ln price (results files give the field); held-out from {FIRST_TEST} in the console output of fit_debut.py'}
    if '--write' in sys.argv:
        json.dump(fj, open(FJ, 'w'), indent=1)
        print('written', FJ)


if __name__ == '__main__':
    main()
