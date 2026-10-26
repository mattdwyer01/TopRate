"""Does how a horse travelled last start (distance from the rail through the race) predict its NEXT rating, beyond its earlier ratings?

The Racing Victoria PDFs (rc_pdf_gps.py) give the distance off the rail by section. The idea punters call a "trip": a horse that ran wide
without cover and was beaten may have run better than its rating, one that sat on the fence may have been flattered. Tested on VIC/SA runs
since 28 Apr 2026 (rating = results-file wpr, which stops on 8 Oct 2026):

  next rating  ~  last 3 ratings  +  last run's width features   (OLS, rating as given, plain scale)

Width features of the last run (all relative to the rest of that field, so track and day effects drop out):
  mid_w   mean distance off the rail over the middle sections (not the first or the last 200m)
  w800    distance off the rail at 800m from home
  extra   metres run beyond the race distance (racing.com GPS, ground lost)
and the same multiplied by how far the horse was beaten (a wide horse that won is not a hard-luck story).

  PYTHONPATH=. python research/rail_trip_rating_test.py
"""
import glob
import os
import sys

import numpy as np
import pandas as pd

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'analysis', 'trip_map'))
import build_trip_map as B  # noqa: E402

ROOT = B.ROOT


def run_features():
    fs = sorted(glob.glob(os.path.join(ROOT, 'data', 'gps', 'rc_pdf_rail_*.parquet')))
    d = pd.concat([pd.read_parquet(f) for f in fs], ignore_index=True)
    d['meet_code'] = d.meet_code.astype(str)
    key = ['meet_code', 'race_no', 'tab_no']
    g = d.groupby(key)
    rows = []
    for k, z in g:
        z = z.sort_values('from_m', ascending=False)
        mid = z[(z.from_m < z.from_m.max()) & (z.from_m > 200)]
        r800 = z[z.from_m == 800].rail_m
        rows.append((*k, mid.rail_m.mean() if len(mid) >= 2 else np.nan, r800.iloc[0] if len(r800) else np.nan, len(z)))
    return pd.DataFrame(rows, columns=key + ['mid_w', 'w800', 'npts'])


def main():
    res = B.load_results()
    a = B.vicsa_runs(res)
    a['meet_code'] = a.meet_code.astype(str)
    a = a.merge(run_features(), on=['meet_code', 'race_no', 'tab_no'], how='inner')
    r = res[['race_id', 'horse_id', 'wpr', 'margin800m']].copy()
    # beaten margin at the finish and rating of every earlier run come from the results files
    full = pd.read_csv(os.path.join(ROOT, 'race_results_2026.csv.gz'), usecols=['race_id', 'horse_id', 'marginFinish'], low_memory=False)
    a = a.merge(r[['race_id', 'horse_id', 'wpr']], on=['race_id', 'horse_id'], how='left').merge(full, on=['race_id', 'horse_id'], how='left')
    for c in ('mid_w', 'w800', 'extra'):
        a[c + '_rel'] = a[c] - a.groupby('race_id')[c].transform('mean')
    a['beaten'] = a.marginFinish.clip(lower=0, upper=10)
    a['mid_x_beaten'] = a.mid_w_rel * a.beaten
    # horse history of ratings from all results (not only the PDF runs)
    h = res[['horse_id', 'date', 'wpr', 'race_id']].dropna(subset=['wpr']).sort_values(['horse_id', 'date', 'race_id'])
    h['p1'] = h.groupby('horse_id').wpr.shift(1)
    h['p2'] = h.groupby('horse_id').wpr.shift(2)
    h['p3'] = h.groupby('horse_id').wpr.shift(3)
    h['prev_race'] = h.groupby('horse_id').race_id.shift(1)
    h['p123'] = h[['p1', 'p2', 'p3']].mean(axis=1)
    # target run t, features from run t-1 (the PDF run)
    feats = a[['race_id', 'horse_id', 'mid_w_rel', 'w800_rel', 'extra_rel', 'beaten', 'mid_x_beaten']].rename(columns={'race_id': 'prev_race'})
    t = h.merge(feats, on=['horse_id', 'prev_race'], how='inner').dropna(subset=['wpr', 'p1', 'p123'])
    t = t[t.date >= '2026-04-29']
    t['y'] = t.wpr - t.groupby('race_id').wpr.transform('mean')
    for c in ('p1', 'p123'):
        t[c] = t[c] - t.groupby('race_id')[c].transform('mean')
    print('pairs (PDF run followed by a rated run):', len(t), 'horses', t.horse_id.nunique(), 'races', t.race_id.nunique())
    base = ['p1', 'p123']

    def ols(cols, df):
        X = np.column_stack([np.ones(len(df))] + [df[c].values for c in cols])
        y = df.y.values
        b, *_ = np.linalg.lstsq(X, y, rcond=None)
        res_ = y - X @ b
        s2 = res_.var(ddof=X.shape[1])
        se = np.sqrt(np.diag(s2 * np.linalg.inv(X.T @ X)))
        return b, se, float(np.sqrt((res_ ** 2).mean()))

    t = t.dropna(subset=['mid_w_rel', 'w800_rel', 'extra_rel', 'mid_x_beaten'])
    print('complete rows', len(t))
    b0, se0, rm0 = ols(base, t)
    print(f'baseline (last rating, mean of last 3): RMSE {rm0:.3f}')
    for name, cols in (('mid-race width', ['mid_w_rel']), ('width at 800m', ['w800_rel']), ('ground lost (extra metres)', ['extra_rel']),
                       ('mid width x beaten', ['mid_w_rel', 'mid_x_beaten']), ('all', ['mid_w_rel', 'w800_rel', 'extra_rel', 'mid_x_beaten'])):
        b, se, rm = ols(base + cols, t)
        out = ', '.join(f'{c} {b[1 + base.index(c) if c in base else 1 + len(base) + cols.index(c)]:+.3f} (t {b[1 + len(base) + cols.index(c)] / se[1 + len(base) + cols.index(c)]:+.1f})' for c in cols)
        print(f'+ {name:30s} RMSE {rm:.3f} (gain {100 * (rm0 - rm) / rm0:+.2f}%)  {out}')


if __name__ == '__main__':
    main()
