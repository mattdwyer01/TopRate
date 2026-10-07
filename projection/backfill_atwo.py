"""Fills blank atwo in wpr_projection_log.csv.gz with the modelled offset (atw_offset_model.py), from each run's own weight, age, sex and distance in
the results files. Only blanks are touched, so measured offsets stay. Lets Review and the day results rank past races on the same ATW scale as the race page.

Usage: python projection/backfill_atwo.py
"""
import glob
import os
import sys

import numpy as np
import pandas as pd

sys.path.insert(0, os.path.dirname(__file__))
import atw_offset_model as AM  # noqa: E402
import projlog  # noqa: E402


def main():
    lg = projlog.load()
    r = pd.concat([pd.read_csv(p, usecols=['run_id', 'date', 'distance', 'weightCarried', 'horse_age', 'horse_sex'], low_memory=False)
                   for p in sorted(glob.glob(os.path.join(projlog.ROOT, 'race_results_20*.csv.gz')))[-2:]]).drop_duplicates('run_id', keep='last')
    todo = lg[lg.atwo.isna()].merge(r, on='run_id', how='left', suffixes=('', '_r'))
    ok = todo.weightCarried.notna() & todo.horse_age.notna()
    todo.loc[ok, 'pred'] = AM.predict(todo.weightCarried[ok], todo.distance[ok], todo.date_r[ok] if 'date_r' in todo else todo.date[ok], todo.horse_age[ok], todo.horse_sex[ok])
    m = dict(zip(todo.run_id[ok], todo.pred[ok]))
    fill = lg.atwo.isna() & lg.run_id.isin(m)
    lg.loc[fill, 'atwo'] = lg.loc[fill, 'run_id'].map(m)
    lg.to_csv(projlog.PATH, index=False, compression='gzip', float_format='%.2f')
    print('filled', int(fill.sum()), 'of', int(lg.atwo.isna().sum() + fill.sum()), 'blanks; now blank', int(lg.atwo.isna().sum()))


if __name__ == '__main__':
    main()
