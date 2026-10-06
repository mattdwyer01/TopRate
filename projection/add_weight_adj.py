"""One-off: adds the weight-carried adjustment (projection.run.WT_K per kg above the field average) to rows of
wpr_projection_log.csv.gz that were written before it existed (wtadj column missing or zero), so past races show the same
definition of Proj as future ones. Weight comes from the results files (run_id), falling back to toprate_runners.csv."""
import glob
import os
import sys

import numpy as np
import pandas as pd

sys.path.insert(0, os.path.dirname(os.path.dirname(__file__)))
from projection import projlog  # noqa: E402
from projection.run import WT_K  # noqa: E402


def main():
    lg = projlog.load()
    w = pd.concat([pd.read_csv(f, usecols=['run_id', 'race_id', 'weightCarried'], low_memory=False) for f in sorted(glob.glob(os.path.join(projlog.ROOT, 'race_results_20*.csv.gz')))])
    w = w.dropna(subset=['run_id']).drop_duplicates('run_id').set_index('run_id').weightCarried
    r = pd.read_csv(os.path.join(projlog.ROOT, 'toprate_runners.csv'), usecols=['run_id', 'weight_carried'], low_memory=False).dropna().drop_duplicates('run_id').set_index('run_id').weight_carried
    lg['wt'] = lg.run_id.map(w).fillna(lg.run_id.map(r))
    lg.loc[~lg.wt.between(40, 80), 'wt'] = np.nan
    todo = lg.wtadj.fillna(0).eq(0)
    rel = lg.wt - lg.groupby('race_id').wt.transform('mean')
    new = (-WT_K * rel).fillna(0.0)
    lg.loc[todo, 'proj'] = lg.loc[todo, 'proj'] + new[todo]
    lg.loc[todo, 'wtadj'] = new[todo]
    print('rows', len(lg), 'adjusted', int(todo.sum()), 'with weight', int(lg.wt.notna().sum()), 'wtadj sd', round(float(lg.wtadj.std()), 2))
    lg = lg.drop(columns=['wt'])
    lg['date'] = lg.date.dt.strftime('%Y-%m-%d')
    lg[projlog.COLS].to_csv(projlog.PATH, index=False, compression='gzip', float_format='%.2f')


if __name__ == '__main__':
    main()
