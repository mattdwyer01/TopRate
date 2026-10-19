"""Calibrate a 2019+ proxy for the locked rule's inputs against the real TR / Mid / Late / Total columns (Apr-Oct 2026)."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
import numpy as np, pandas as pd
from common import *

D = load_runs()
a = pd.concat([pd.read_csv(os.path.join(ROOT, 'archive/toprate/toprate_runners_archive.csv.gz'), low_memory=False),
               pd.read_csv(os.path.join(ROOT, 'archive/toprate/toprate_runners.csv'), low_memory=False)]).drop_duplicates('run_id', keep='last')
cands = ['sect_i_time', 'sect_i_early', 'sect_i_to600', 'sect_i_l200', 'sect_i_l400', 'sect_i_l600', 'sect_i_400_200', 'sect_i_600_400',
         'sect_i_800_400', 'sect_i_800_600', 'sect_ld_early', 'wpr']
for c in cands:
    for k in (3, 5, 8):
        D[f'{c}_m{k}'] = asof_mean(D, c, k)
x = a[a.date <= '2026-10-08'][['run_id', 'toprate_rating', 'early_speed_score', 'mid_speed_score', 'late_speed_score', 'total_speed_score', 'wpr_nett', 'wpr_avg_last3', 'wpr_last1']].merge(D, on='run_id')
print(len(x), x.race_id.nunique())

def wcorr(col, real):
    r = x[['race_id', col, real]].dropna()
    r = r[r.groupby('race_id')[col].transform('size') >= 4]
    return round(pd.concat([r.groupby('race_id')[col].rank(), r.groupby('race_id')[real].rank()], axis=1).corr().iloc[0, 1], 3), len(r)
for real, cs in [('mid_speed_score', ['sect_i_800_400', 'sect_i_600_400', 'sect_i_800_600', 'sect_i_400_200']),
                 ('late_speed_score', ['sect_i_l400', 'sect_i_l600', 'sect_i_l200', 'sect_i_400_200']),
                 ('total_speed_score', ['sect_i_time', 'sect_i_l400', 'sect_i_l600']),
                 ('early_speed_score', ['sect_i_early', 'sect_i_to600', 'sect_ld_early']),
                 ('toprate_rating', ['wpr']), ('wpr_nett', ['wpr']), ('wpr_avg_last3', ['wpr'])]:
    for c in cs:
        print(real, c, [wcorr(f'{c}_m{k}', real)[0] for k in (3, 5, 8)])
x['rating_real_vs_last3'] = x['wpr_avg_last3']
print('toprate_rating vs wpr_avg_last3 (TopRate own)', wcorr('wpr_avg_last3', 'toprate_rating'))
