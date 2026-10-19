"""The locked rule (exact, real TopRate columns, 26 Apr - 8 Oct 2026 only) and a 2019+ proxy rule built from as-of results data."""
import os, sys
sys.path.insert(0, os.path.dirname(__file__))
import numpy as np, pandas as pd
from common import *

MIN_TOP = 3.0


def load_archive():
    """Retired TopRate runner files: the only place TR rating and Mid/Late/Total scores exist (26 Apr - 8 Oct 2026 with results)."""
    a = pd.concat([pd.read_csv(os.path.join(ROOT, 'archive/toprate/toprate_runners_archive.csv.gz'), low_memory=False),
                   pd.read_csv(os.path.join(ROOT, 'archive/toprate/toprate_runners.csv'), low_memory=False)])
    a = a.drop_duplicates('run_id', keep='last')
    a = a[(a['date'] <= '2026-10-08') & a['finish_position'].notna() & (a['finish_position'] > 0)].copy()
    a['win'] = (a['finish_position'] == 1).astype(int)
    nw = a.groupby('race_id')['win'].transform('sum')
    a = a[nw == 1].copy()
    for src, dst in (('toprate_rating', 'tr_rank'), ('mid_speed_score', 'mid_rank'), ('late_speed_score', 'late_rank'), ('total_speed_score', 'total_rank')):
        a[dst] = a.groupby('race_id')[src].rank(ascending=False, method='min')
    a['has_first_starter'] = a.get('has_first_starter', 0)
    return a


def locked_rule_real(a, tr=3, sect=2, min_top=MIN_TOP):
    """TR<=3 AND Mid<=2 AND Late<=2 AND Total<=2 AND Top price >= $3, fixed-odds win at the Top price."""
    m = (a['tr_rank'] <= tr) & (a['mid_rank'] <= sect) & (a['late_rank'] <= sect) & (a['total_rank'] <= sect) & (a['price_top'] >= min_top)
    return a[m]


def proxy_ranks(D):
    D['p_tr_rank'] = D.groupby('race_id')['wpr_m3'].rank(ascending=False, method='min')
    D['p_mid_rank'] = D.groupby('race_id')['sect_i_400_200_m5'].rank(ascending=False, method='min')
    D['p_late_rank'] = D.groupby('race_id')['sect_i_l200_m5'].rank(ascending=False, method='min')
    D['p_total_rank'] = D.groupby('race_id')['sect_i_l600_m5'].rank(ascending=False, method='min')
    return D


def proxy_rule(D, tr=3, sect=2, min_top=MIN_TOP):
    m = (D['p_tr_rank'] <= tr) & (D['p_mid_rank'] <= sect) & (D['p_late_rank'] <= sect) & (D['p_total_rank'] <= sect) & (D['price_top'] >= min_top)
    return D[m]
