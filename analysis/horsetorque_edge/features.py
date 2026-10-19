"""As-of feature build for the Horsetorque Edge tests. Every feature for a run uses only that horse's EARLIER runs
(strictly before the run's date) plus facts declared before the race (weight, barrier, distance, class, field size).
The only post-race quantities (XR, TOF, settle position) are used as history for the horse's NEXT start.
"""
import os, sys
sys.path.insert(0, os.path.dirname(__file__))
import numpy as np, pandas as pd
from common import *
from class_par import add_class_par

LEN_TO_SEC = 0.147        # repo-measured: 1 length ~ 0.147 s (research/speed_style_study.py notes in CLAUDE.md)
PTS_PER_SEC = 10.0        # owner spec: +/-1 rating point per 0.1 s vs the winner's last 400m
ALT_PTS_PER_LEN = 2.15    # the repo's own within-race rating-per-length slope (CLAUDE.md, Spd scale), used as a sensitivity


def old_rung(rc):
    """Class rung used by the retired wpr_projection.py (archive/toprate/wpr_projection.py _class_rung), for comparison."""
    fixed = {"MAI": 5, "MAIH": 5, "MAIS": 5, "NOV": 8, "R0MW": 10, "R1MW": 10, "R0MWLY": 10, "R1MWLY": 10, "R0MWL2Y": 10, "R1MWL2Y": 10,
             "CLSA": 50, "CLSB": 50, "CLS1": 55, "CLS2": 58, "CLS3": 62, "CLS4": 66, "CLS5": 70, "CLS6": 74, "REST": 58, "OPEN": 105}
    c = str(rc).strip().upper()
    if c in fixed: return fixed[c]
    import re
    m = re.match(r'^(BM|RST)(\d+)', c)
    return int(m.group(2)) if m else np.nan


def _class_move_peak(df, par_col, out_prefix):
    """class_move = today's rung - mean rung of last 5 earlier runs; peak_at_class = best earlier wpr at or below today's rung."""
    g = df['horse_id'].values
    par = df[par_col].values.astype(float)
    wpr = df['wpr'].values.astype(float)
    n = len(df)
    recent = asof_mean(df, par_col, 5)
    peak = np.full(n, np.nan)
    peak_any = np.full(n, np.nan)
    starts = np.r_[0, np.flatnonzero(g[1:] != g[:-1]) + 1, n]
    for s, e in zip(starts[:-1], starts[1:]):
        if e - s < 2: continue
        w = wpr[s:e]; p = par[s:e]
        for i in range(1, e - s):
            pw = w[:i]; pp = p[:i]
            ok = ~np.isnan(pw)
            if not ok.any(): continue
            peak_any[s + i] = pw[ok].max()
            m = ok & (pp <= p[i]) if not np.isnan(p[i]) else ok
            if m.any(): peak[s + i] = pw[m].max()
    df[f'{out_prefix}_class_move'] = np.where(np.isnan(par) | np.isnan(recent), 0.0, par - recent)
    df[f'{out_prefix}_peak_at_class'] = np.where(np.isnan(peak), peak_any, peak)
    return df


def build(refresh=False):
    path = os.path.join(CACHE, 'features.pkl')
    if os.path.exists(path) and not refresh:
        return pd.read_pickle(path)
    D = load_runs().copy()
    D = add_class_par(D)
    D['rung_old'] = D['race_class'].map(old_rung)
    D['tg'] = pd.to_numeric(D['trackGrading'], errors='coerce')     # the buggy "class" (this is the going number)

    # ---- test 1: class features three ways (trackGrading bug, retired rung ladder, new class_par)
    for par_col, pre in (('tg', 'tg'), ('rung_old', 'rung'), ('class_par', 'cp')):
        D = _class_move_peak(D, par_col, pre)
    D['sr_vs_par'] = D['wpr'] - D['class_par']                                   # post-race, history only
    D['sr_vs_par_m3'] = asof_mean(D, 'sr_vs_par', 3)
    D['sr_vs_par_last'] = asof_last(D, 'sr_vs_par')

    # ---- test 2: winner-anchored sectional rating XR and TOF (post-race, used as history)
    win = D['win'] == 1
    for c in ('wpr', 'sect_i_l400'):
        D[f'w_{c}'] = D[c].where(win).groupby(D['race_id']).transform('max')
    dl = (D['sect_i_l400'] - D['w_sect_i_l400']).clip(-15, 15)                   # lengths; <0 = slower than the winner home (clip: sect values hold +-100 data errors)
    D['XR'] = D['w_wpr'] + dl * LEN_TO_SEC * PTS_PER_SEC
    D['XR_alt'] = D['w_wpr'] + dl * ALT_PTS_PER_LEN
    D['TOF'] = D['XR'] - D['wpr']
    D['TOF_alt'] = D['XR_alt'] - D['wpr']
    for c in ('XR', 'TOF', 'TOF_alt'):
        D[f'{c}_m3'] = asof_mean(D, c, 3)
        D[f'{c}_last'] = asof_last(D, c)
    D['tof_rank'] = D.groupby('race_id')['TOF_m3'].rank(ascending=False, method='min')
    D['tof_rank_pct'] = (D['tof_rank'] - 1) / (D['field_size'] - 1).clip(lower=1)

    # ---- settle position (position800m is the earliest call that is populated; positionSettled is blank everywhere)
    D['settle'] = D['position800m'].where(D['position800m'] > 0)
    D['settle_pct'] = ((D['settle'] - 1) / (D['field_size'] - 1).clip(lower=1)).clip(0, 1)
    D['rear_third'] = (D['settle_pct'] > 2 / 3).astype(float).where(D['settle'].notna())
    D['settle_last'] = asof_last(D, 'settle_pct')
    D['rear_last'] = asof_last(D, 'rear_third')
    D['settle_m3'] = asof_mean(D, 'settle_pct', 3)
    D['settle_m3_pos'] = asof_mean(D, 'settle', 3)

    # ---- rating history
    for k in (1, 3, 5):
        D[f'wpr_m{k}'] = asof_mean(D, 'wpr', k)
    D['wpr_m8'] = asof_mean(D, 'wpr', 8)
    D['wpr_best'] = D.groupby('horse_id')['wpr'].transform(lambda s: s.shift(1).expanding().max())
    D['n_prior'] = D.groupby('horse_id').cumcount()
    D['days_since'] = D.groupby('horse_id')['dt'].diff().dt.days
    D['w_carried'] = pd.to_numeric(D['weightCarried'], errors='coerce')
    D['w_prev'] = asof_last(D, 'w_carried')
    D['dist_prev'] = asof_last(D, 'distance')
    D['w_up'] = (D['w_carried'] - D['w_prev'])
    D['d_up'] = (D['distance'] - D['dist_prev'])
    D['tof_prev'] = D['TOF_last']

    # ---- proxies for the TopRate Mid / Late / Total speed scores (partial; see calibrate_proxy.py)
    for c in ('sect_i_400_200', 'sect_i_l200', 'sect_i_l600', 'sect_i_time', 'sect_i_early'):
        D[f'{c}_m5'] = asof_mean(D, c, 5)
    D['dt_year'] = D['dt'].dt.year
    D.to_pickle(path)
    return D


if __name__ == '__main__':
    import time
    t = time.time(); D = build(refresh=True); print(D.shape, round(time.time() - t), 's')
    print(D[['class_par', 'rung_old', 'tg', 'cp_class_move', 'cp_peak_at_class', 'XR', 'TOF', 'TOF_m3', 'settle_pct', 'rear_third', 'wpr_m3']].describe().T.round(2).to_string())
    print('class_par coverage', D.class_par.notna().mean().round(4), ' unmapped classes:', D[D.class_par.isna()].race_class.value_counts().head(10).to_dict())
