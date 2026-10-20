"""Can any Horsetorque term improve Spd? Fit on 2025-07..12, score on 2026 (analysis only).
Target = the run's own wpr minus the race mean (as in research/speed_adjusted_rating.py); score = Spd plus fitted terms, all demeaned in race.
Metrics: RMSE on the target, and winner log-likelihood of a softmax over the score (beta fitted on the fit period), paired gain vs Spd alone.
Finding (20 Oct 2026): WPR-free closing gain +0.0118 nats, map +0.0019, class_move -0.0033; terms built from wpr (TOF, XR, sr_vs_par) gain more only because they add L3.
usage: PYTHONPATH=.:research python analysis/horsetorque_edge/spd_improve.py"""
import os, sys
import numpy as np, pandas as pd
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import spd_only
from common import CACHE
from scipy.optimize import minimize_scalar

d = spd_only.build()
from common import asof_mean
F = pd.read_pickle(os.path.join(CACHE, 'features.pkl'))
F['dl400'] = (F['sect_i_l400'] - F['w_sect_i_l400']).clip(-15, 15)      # WPR-free closing gain vs the winner, lengths
F['close400_m3'] = asof_mean(F, 'dl400', 3)
w4 = F['margin400m'].where(F['win'] == 1).groupby(F['race_id']).transform('max')
F['cm400'] = ((F['margin400m'] - w4).clip(-25, 25) - F['marginFinish'].clip(lower=0, upper=25)).clip(-15, 15)   # raw-margin closing gain (no TopRate sect_ columns)
F.loc[w4.isna() | F['margin400m'].isna(), 'cm400'] = np.nan
F['cm400_m3'] = asof_mean(F, 'cm400', 3)
f = F[['race_id', 'horse_id', 'TOF_m3', 'XR_m3', 'sr_vs_par_m3', 'settle_m3', 'close400_m3', 'cm400_m3', 'wpr']].rename(columns={'wpr': 'wpr_t'})
d = d.merge(f, on=['race_id', 'horse_id'], how='left')
d = d[d.wpr_t.notna()].copy()
terms = {'closing gain from raw 400m margins (no WPR, no sect_)': 'cm400_m3', 'closing gain last 400m (sect_i_l400)': 'close400_m3', 'class_move': 'cp_class_move', 'TOF (last-3 mean)': 'TOF_m3', 'XR (last-3 mean)': 'XR_m3', 'last start vs par (sr_vs_par)': 'sr_vs_par_m3', 'map position (settle %)': 'settle_m3'}
need = ['spd'] + list(terms.values())
d = d.dropna(subset=need)
d['n'] = d.groupby('race_id')['race_id'].transform('size')
d = d[d.n >= 5].copy()
for c in need + ['wpr_t']:
    d[c + '_d'] = d[c] - d.groupby('race_id')[c].transform('mean')
fit = d[d.date < '2026-01-01']; te = d[d.date >= '2026-01-01']


def ols(cols):
    X = fit[[c + '_d' for c in cols]].values; y = fit['wpr_t_d'].values
    b = np.linalg.lstsq(X, y, rcond=None)[0]
    return b


def score(df, cols, b):
    return df[[c + '_d' for c in cols]].values @ b


def ll(df, s, beta):
    e = np.exp(beta * s); df = df.assign(_e=e)
    den = df.groupby('race_id')['_e'].transform('sum')
    p = (df['_e'] / den)[df.win == 1]
    return -np.log(p.clip(1e-9)).values


def best_beta(df, s):
    return minimize_scalar(lambda b: ll(df, s, b).mean(), bounds=(0.01, 2), method='bounded').x


rows, base_ll = [], None
for name, cols in [('Spd alone (refit scale)', ['spd'])] + [(f'Spd + {k}', ['spd', v]) for k, v in terms.items()] + [('Spd + all six', ['spd'] + list(terms.values())), ('Spd + the WPR-free three (closing, class_move, map)', ['spd', 'close400_m3', 'cp_class_move', 'settle_m3'])]:
    b = ols(cols)
    sf, st = score(fit, cols, b), score(te, cols, b)
    beta = best_beta(fit, sf)
    l = ll(te, st, beta)
    if base_ll is None: base_ll = l
    rm = np.sqrt(np.mean((te['wpr_t_d'].values - st) ** 2))
    top = te.assign(s=st).groupby('race_id')['s'].transform('max') == st
    wr = te.assign(t=top)[lambda x: x.t].win.mean() * 100
    rows.append(dict(model=name, races=len(l), rmse=rm, winner_ll=-l.mean(), gain_vs_spd=(base_ll - l).mean() if name != 'Spd alone (refit scale)' else np.nan,
                     se=(base_ll - l).std(ddof=1) / np.sqrt(len(l)) if name != 'Spd alone (refit scale)' else np.nan, top_pick_win=wr, coefs=' '.join(f'{x:+.3f}' for x in b)))
r = pd.DataFrame(rows)
print(r.to_string(index=False, float_format=lambda x: f'{x:.4f}'))
