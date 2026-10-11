"""Features for the market-residual win model (see betsignal/README.md).

Two code paths that must agree:
  batch_features(D)            reference implementation, used for training (every row's features use strictly earlier rows).
  build_state(D) + serve_features(U, state)   fast path for upcoming runners: per-horse and per-jockey/trainer state as of the
                                              end of the history, then the same features for the new rows.
betsignal/check_equivalence.py proves they match on a held-out stretch of history.
"""
import glob
import os
import re

import numpy as np
import pandas as pd

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

USECOLS = ['race_id', 'date', 'raceNumber', 'track', 'horse_id', 'jockey', 'trainer', 'field_size', 'distance', 'going', 'wpr',
           'weightCarried', 'barrier', 'priceStarting', 'positionFinish', 'marginFinish', 'horse_age', 'horse_sex', 'race_class',
           'isBarrierTrial', 'is_jumpout']

# Order matters: the saved model is fitted on exactly these columns.
FEATURES = ['field_size', 'distance', 'going_n', 'weightCarried', 'wt_rel', 'barrier', 'bar_rel', 'horse_age', 'sex', 'cls', 'trk',
            'nruns', 'w1', 'w2', 'w3', 'wavg3', 'wbest', 'wavg_all', 'wavg3_rel', 'wavg3_mean', 'days', 'pwin', 'lastfin', 'lastmarg',
            'lastpm', 'avgpm', 'last_res_vs_mkt', 'dist_ch', 'wt_ch', 'j_wr', 'j_n', 'j_ex', 't_wr', 't_n', 't_ex', 'rank_m']

JT_PRIOR_RATE, JT_PRIOR_N, JT_EX_K = 0.08, 20, 30
ASSUME_GOING = 4.0

_CLASS_PATTERNS = [(re.compile(r'^benchmark\s*(\d+)$', re.I), lambda m: f'BM{m.group(1)}'),
                   (re.compile(r'^class\s*(\d+)$', re.I), lambda m: f'CLS{m.group(1)}'),
                   (re.compile(r'^maiden$', re.I), lambda m: 'MAI'),
                   (re.compile(r'^open$', re.I), lambda m: 'OPEN')]


def norm_class(s):
    """Live runner file says 'Benchmark 58' / 'Class 2' / 'Maiden' / 'Open'; the results files say BM58 / CLS2 / MAI / OPEN."""
    if s is None or (isinstance(s, float) and np.isnan(s)):
        return np.nan
    s = str(s).strip()
    for pat, fn in _CLASS_PATTERNS:
        m = pat.match(s)
        if m:
            return fn(m)
    return s


def going_number(s):
    m = re.search(r'(\d+)', str(s))
    return float(m.group(1)) if m else np.nan


def load_history(root=ROOT):
    """All complete, priced, non-trial races from the results files (2018-06 on), sorted. Same filters the research used."""
    files = sorted(glob.glob(os.path.join(root, 'race_results_20*.csv.gz')))
    D = pd.concat([pd.read_csv(f, usecols=lambda c: c in USECOLS, low_memory=False) for f in files]).drop_duplicates(['race_id', 'horse_id'])
    D = D[(D.isBarrierTrial != True) & (D.is_jumpout != True) & (D.field_size >= 5)].drop(columns=['isBarrierTrial', 'is_jumpout']).copy()
    D['date'] = pd.to_datetime(D.date)
    D['fin'] = pd.to_numeric(D.positionFinish, errors='coerce')
    D['win'] = (D.fin == 1).astype(int)
    D['sp'] = D.priceStarting.where(D.priceStarting > 1)
    g = D.groupby('race_id')
    ok = g.sp.apply(lambda s: s.notna().all()) & g.win.sum().eq(1) & g.fin.apply(lambda s: s.notna().all())
    D = D[D.race_id.isin(ok[ok].index)]
    D = D[D.date >= '2018-06-01'].copy()
    return D.sort_values(['date', 'track', 'raceNumber', 'race_id']).reset_index(drop=True)


def categories(D):
    """Fixed code books so training and serving agree. Unknown values code as -1."""
    return {'sex': sorted(D.horse_sex.dropna().astype(str).unique()),
            'cls': sorted(D.race_class.dropna().astype(str).unique()),
            'trk': sorted(D.track.dropna().astype(str).unique())}


def _code(series, book):
    return pd.Categorical(series.astype('object').where(series.notna(), None).astype(object), categories=book).codes.astype(float)


def _market(D):
    D['imp'] = 1 / D.sp
    D['pm'] = D.imp / D.groupby('race_id').imp.transform('sum')
    D['rank_m'] = D.groupby('race_id').sp.rank(method='min')
    return D


def _static(D, cats):
    D['going_n'] = D.going.map(going_number)
    D['sex'] = _code(D.horse_sex, cats['sex'])
    D['cls'] = _code(D.race_class, cats['cls'])
    D['trk'] = _code(D.track, cats['trk'])
    # A horse with no earlier run has no age or sex in the live files, so the model is trained to see them blank too.
    D.loc[D.nruns == 0, ['horse_age', 'sex']] = [np.nan, -1.0]
    r = D.groupby('race_id')
    D['wt_rel'] = D.weightCarried - r.weightCarried.transform('mean')
    D['bar_rel'] = D.barrier / D.field_size
    return D


def _relative(D):
    r = D.groupby('race_id')
    D['wavg3_rel'] = D.wavg3 - r.wavg3.transform('max')
    D['wavg3_mean'] = D.wavg3 - r.wavg3.transform('mean')
    return D


def batch_features(D, cats):
    """Reference implementation. D needs the load_history columns; outcome columns may be NaN for rows to be predicted."""
    D = D.sort_values(['horse_id', 'date', 'raceNumber']).copy()
    D = _market(D)
    h = D.groupby('horse_id')
    D['nruns'] = h.cumcount()
    for k in (1, 2, 3):
        D[f'w{k}'] = h.wpr.shift(k)
    D['wavg3'] = D[['w1', 'w2', 'w3']].mean(axis=1)
    D['wbest'] = h.wpr.transform(lambda s: s.shift(1).expanding().max())
    D['wavg_all'] = h.wpr.transform(lambda s: s.shift(1).expanding().mean())
    D['days'] = (D.date - h.date.shift(1)).dt.days
    D['pwin'] = h.win.transform(lambda s: s.shift(1).expanding().mean())
    D['lastfin'] = h.fin.shift(1)
    D['lastmarg'] = h.marginFinish.shift(1)
    D['lastpm'] = h.pm.shift(1)
    D['avgpm'] = h.pm.transform(lambda s: s.shift(1).expanding().mean())
    D['last_res_vs_mkt'] = h.win.shift(1) - D.lastpm
    D['dist_ch'] = D.distance - h.distance.shift(1)
    D['wt_ch'] = D.weightCarried - h.weightCarried.shift(1)
    D['_ex'] = D.win - D.pm
    for key, name in (('jockey', 'j'), ('trainer', 't')):
        d = D.groupby([key, 'date']).agg(w=('win', 'sum'), n=('win', 'size'), e=('_ex', 'sum')).reset_index().sort_values([key, 'date'])
        for c in ('w', 'n', 'e'):
            d['c' + c] = d.groupby(key)[c].cumsum() - d[c]
        d[f'{name}_wr'] = (d.cw + JT_PRIOR_RATE * JT_PRIOR_N) / (d.cn + JT_PRIOR_N)
        d[f'{name}_n'] = d.cn
        d[f'{name}_ex'] = d.ce / (d.cn + JT_EX_K)
        D = D.merge(d[[key, 'date', f'{name}_wr', f'{name}_n', f'{name}_ex']], on=[key, 'date'], how='left')
    D = _static(D, cats)
    D = _relative(D)
    D['year'] = D.date.dt.year
    return D.sort_values(['date', 'race_id']).reset_index(drop=True)


# ---------------------------------------------------------------- state-based serving path
def build_state(D):
    """State as of the END of D (D must be sorted by date; features are computed for rows after D's last date)."""
    D = D.sort_values(['horse_id', 'date', 'raceNumber'])
    D = _market(D.copy())
    g = D.groupby('horse_id')
    last3 = g.wpr.apply(lambda s: list(s.iloc[-3:][::-1].values) + [np.nan] * (3 - min(3, len(s))))
    hs = pd.DataFrame({
        'n': g.size(),
        'w1': last3.map(lambda v: v[0]), 'w2': last3.map(lambda v: v[1]), 'w3': last3.map(lambda v: v[2]),
        'w_sum': g.wpr.sum(), 'w_cnt': g.wpr.count(), 'w_max': g.wpr.max(),
        'win_sum': g.win.sum(), 'pm_sum': g.pm.sum(), 'pm_cnt': g.pm.count(),
        'last_date': g.date.last(), 'last_fin': g.fin.last(), 'last_marg': g.marginFinish.last(), 'last_pm': g.pm.last(),
        'last_win': g.win.last(), 'last_dist': g.distance.last(), 'last_wt': g.weightCarried.last(),
        'last_age': g.horse_age.last(), 'last_sex': g.horse_sex.last()})
    D['_ex'] = D.win - D.pm
    js = {}
    for key in ('jockey', 'trainer'):
        a = D.groupby(key).agg(w=('win', 'sum'), n=('win', 'size'), e=('_ex', 'sum'))
        js[key] = a
    return {'horse': hs, 'jockey': js['jockey'], 'trainer': js['trainer'], 'through': D.date.max()}


def age_now(last_age, last_date, target_date):
    """Australian racing ages turn over on 1 August."""
    if pd.isna(last_age) or pd.isna(last_date):
        return np.nan
    last_date, target_date = pd.Timestamp(last_date), pd.Timestamp(target_date)
    def aug1s(d):
        y = d.year
        return y if d >= pd.Timestamp(y, 8, 1) else y - 1
    return float(last_age) + (aug1s(target_date) - aug1s(last_date))


def serve_features(U, state, cats):
    """U: one row per runner to score. Required: race_id, date, track, horse_id, jockey, trainer, field_size, distance, going,
    weightCarried, barrier, race_class, sp (the price to be judged against). Returns U with FEATURES filled in."""
    U = U.copy()
    U['date'] = pd.to_datetime(U.date)
    U = _market(U)
    hs = state['horse']
    S = hs.reindex(U.horse_id.values)
    S.index = U.index
    U['nruns'] = S.n.fillna(0).values
    for k in (1, 2, 3):
        U[f'w{k}'] = S[f'w{k}'].values
    U['wavg3'] = U[['w1', 'w2', 'w3']].mean(axis=1)
    U['wbest'] = S.w_max.values
    U['wavg_all'] = (S.w_sum / S.w_cnt.where(S.w_cnt > 0)).values
    U['days'] = (U.date - S.last_date).dt.days.values
    U['pwin'] = (S.win_sum / S.n.where(S.n > 0)).values
    U['lastfin'] = S.last_fin.values
    U['lastmarg'] = S.last_marg.values
    U['lastpm'] = S.last_pm.values
    U['avgpm'] = (S.pm_sum / S.pm_cnt.where(S.pm_cnt > 0)).values
    U['last_res_vs_mkt'] = (S.last_win - S.last_pm).values
    U['dist_ch'] = (U.distance - S.last_dist).values
    U['wt_ch'] = (U.weightCarried - S.last_wt).values
    # age and sex come from the horse's last run when the live file does not carry them
    if 'horse_age' not in U or U.horse_age.isna().all():
        U['horse_age'] = [age_now(a, d, t) for a, d, t in zip(S.last_age.values, S.last_date.values, U.date.values)]
    if 'horse_sex' not in U or U.horse_sex.isna().all():
        U['horse_sex'] = S.last_sex.values
    for key, name in (('jockey', 'j'), ('trainer', 't')):
        a = state[key].reindex(U[key].values)
        a.index = U.index
        cn = a.n.fillna(0)
        cw = a.w.fillna(0)
        ce = a.e.fillna(0)
        known = U[key].notna()
        U[f'{name}_wr'] = np.where(known, (cw + JT_PRIOR_RATE * JT_PRIOR_N) / (cn + JT_PRIOR_N), np.nan)
        U[f'{name}_n'] = np.where(known, cn, np.nan)
        U[f'{name}_ex'] = np.where(known, ce / (cn + JT_EX_K), np.nan)
    U = _static(U, cats)
    U = _relative(U)
    return U
