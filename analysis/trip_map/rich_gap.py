"""Richer early-position (gap behind the leader at 800m) forecast, shared by the daily trip map build and research/trip_model_study.py.

Built from the results files only (every track). Features: track x distance cell, barrier, field size, rail, going, the horse's own
earlier early positions (last 1/3/8, at this distance band and at this track), run-style spread, days since run, jockey early tendency
(lagged a day), weight and class, and the rival profile of the field (likely leaders, tempo, own rank). Strictly pre-race.
Held out (2025-07 on, fields of 8+): within-race correlation with the real 800m gap 0.569 vs 0.541 for the base set the trip map used
before, better in 132 of 135 track x distance cells with 300+ runs (see research/trip_model_study.py).

`rerank(races, up, today)` keeps every race's placed gap values (the spread of a real field) and re-assigns them to the runners in the
rich model's order, so only the ORDER of the forecast changes.
"""
import glob
import os

import lightgbm as lgb
import numpy as np
import pandas as pd

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..'))
PARAMS = dict(objective='regression', learning_rate=0.05, num_leaves=63, min_data_in_leaf=200, feature_fraction=0.8,
              bagging_fraction=0.8, bagging_freq=1, verbose=-1, num_threads=4)
LIVE_ROUNDS = 230   # best iteration on the held-out check was 215 to 260


def load():
    cols = ['race_id', 'horse_id', 'date', 'track', 'distance', 'going', 'barrier', 'field_size', 'position800m', 'margin800m',
            'rail_position', 'wpr', 'isBarrierTrial', 'is_jumpout', 'positionFinish', 'priceStarting', 'jockey', 'weightCarried',
            'race_class', 'horse_age', 'horse_sex', 'raceNumber']
    fs = [f for f in sorted(glob.glob(os.path.join(ROOT, 'race_results_20*.csv.gz'))) if not f.endswith('_rc.csv.gz')]
    d = pd.concat([pd.read_csv(f, usecols=lambda c: c in set(cols), low_memory=False) for f in fs], ignore_index=True)
    d = d[(~d.isBarrierTrial.astype(bool)) & (~d.is_jumpout.fillna(False).astype(bool))].copy()
    d = d[~d.race_class.astype(str).str.contains('Hurdle|Steeple', case=False, na=False)]
    d = d.drop_duplicates(['race_id', 'horse_id'])
    d['date'] = pd.to_datetime(d.date)
    d = d[(d.field_size >= 5) & (d.barrier > 0)].copy()
    d['fs'] = d.field_size
    d['barfrac'] = (d.barrier - 1) / (d.fs - 1).clip(lower=1)
    d['settle'] = (d.position800m - 1) / (d.fs - 1).clip(lower=1)
    d['gap800'] = d.margin800m.clip(0, 30)
    s = d.rail_position.astype(str)
    d['rail_m'] = np.where(s.str.contains('True'), 0.0, pd.to_numeric(s.str.extract(r'(\d+)\s*m')[0], errors='coerce'))
    d['going_s'] = pd.to_numeric(d.going.astype(str).str.extract(r'(\d+)')[0], errors='coerce')
    d['band'] = pd.cut(d.distance, [0, 1150, 1450, 1850, 2300, 9999], labels=False)
    d['trk'] = d.track.astype('category')
    d['cell'] = (d.track.astype(str) + '|' + d.distance.astype(str)).astype('category')
    d['cls'] = d.race_class.astype('category')
    d['sex'] = d.horse_sex.astype('category')
    d['jock'] = d.jockey.astype(str)
    return d.sort_values(['horse_id', 'date', 'race_id']).reset_index(drop=True)


def lagmean(g, col, k_max, min_n, k_min=1):
    """Mean of the previous k_min..k_max values of col within horse (NaN skipped)."""
    arr = np.column_stack([g[col].shift(k) for k in range(k_min, k_max + 1)])
    n = np.isfinite(arr).sum(1)
    with np.errstate(all='ignore'):
        m = np.nanmean(arr, 1)
    m[n < min_n] = np.nan
    return m


def add_features(d):
    g = d.groupby('horse_id')
    for t in ('settle', 'gap800'):
        d[t + '_l1'] = g[t].shift(1)
        d[t + '_h3'] = lagmean(g, t, 3, 1)
        d[t + '_h8'] = lagmean(g, t, 8, 2)
    arr = np.column_stack([g['settle'].shift(k) for k in range(1, 9)])
    with np.errstate(all='ignore'):
        d['settle_sd8'] = np.where(np.isfinite(arr).sum(1) >= 3, np.nanstd(arr, 1), np.nan)
    d['n_hist'] = g.cumcount()
    d['days'] = (d.date - g.date.shift(1)).dt.days
    # horse's earlier runs at this distance band, and at this track (expanding, excludes the run itself)
    for key, nm in (('band', 'band'), ('track', 'trk')):
        gg = d.groupby(['horse_id', key])
        x = d.settle
        ok = x.notna()
        cs = x.fillna(0).groupby([d.horse_id, d[key]]).cumsum() - x.fillna(0)
        cn = ok.groupby([d.horse_id, d[key]]).cumsum() - ok.astype(int)
        d['settle_' + nm + '_h'] = np.where(cn >= 1, cs / cn.replace(0, np.nan), np.nan)
        d['n_' + nm + '_h'] = cn
    d['wpr_l1'] = g.wpr.shift(1)
    d['r3'] = lagmean(g, 'wpr', 3, 2)
    d['wt_chg'] = d.weightCarried - g.weightCarried.shift(1)
    # jockey early tendency: how far the jockey's mounts settle ahead of their own horses' usual position, as of the day before
    # (cumulative to the last day the jockey had a measured ride before this row's date, so an upcoming row gets a value too)
    resid = (d.settle - d.settle_h8)
    jd = pd.DataFrame({'jock': d.jock, 'date': d.date, 'r': resid}).dropna()
    ja = jd.groupby(['jock', 'date']).r.agg(['sum', 'count']).reset_index().sort_values(['jock', 'date'])
    ja['cum_s'] = ja.groupby('jock')['sum'].cumsum()
    ja['cum_n'] = ja.groupby('jock')['count'].cumsum()
    key = d[['jock', 'date']].copy()
    key['_i'] = np.arange(len(d))
    m = pd.merge_asof(key.sort_values('date'), ja[['jock', 'date', 'cum_s', 'cum_n']].sort_values('date'), on='date', by='jock',
                      allow_exact_matches=False, direction='backward').sort_values('_i')
    d['jock_early'] = (m.cum_s / (m.cum_n + 30)).values
    d['jock_n'] = m.cum_n.values
    # rivals: leaders in the field, field tempo, own rank
    r = d.groupby('race_id')
    d['own_rel'] = d.settle_h3 - r.settle_h3.transform('mean')
    d['n_lead3'] = (d.settle_h3 <= 0.25).groupby(d.race_id).transform('sum')
    d['n_lead8'] = (d.settle_h8 <= 0.25).groupby(d.race_id).transform('sum')
    d['tempo_gap'] = r.gap800_h3.transform('mean')
    d['tempo_set'] = r.settle_h3.transform('mean')
    d['own_rank'] = r.settle_h3.rank(method='min')
    d['rank_frac'] = d.own_rank / r.settle_h3.transform('count').clip(lower=1)
    d['field_known'] = r.settle_h3.transform('count') / d.fs
    d['bar_x_lead'] = d.barfrac * d.n_lead3
    d['wt_rel'] = d.weightCarried - r.weightCarried.transform('mean')
    d['r3_rel'] = d.r3 - r.r3.transform('mean')
    return d


BASE = ['trk', 'distance', 'barrier', 'barfrac', 'fs', 'rail_m', 'going_s',
        'settle_h3', 'settle_h8', 'gap800_h3', 'gap800_h8', 'own_rel', 'n_lead3']
RICH = BASE + ['cell', 'band', 'settle_l1', 'gap800_l1', 'settle_sd8', 'n_hist', 'days', 'settle_band_h', 'n_band_h', 'settle_trk_h', 'n_trk_h',
               'jock_early', 'jock_n', 'n_lead8', 'tempo_gap', 'tempo_set', 'own_rank', 'rank_frac', 'field_known', 'bar_x_lead',
               'weightCarried', 'wt_chg', 'wt_rel', 'cls', 'horse_age', 'sex', 'wpr_l1', 'r3_rel']




# ---------------------------------------------------------------- live path
def upcoming_frame(up):
    """Rows for the upcoming runners in the same columns load() gives (barrier, field size, rail, going, jockey, weight, class, age, sex)."""
    u = pd.DataFrame({
        'race_id': 'U' + up.race_id.astype(str).values, 'horse_id': up.horse_id.values, 'date': pd.to_datetime(up.date).values,
        'track': up.track.values, 'distance': up.distance.values, 'going': up.going.values, 'barrier': up.barrier.values, 'fs': up.fs.values,
        'barfrac': up.barfrac.values, 'rail_m': up.rail_m.values, 'going_s': up.going_s.values,
        'jockey': up.jockey.values if 'jockey' in up else None, 'weightCarried': up.weight_carried.values if 'weight_carried' in up else np.nan,
        'race_class': up.race_class.values if 'race_class' in up else None, 'horse_age': up.horse_age.values if 'horse_age' in up else np.nan,
        'horse_sex': up.horse_sex.values if 'horse_sex' in up else None, 'run_id': up.run_id.values})
    u['jock'] = u.jockey.astype(str)
    u['band'] = pd.cut(u.distance, [0, 1150, 1450, 1850, 2300, 9999], labels=False)
    for c in ('position800m', 'margin800m', 'wpr', 'settle', 'gap800', 'positionFinish', 'priceStarting'):
        u[c] = np.nan
    return u


def predict_upcoming(up, today, rounds=LIVE_ROUNDS):
    """Rich gap forecast (lengths behind the leader at 800m, raw model output) for each upcoming runner: {run_id (str): value}."""
    h = load()
    h = h[(h.date < today) & (h.date >= '2018-01-01')].copy()
    h['race_id'] = h.race_id.astype(str)
    u = upcoming_frame(up)
    u = u[u.track.notna() & u.horse_id.notna()]
    keep = [c for c in h.columns if c in u.columns or c in ('trk', 'cell', 'cls', 'sex')]
    comb = pd.concat([h[[c for c in h.columns if c in u.columns]].assign(_up=0), u[[c for c in h.columns if c in u.columns]].assign(_up=1, run_id=u.run_id.values)],
                     ignore_index=True)
    for col, src in (('trk', 'track'), ('cell', None), ('cls', 'race_class'), ('sex', 'horse_sex')):
        v = (comb.track.astype(str) + '|' + comb.distance.astype(str)) if col == 'cell' else comb[src].astype(str)
        comb[col] = v.astype('category')
    comb = comb.sort_values(['horse_id', 'date', 'race_id'], kind='stable').reset_index(drop=True)
    comb = add_features(comb)
    tr = comb[(comb._up == 0) & comb.gap800.notna()]
    mdl = lgb.train(PARAMS, lgb.Dataset(tr[RICH], tr.gap800), rounds)
    pu = comb[comb._up == 1]
    return dict(zip(pu.run_id.astype('int64').astype(str), mdl.predict(pu[RICH])))


def rerank(races, pred, min_cover=0.8):
    """In each race put the already-placed gap values in the rich model's order. Returns how many races were reordered."""
    n = 0
    for rid, race in races.items():
        rs = [r for r in race['runners'] if r.get('gap') is not None]
        have = [r for r in rs if r['rid'] in pred]
        if len(rs) < 5 or len(have) < min_cover * len(rs):
            continue
        order = sorted(have, key=lambda r: pred[r['rid']])
        vals = sorted(r['gap'] for r in have)
        changed = False
        for r, v in zip(order, vals):
            if r['gap'] != v:
                r['gap'] = v
                changed = True
        # runners with no forecast keep their own value; the front of the field stays at 0
        m = min(r['gap'] for r in rs)
        if m:
            for r in rs:
                r['gap'] = round(r['gap'] - m, 1)
        n += changed
    return n
