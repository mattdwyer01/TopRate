"""Trip map for tracks WITHOUT GPS (NSW, WA, TAS, ACT, NT and any VIC/SA/QLD course with no GPS history).

GPS gives measured width and extra ground, which these tracks lack. What every track has, from race_results_*.csv.gz, is each run's
position and margin at 800m. So:
  gap   - forecast from track, distance, going, rail, barrier, field size and the horse's last 3 / 8 results-based settle and gap at 800m
          (same model family and spread-template placing as the GPS states; trained on every track's runs, scored on non-GPS tracks).
  width - NOT measured. Estimated from barrier, field size, rail, predicted settle and own settle history, by a small model fitted on the
          QLD runs (width at 800m). This is an estimate of the running line, not a measurement; the file marks it laneKind='est'.

Used by build_trip_map.py (main calls build()); `python analysis/trip_map/nongps.py` runs the held-out check alone.
"""
import os
import sys

import lightgbm as lgb
import numpy as np
import pandas as pd

sys.path.insert(0, os.path.dirname(__file__))
import build_trip_map as B  # noqa: E402

NT = ['gap800', 'settle']
BASE = ['trk', 'distance', 'barrier', 'barfrac', 'fs', 'rail_m', 'going_s']
HIST = [t + s for t in NT for s in ('_h3', '_h8')] + ['n_lead', 'own_rel']
FEATS = BASE + HIST
LANE_FEATS = ['distance', 'barrier', 'barfrac', 'fs', 'rail_m', 'going_s', 'settle_h3', 'gap800_h3', 'own_rel', 'n_lead', 'pred_gap', 'pred_settle']


def add_hist(a):
    a = a.sort_values(['horse_id', 'date', 'race_id']).reset_index(drop=True)
    g = a.groupby('horse_id')
    for t in NT:
        a[t + '_h3'] = g[t].transform(lambda s: s.shift(1).rolling(3, min_periods=1).mean())
        a[t + '_h8'] = g[t].transform(lambda s: s.shift(1).rolling(8, min_periods=2).mean())
    a['n_lead'] = a.groupby('race_id').settle_h3.transform(lambda s: (s <= 0.25).sum())
    a['own_rel'] = a.settle_h3 - a.groupby('race_id').settle_h3.transform('mean')
    a['n_hist'] = g.cumcount()
    return a


def result_runs(res):
    d = B.add_result_features(res)
    d = d[d.position800m.notna() & d.margin800m.notna() & (d.fs >= 5) & (d.field_size.notna())].copy()
    d['race_id'] = d.race_id.astype(str)
    return d[['race_id', 'horse_id', 'date', 'track', 'distance', 'barrier', 'barfrac', 'fs', 'rail_m', 'going_s', 'settle', 'gap800']]


def fit(train):
    train = train.copy()
    train['band'] = B.dist_band(train.distance)
    train['fsb'] = B.fs_band(train.fs)
    m = lgb.train(B.PARAMS, lgb.Dataset(train[FEATS], train.gap800), B.ROUNDS)
    ms = lgb.train(B.PARAMS, lgb.Dataset(train[FEATS], train.settle), B.ROUNDS)
    tab = {(int(b), int(f)): np.quantile(z.gap800, B.Q) for (b, f), z in train.groupby(['band', 'fsb']) if len(z) > 200}
    return m, ms, tab


def place(df, m, ms, tab):
    out = df.copy()
    out['raw_gap'] = m.predict(out[FEATS])
    out['pred_settle'] = ms.predict(out[FEATS])
    out['pred_gap'] = out.raw_gap
    out['band'] = B.dist_band(out.distance)
    out['fsb'] = B.fs_band(out.fs)
    g = out.groupby('race_id')
    out['p_gap'] = (g.raw_gap.rank(method='first') - 0.5) / g.raw_gap.transform('size')
    gap = []
    for r in out.itertuples():
        q = tab.get((int(r.band), int(r.fsb))) if pd.notna(r.band) and pd.notna(r.fsb) else None
        gap.append(np.interp(r.p_gap, B.Q, q) if q is not None else np.nan)
    out['gap'] = gap
    return out


def lane_model(qld_rows):
    """Width at 800m from things every track has. qld_rows needs LANE_FEATS (pred_* from out-of-fold forecasts) and lane."""
    z = qld_rows[qld_rows.lane.notna()]
    return lgb.train(dict(B.PARAMS, min_data_in_leaf=150), lgb.Dataset(z[LANE_FEATS], z.lane), 250)


def build(res, a_gps, TODAY, up, cats_note=None):
    """res: load_results(); a_gps: GPS run table from main (needs QLD rows with 'lane'); up: upcoming-runner frame prepared in main.
    Returns (races dict, err dict)."""
    R = result_runs(res)
    gps_tracks = set(a_gps.track)
    cats = sorted(R.track.unique())
    R['trk'] = pd.Categorical(R.track, categories=cats)
    R = add_hist(R)
    train = R[R.date < TODAY]
    # held-out: train before 2025, score non-GPS tracks 2025+ (fields 8+)
    tr = R[R.date < '2025-01-01']
    te = R[(R.date >= '2025-01-01') & (R.fs >= 8) & (~R.track.isin(gps_tracks))].copy()
    m, ms, tab = fit(tr)
    sc = place(te, m, ms, tab)
    ok = sc.gap.notna()
    yc = te.gap800 - te.groupby('race_id').gap800.transform('mean')
    rawc = sc.raw_gap - sc.groupby('race_id').raw_gap.transform('mean')
    err = dict(gap=round(float(np.sqrt(((sc.gap800 - sc.gap)[ok] ** 2).mean())), 2), gap_corr=round(float(np.corrcoef(rawc[ok], yc[ok])[0, 1]), 2),
               n_races=int(te.race_id.nunique()))
    print('non-GPS held-out 2025+ (gap):', err, flush=True)

    # width estimate: fit on QLD GPS runs using the results-based forecasts (out-of-fold would be cleaner; pred_* here come from a model that
    # trained on earlier years only for the held-out check, and on everything for the live one - the same leak-free split used for gap)
    q = a_gps[(a_gps.state == 'QLD') & a_gps.lane.notna()][['race_id', 'horse_id', 'lane']].copy()
    q['race_id'] = q.race_id.astype(str)
    qd = R.merge(q, on=['race_id', 'horse_id'])
    qd_tr, qd_te = qd[qd.date < '2025-01-01'], qd[qd.date >= '2025-01-01']
    mq, msq, tabq = m, ms, tab  # trained before 2025: out-of-sample for the 2025+ rows, in-sample for earlier ones (acceptable for a width helper)
    for d in (qd_tr, qd_te):
        d['pred_gap'] = mq.predict(d[FEATS])
        d['pred_settle'] = msq.predict(d[FEATS])
    lm = lane_model(qd_tr)
    pl = lm.predict(qd_te[LANE_FEATS])
    yl = qd_te.lane - qd_te.groupby('race_id').lane.transform('mean')
    pw = pd.Series(pl, index=qd_te.index)
    err['lane'] = round(float(np.sqrt(((qd_te.lane - pw) ** 2).mean())), 2)
    err['lane_corr'] = round(float(np.corrcoef(pw - pw.groupby(qd_te.race_id).transform('mean'), yl)[0, 1]), 2)
    print('width estimate vs measured QLD width at 800m (2025+):', {k: err[k] for k in ('lane', 'lane_corr')}, flush=True)

    # live models on everything before today
    m, ms, tab = fit(train)
    qd_all = qd[qd.date < TODAY].copy()
    qd_all['pred_gap'] = m.predict(qd_all[FEATS])
    qd_all['pred_settle'] = ms.predict(qd_all[FEATS])
    lm = lane_model(qd_all)

    races = {}
    u = up[~up.track.isin(gps_tracks)].copy()
    if u.empty:
        return races, err
    u['race_id'] = u.race_id.astype(str)
    hist = R[R.date < TODAY][['race_id', 'horse_id', 'date', 'track'] + NT]
    u2 = u[['race_id', 'horse_id', 'date', 'track']].assign(**{t: np.nan for t in NT})
    comb = pd.concat([hist.assign(_up=0), u2.assign(_up=1)], ignore_index=True)
    comb = add_hist(comb.assign(fs=0, barrier=0, barfrac=0, rail_m=0, going_s=0, distance=0))
    feat = comb[comb._up == 1][['race_id', 'horse_id'] + HIST + ['n_hist']]
    u = u.merge(feat, on=['race_id', 'horse_id'], how='left')
    u['trk'] = pd.Categorical(u.track, categories=cats)
    sc = place(u, m, ms, tab)
    sc['lane'] = np.clip(lm.predict(sc.assign(settle_h3=sc.settle_h3, gap800_h3=sc.gap800_h3)[LANE_FEATS]), 0.3, None)
    last = hist.sort_values('date').drop_duplicates('horse_id', keep='last').set_index('horse_id')
    for rid, z in sc.groupby('race_id'):
        z = z.copy()
        z['gap'] = z.gap - z.gap.min()
        f = z.iloc[0]
        races[str(rid)] = dict(
            venue=f.venue, date=str(f.date.date()), race=int(f.race) if pd.notna(f.race) else None, distance=int(f.distance),
            going=None if pd.isna(f.going) else str(f.going), rail=None if pd.isna(f.rail_position) else str(f.rail_position),
            state='OTHER', laneKind='est', fs=int(len(z)), err=err,
            runners=[dict(rid=str(int(r.run_id)), name=r.horse, barrier=int(r.barrier),
                          gap=None if pd.isna(r.gap) else round(float(r.gap), 1), lane=round(float(r.lane), 1),
                          nHist=int(r.n_hist) if pd.notna(r.n_hist) else 0,
                          last=(dict(date=str(last.loc[r.horse_id, 'date'].date()), track=last.loc[r.horse_id, 'track'], lane=None) if r.horse_id in last.index else None))
                     for r in z.sort_values('barrier').itertuples()])
    return races, err


def main():
    res = B.load_results()
    print('GPS run table ...', flush=True)
    a = pd.concat([B.vicsa_runs(res), B.qld_runs(res)], ignore_index=True)
    TODAY = B.TODAY
    cols = ['date', 'venue', 'state', 'race_id', 'race', 'distance', 'going', 'rail_position', 'run_id', 'horse_id', 'barrier', 'horse', 'scratched']
    up = pd.read_csv(os.path.join(B.ROOT, 'toprate_runners.csv'), usecols=lambda c: c in set(cols), low_memory=False)
    up['date'] = pd.to_datetime(up.date)
    up = up[(up.date >= TODAY) & (up.barrier > 0) & (up.scratched.fillna(0) != 1)].copy()
    up['track'] = up.venue
    up['hn'] = B.clean_name(up.horse)
    name_to_id = res.sort_values('date').drop_duplicates('hn', keep='last').set_index('hn').horse_id.to_dict()
    up['horse_id'] = up.horse_id.fillna(up.hn.map(name_to_id))
    unk = up.horse_id.isna()
    up.loc[unk, 'horse_id'] = -(np.arange(unk.sum()) + 1)
    up['horse_id'] = up.horse_id.astype('int64')
    up['fs'] = up.groupby('race_id').run_id.transform('size')
    up['barfrac'] = (up.barrier - 1) / (up.fs - 1).clip(lower=1)
    up['rail_m'] = B.parse_rail(up.rail_position)
    up['going_s'] = B.parse_going(up.going)
    up = up[up.fs >= 5]
    races, err = build(res, a, TODAY, up)
    print(len(races), 'non-GPS races for', TODAY.date(), err)


if __name__ == '__main__':
    main()
