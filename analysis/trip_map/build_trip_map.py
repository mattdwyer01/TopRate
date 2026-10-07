"""Trip map projections for upcoming races at GPS-tracked courses (VIC, SA, QLD).

For every upcoming race with declared barriers at a course that has GPS history, projects where each runner
will be at about 800m from home: gap behind the leader (lengths) and width from the rail (metres).

Method (validated on 2025 races, see analysis/trip_map/README.md):
  1. A gradient-boosted model per state is trained on every GPS-tracked run, using the track, distance, going,
     rail, barrier and field size plus each horse's last 3 and 8 GPS runs (width, extra ground, early speed,
     settle position, gap to the leader).
  2. Within each race the runners are ranked on the model's forecast and then placed using the spread real fields
     show at that field size (distance matching), so the picture has the spread of a real race. The order is the
     forecast; each exact position is uncertain (typical error is written to the file).

Width means different things by state: VIC/SA GPS only has each horse's average width over the whole run, QLD has
width every 200m so QLD uses width at the 800m mark.

Run after the daily GPS job:   python analysis/trip_map/build_trip_map.py
Also covers tracks with no GPS via nongps.py (gap from results, width estimated).
Writes trip_map.json at the repo root (read by frontend/src/lib/tripMap.ts).
"""
import glob
import json
import os
import re
import sys
from datetime import datetime, timezone

import lightgbm as lgb
import numpy as np
import pandas as pd

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..'))
OUT = os.path.join(ROOT, 'trip_map.json')
TODAY = pd.Timestamp(os.environ.get('TRIP_MAP_TODAY') or datetime.now(timezone.utc).strftime('%Y-%m-%d'))
Q = np.linspace(0.01, 0.99, 99)
PARAMS = dict(objective='regression', learning_rate=0.04, num_leaves=31, min_data_in_leaf=80, feature_fraction=0.8, verbose=-1, num_threads=4)
ROUNDS = 400


def clean_name(s):
    return s.astype(str).str.lower().str.replace(r'\s*\([a-z]{2,3}\)\s*$', '', regex=True).str.replace(r'[^a-z0-9 ]', '', regex=True).str.strip()


# ---------------------------------------------------------------- results
def load_results():
    cols = ['race_id', 'horse_id', 'horse', 'date', 'track', 'distance', 'going', 'barrier', 'field_size', 'position800m', 'margin800m',
            'rail_position', 'wpr', 'isBarrierTrial', 'is_jumpout']
    res = pd.concat([pd.read_csv(f, usecols=lambda c: c in set(cols), low_memory=False) for f in sorted(glob.glob(os.path.join(ROOT, 'race_results_20*.csv.gz')))])
    res = res.drop_duplicates(['race_id', 'horse_id'])
    res = res[(~res.isBarrierTrial.astype(bool)) & (~res.is_jumpout.fillna(False).astype(bool))].copy()
    res['date'] = pd.to_datetime(res['date'])
    res['hn'] = clean_name(res.horse)
    return res


def parse_rail(s):
    s = s.astype(str)
    return np.where(s.str.contains('True'), 0.0, pd.to_numeric(s.str.extract(r'(\d+)\s*m')[0], errors='coerce'))


def parse_going(s):
    return pd.to_numeric(s.astype(str).str.extract(r'(\d+)')[0], errors='coerce')


def add_result_features(d):
    d = d.copy()
    d['fs'] = d.field_size
    d['barfrac'] = (d.barrier - 1) / (d.fs - 1).clip(lower=1)
    d['rail_m'] = parse_rail(d.rail_position)
    d['going_s'] = parse_going(d.going)
    d['settle'] = (d.position800m - 1) / (d.fs - 1).clip(lower=1)
    d['gap800'] = d.margin800m.clip(0, 30)
    return d


# ---------------------------------------------------------------- VIC/SA GPS runs
def vicsa_runs(res):
    gdir = os.path.join(ROOT, 'data', 'gps')
    r = pd.concat([pd.read_parquet(f) for f in sorted(glob.glob(os.path.join(gdir, 'rc_gps_runs_*.parquet')))])
    r['date'] = pd.to_datetime(r.start_utc).dt.tz_convert('Australia/Melbourne').dt.tz_localize(None).dt.normalize()
    r['hn'] = clean_name(r.horse)
    r['dist'] = r.race_distance.str.replace('m', '').astype(int)
    s = pd.concat([pd.read_parquet(f) for f in sorted(glob.glob(os.path.join(gdir, 'rc_gps_sections_*.parquet')))])
    k = ['meet_code', 'race_no', 'tab_no']
    s = s[((s.from_m - s.to_m) >= 50) & (s.split_s > 0)].sort_values(k + ['from_m'], ascending=[True, True, True, False])
    s['m'] = s.from_m - s.to_m
    s['i'] = s.groupby(k).cumcount()
    s['n'] = s.groupby(k).i.transform('max') + 1
    s = s[s.n >= 4]
    e = s[s.i < 2].groupby(k).agg(em=('m', 'sum'), et=('split_s', 'sum'))
    p = e.reset_index()
    p['early_v'] = p.em / p.et
    g = r.merge(p[k + ['early_v']], on=k)
    g = g[(g.finish > 0) & g.time_s.notna() & (g.time_s < 200)].copy()
    g['avg_v'] = g.dist / g.time_s
    g = g[(g.avg_v > 10) & (g.avg_v < 22)]
    gr = ['meet_code', 'race_no']
    g['early'] = g.early_v - g.groupby(gr).early_v.transform('mean')
    g['nrun'] = g.groupby(gr).horse.transform('size')
    g = g[g.nrun >= 6]
    rk = res[res.wpr.notna()][['race_id', 'date', 'hn', 'distance', 'track', 'horse_id']].copy()
    rk = rk[~rk.duplicated(['date', 'hn', 'distance'], keep=False)]
    j = g.merge(rk, left_on=['date', 'hn', 'dist'], right_on=['date', 'hn', 'distance'])
    j['extra'] = j.dist_travelled_m - j.race_distance.str.replace('m', '').astype(float)
    j['lane'] = j.rail_avg_m
    j = j.drop(columns=[c for c in ['distance', 'barrier', 'field_size', 'going', 'position800m', 'margin800m', 'rail_position'] if c in j.columns]).merge(res[['race_id', 'horse_id', 'distance', 'going', 'barrier', 'field_size', 'position800m', 'margin800m', 'rail_position']], on=['race_id', 'horse_id'])
    j = add_result_features(j)
    j = j[j.extra.between(-5, 60) & j.lane.notna()]
    j['state'] = 'VICSA'
    return j[['race_id', 'horse_id', 'date', 'track', 'state', 'distance', 'barrier', 'barfrac', 'fs', 'rail_m', 'going_s', 'extra', 'lane', 'early', 'settle', 'gap800']]


# ---------------------------------------------------------------- QLD GPS runs (200m sections: width at 800m from home)
def qld_runs(res):
    gdir = os.path.join(ROOT, 'data', 'gps')
    rs = res[(res.date >= '2022-01-01') & res.wpr.notna()].copy()
    q = pd.concat([pd.read_parquet(f) for f in sorted(glob.glob(os.path.join(gdir, 'rq_gps_runs_*.parquet')))])
    q['date'] = pd.to_datetime(q.race_date).astype('datetime64[ns]')
    q['hn'] = clean_name(q.horse)
    q = q[q.result_state == 'Finished'].copy()
    u = rs.groupby(['date', 'hn']).filter(lambda z: len(z) == 1)
    mp = q.merge(u[['date', 'hn', 'track']], on=['date', 'hn']).groupby(['course', 'track']).size().reset_index(name='n')
    tot = mp.groupby('course').n.transform('sum')
    mp = mp[(mp.n / tot >= 0.5)].sort_values('n', ascending=False).drop_duplicates('course')
    q['track'] = q.course.map(dict(zip(mp.course, mp.track)))
    s = pd.concat([pd.read_parquet(f) for f in sorted(glob.glob(os.path.join(gdir, 'rq_gps_sections_*.parquet')))])
    s = s[(s.split_s > 5) & (s.split_s < 30) & (s.avg_speed_ms > 8) & (s.avg_speed_ms < 22) & (s.real_dist_m > 150) & (s.real_dist_m < 260)].sort_values(['race_code', 'tab_no', 'cum_dist_m'])
    k = ['race_code', 'tab_no']
    s['i'] = s.groupby(k).cumcount()
    s['n'] = s.groupby(k).i.transform('max') + 1
    s = s[s.n >= 4]
    early = s[s.i < 2].groupby(k).apply(lambda z: z.real_dist_m.sum() / z.split_s.sum()).rename('q_early').reset_index()
    q = q.merge(early, on=k, how='inner')
    q['early'] = q.q_early - q.groupby('race_code').q_early.transform('mean')
    rk = rs[['race_id', 'horse_id', 'date', 'hn', 'track', 'distance', 'barrier', 'field_size', 'going', 'position800m', 'margin800m', 'rail_position']]
    rk = rk[~rk.duplicated(['date', 'hn', 'track'], keep=False)]
    qm = q.drop(columns=[c for c in ['going', 'distance', 'barrier', 'field_size'] if c in q.columns]).merge(rk, on=['date', 'hn', 'track'], how='inner').drop_duplicates(['race_code', 'tab_no'])
    qm['extra'] = qm.dist_travelled_m - qm.distance
    s2 = s.merge(qm[['race_code', 'tab_no', 'distance']], on=k, how='inner')
    s2['rem'] = s2.distance - s2.cum_dist_m

    def prof(z):
        j = (z.rem - 800).abs().idxmin()
        return z.rail_m[j] if abs(z.rem[j] - 800) <= 150 else np.nan

    lane = s2.groupby(k).apply(prof).rename('lane').reset_index()
    qm = qm.merge(lane, on=k)
    qm = add_result_features(qm)
    qm = qm[qm.extra.between(-5, 60) & qm.lane.between(0, 40)]
    qm['state'] = 'QLD'
    return qm[['race_id', 'horse_id', 'date', 'track', 'state', 'distance', 'barrier', 'barfrac', 'fs', 'rail_m', 'going_s', 'extra', 'lane', 'early', 'settle', 'gap800']]


# ---------------------------------------------------------------- history features
TARGETS = ['extra', 'lane', 'early', 'settle', 'gap800']
BASE = ['trk', 'distance', 'barrier', 'barfrac', 'fs', 'rail_m', 'going_s']


def add_history(a):
    a = a.sort_values(['horse_id', 'date', 'race_id']).reset_index(drop=True)
    g = a.groupby('horse_id')
    for t in TARGETS:
        a[t + '_h3'] = g[t].transform(lambda s: s.shift(1).rolling(3, min_periods=1).mean())
        a[t + '_h8'] = g[t].transform(lambda s: s.shift(1).rolling(8, min_periods=2).mean())
    a['n_lead'] = a.groupby('race_id').settle_h3.transform(lambda s: (s <= 0.25).sum())
    a['own_rel'] = a.settle_h3 - a.groupby('race_id').settle_h3.transform('mean')
    a['n_hist'] = g.cumcount()
    return a


HIST = [t + s for t in TARGETS for s in ('_h3', '_h8')] + ['n_lead', 'own_rel']
FEATS = BASE + HIST


def dist_band(d):
    return pd.cut(d, [0, 1150, 1450, 1850, 9999], labels=False)


def fs_band(f):
    return pd.cut(f, [0, 9, 12, 14, 99], labels=False)


def fit_state(train):
    """Models and spread templates for one state's runs (all GPS runs before today)."""
    train = train.copy()
    train['band'] = dist_band(train.distance)
    train['fsb'] = fs_band(train.fs)
    models, tabs = {}, {}
    for t in ('gap800', 'lane'):
        A = train[train[t].notna()]
        models[t] = lgb.train(PARAMS, lgb.Dataset(A[FEATS], A[t]), ROUNDS)
    gg = train[train.gap800.notna()]
    tabs['gap'] = {(int(b), int(f)): np.quantile(z.gap800, Q) for (b, f), z in gg.groupby(['band', 'fsb']) if len(z) > 200}
    ll = train[(train.fs >= 8) & train.lane.notna()].copy()
    ll['dev'] = ll.lane - ll.groupby('race_id').lane.transform('mean')
    tabs['lane'] = {int(f): np.quantile(z.dev, Q) for f, z in ll.groupby('fsb') if len(z) > 200}
    return models, tabs


def scenario(df, models, tabs):
    """Forecast ranks -> placed positions with real-race spread. df needs FEATS, race_id, distance, fs."""
    out = df.copy()
    out['raw_gap'] = models['gap800'].predict(out[FEATS])
    out['raw_lane'] = models['lane'].predict(out[FEATS])
    out['band'] = dist_band(out.distance)
    out['fsb'] = fs_band(out.fs)
    g = out.groupby('race_id')
    for key in ('gap', 'lane'):
        out['p_' + key] = (g['raw_' + key].rank(method='first') - 0.5) / g['raw_' + key].transform('size')
    gap, lane = [], []
    for row in out.itertuples():
        q = tabs['gap'].get((int(row.band), int(row.fsb))) if pd.notna(row.band) and pd.notna(row.fsb) else None
        gap.append(np.interp(row.p_gap, Q, q) if q is not None else np.nan)
        qd = tabs['lane'].get(int(row.fsb)) if pd.notna(row.fsb) else None
        lane.append(np.interp(row.p_lane, Q, qd) if qd is not None else 0.0)
    out['gap'] = gap
    out['lane_dev'] = lane
    out['lane'] = out.groupby('race_id').raw_lane.transform('mean') + out.lane_dev
    return out


def main():
    print('loading results ...', flush=True)
    res = load_results()
    print('building GPS run tables ...', flush=True)
    a = pd.concat([vicsa_runs(res), qld_runs(res)], ignore_index=True)
    a = a[a.fs >= 5]
    a['trk'] = a.track.astype('category')
    cats = list(a.trk.cat.categories)
    a = add_history(a)
    a['trk'] = pd.Categorical(a.track, categories=cats)
    print('GPS runs:', a.groupby('state').size().to_dict(), flush=True)

    # ---- held-out check (2025+) to size the typical error
    err = {}
    for state, z in a.groupby('state'):
        tr, te = z[z.date < '2025-01-01'], z[(z.date >= '2025-01-01') & (z.fs >= 8)].copy()
        te = te[te.race_id.map(te.groupby('race_id').size()) >= 6]
        m, t = fit_state(tr)
        sc = scenario(te, m, t)
        okg = sc.gap800.notna() & sc.gap.notna()
        okl = sc.lane.notna() & sc.lane_dev.notna()
        yc = lambda col: te[col] - te.groupby('race_id')[col].transform('mean')
        err[state] = dict(
            gap=round(float(np.sqrt(((sc.gap800 - sc.gap)[okg] ** 2).mean())), 2),
            lane=round(float(np.sqrt(((te.lane - sc.lane)[okl] ** 2).mean())), 2),
            gap_corr=round(float(np.corrcoef((sc.raw_gap - sc.groupby('race_id').raw_gap.transform('mean'))[okg], yc('gap800')[okg])[0, 1]), 2),
            lane_corr=round(float(np.corrcoef((sc.raw_lane - sc.groupby('race_id').raw_lane.transform('mean'))[okl], yc('lane')[okl])[0, 1]), 2),
            n_races=int(te.race_id.nunique()),
        )
        print(state, 'held-out 2025+:', err[state], flush=True)

    # ---- final models on everything before today
    fitted = {}
    for state, z in a[a.date < TODAY].groupby('state'):
        fitted[state] = fit_state(z)
    tracks_by_state = {s: set(z.track) for s, z in a.groupby('state')}

    # ---- upcoming races
    cols = ['date', 'venue', 'state', 'race_id', 'race', 'distance', 'going', 'rail_position', 'run_id', 'horse_id', 'barrier', 'horse', 'scratched']
    up = pd.read_csv(os.path.join(ROOT, 'toprate_runners.csv'), usecols=lambda c: c in set(cols), low_memory=False)
    up['date'] = pd.to_datetime(up.date)
    up = up[(up.date >= TODAY) & (up.barrier > 0) & (up.scratched.fillna(0) != 1)].copy()
    up['track'] = up.venue
    name_to_id = res.sort_values('date').drop_duplicates('hn', keep='last').set_index('hn').horse_id.to_dict()
    up['hn'] = clean_name(up.horse)
    up['horse_id'] = up.horse_id.fillna(up.hn.map(name_to_id))
    unk = up.horse_id.isna()
    up.loc[unk, 'horse_id'] = -(np.arange(unk.sum()) + 1)
    up['horse_id'] = up.horse_id.astype('int64')
    up['fs'] = up.groupby('race_id').run_id.transform('size')
    up['barfrac'] = (up.barrier - 1) / (up.fs - 1).clip(lower=1)
    up['rail_m'] = parse_rail(up.rail_position)
    up['going_s'] = parse_going(up.going)
    up = up[(up.fs >= 5)]
    races = {}
    for state, (models, tabs) in fitted.items():
        u = up[up.track.isin(tracks_by_state[state])].copy()
        if u.empty:
            continue
        hist_rows = a[(a.state == state) & (a.date < TODAY)][['race_id', 'horse_id', 'date', 'track'] + TARGETS]
        u2 = u[['race_id', 'horse_id', 'date', 'track']].assign(**{t: np.nan for t in TARGETS})
        comb = pd.concat([hist_rows.assign(_up=0), u2.assign(_up=1)], ignore_index=True)
        comb['race_id'] = comb.race_id.astype(str)
        comb = add_history(comb.assign(fs=0, barrier=0, barfrac=0, rail_m=0, going_s=0, distance=0))
        feat = comb[comb._up == 1][['race_id', 'horse_id'] + HIST + ['n_hist']]
        u['race_id'] = u.race_id.astype(str)
        u = u.merge(feat, on=['race_id', 'horse_id'], how='left')
        u['trk'] = pd.Categorical(u.track, categories=cats)
        sc = scenario(u, models, tabs)
        # last GPS run per horse for the tooltip
        last = hist_rows.sort_values('date').drop_duplicates('horse_id', keep='last').set_index('horse_id')
        for rid, z in sc.groupby('race_id'):
            z = z.copy()
            z['gap'] = z.gap - z.gap.min()
            first = z.iloc[0]
            races[str(rid)] = dict(
                venue=first.venue, date=str(first.date.date()), race=int(first.race) if pd.notna(first.race) else None, distance=int(first.distance),
                going=None if pd.isna(first.going) else str(first.going), rail=None if pd.isna(first.rail_position) else str(first.rail_position),
                state=state, laneKind='avg' if state == 'VICSA' else '800m', fs=int(len(z)), err=err[state],
                runners=[dict(rid=str(int(r.run_id)), name=r.horse, barrier=int(r.barrier),
                              gap=None if pd.isna(r.gap) else round(float(r.gap), 1), lane=round(float(max(0.3, r.lane)), 1),
                              nHist=int(r.n_hist) if pd.notna(r.n_hist) else 0,
                              last=(dict(date=str(last.loc[r.horse_id, 'date'].date()), track=last.loc[r.horse_id, 'track'], lane=round(float(last.loc[r.horse_id, 'lane']), 1) if 'lane' in last.columns else None)
                                    if r.horse_id in last.index else None)) for r in z.sort_values('barrier').itertuples()])
    # ---- tracks without GPS: results-based gap forecast, estimated width (see nongps.py)
    try:
        import nongps
        o_races, o_err = nongps.build(res, a, TODAY, up)
        races.update(o_races)
        err['OTHER'] = o_err
        print('non-GPS races:', len(o_races), flush=True)
    except Exception as e:  # never lose the GPS maps because of this extension
        print('non-GPS trip map skipped:', repr(e), flush=True)
    payload = dict(generated=datetime.now(timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ'), trainEnd=str(a.date.max().date()), error=err, races=races)
    with open(OUT, 'w') as f:
        json.dump(payload, f, separators=(',', ':'))
    print('wrote', OUT, len(races), 'races', os.path.getsize(OUT) // 1024, 'KB')


if __name__ == '__main__':
    sys.exit(main())
