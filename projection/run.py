"""Live projections for upcoming races with the new WPR model.

Routing: runners with three or more prior rated runs use the main model (139 features); runners with 0-2 prior rated runs
use the light-history model. Main-model projections then get the small suitability adjustment (comment history, day-of
bias, finishing profile, jockey/trainer tendencies). Writes wpr_projection_new.json at the repo root.

The going each race is projected on is whatever toprate_runners.csv holds for that race when this runs, so a mid-meeting
track change is picked up by re-running (see README for the refresh path).

usage: python projection/run.py [--today YYYY-MM-DD] [--out PATH]
"""
import argparse
import glob
import gzip
import json
import os
import sys
from datetime import datetime, timedelta, timezone

import lightgbm as lgb
import numpy as np
import pandas as pd

sys.path.insert(0, os.path.dirname(__file__))
import features as F  # noqa: E402
import projlog  # noqa: E402

ROOT, M = F.ROOT, F.MODELS
CACHE = os.path.join(os.path.dirname(__file__), 'cache')
SUIT_BASE = ['pos_hist3', 'own_rel', 'm800_hist3', 'bf', 'field_size', 'dist', 'going_num']


WT_K = 0.4   # WPR per kg above the field average; out-of-sample fit on 4,551 races: 0.41 (90% interval 0.35 to 0.47). Set 0 to switch the term off (then rerun projection/add_weight_adj.py)


def au_today():
    return (datetime.now(timezone.utc) + timedelta(hours=10)).strftime('%Y-%m-%d')


def booster(path):
    with gzip.open(path, 'rt') as f:
        return lgb.Booster(model_str=f.read())


def clean_name(s):
    return s.astype(str).str.lower().str.replace(r'\s*\([a-z]{2,3}\)\s*$', '', regex=True).str.replace(r'[^a-z0-9 ]', '', regex=True).str.strip()


def load_upcoming(today, hist, backfill_days=0):
    cols = ['date', 'venue', 'race_id', 'race', 'distance', 'going', 'track_grading', 'race_class', 'run_id', 'horse_id', 'barrier', 'horse', 'jockey', 'trainer',
            'weight_carried', 'scratched', 'finish_position', 'interim_resulted', 'resulted']
    u = pd.read_csv(os.path.join(ROOT, 'toprate_runners.csv'), usecols=lambda c: c in set(cols), low_memory=False)
    u['date'] = pd.to_datetime(u.date)
    lo = pd.Timestamp(today) - pd.Timedelta(days=backfill_days)
    u = u[u.date >= lo].copy()
    run = u.groupby('race_id').apply(lambda z: ((z.interim_resulted.fillna(0) == 1) | (z.resulted.fillna(0) == 1)).any()).rename('ran')
    u = u.join(run, on='race_id')
    done = u[u.ran & (u.scratched.fillna(0) != 1) & (u.date >= pd.Timestamp(today))].copy()   # races already run today: only used for day-of bias
    if backfill_days:
        # runners of races that have already run but are NOT in the rated history yet (their WPR has not settled), so projecting them is
        # still out of sample; anything already in the history is skipped (it would see its own result)
        keys = set(zip(hist.race_id.astype('int64'), hist.horse_id.astype('int64')))
        u = u[(u.date < pd.Timestamp(today)) & (u.scratched.fillna(0) != 1) & (u.barrier > 0) & u.horse_id.notna()].copy()
        u = u[[(int(r), int(h)) not in keys for r, h in zip(u.race_id, u.horse_id)]]
        done = done.iloc[0:0]
    else:
        u = u[(~u.ran) & (u.scratched.fillna(0) != 1) & (u.barrier > 0)].copy()
    for c in ('jockey', 'trainer'):
        u[c] = u[c].where(u[c].astype(str).str.lower() != 'nan')
    # identify horses without an id by name
    last = hist.sort_values('date').drop_duplicates('horse_id', keep='last').set_index('horse_id')
    names = pd.concat([pd.read_csv(f, usecols=['horse_id', 'horse', 'date'], low_memory=False) for f in sorted(glob.glob(os.path.join(ROOT, 'race_results_20*.csv.gz')))])
    names['hn'] = clean_name(names.horse)
    n2id = names.sort_values('date').drop_duplicates('hn', keep='last').set_index('hn').horse_id.to_dict()
    u['hn'] = clean_name(u.horse)
    u['horse_id'] = u.horse_id.fillna(u.hn.map(n2id))
    unk = u.horse_id.isna()
    u.loc[unk, 'horse_id'] = -(np.arange(unk.sum()) + 1)
    u['horse_id'] = u.horse_id.astype('int64')
    u['field_size'] = u.groupby('race_id').run_id.transform('size')
    # age and sex carried from the horse's last run (racing age rolls over on 1 August)
    la = last[['horse_age', 'horse_sex', 'date']].rename(columns={'date': 'last_date', 'horse_age': 'last_age'})
    u = u.join(la, on='horse_id')
    roll = ((u.date.dt.year - u.last_date.dt.year) * 1 + ((u.date.dt.month >= 8).astype(int) - (u.last_date.dt.month >= 8).astype(int))).clip(lower=0)
    u['horse_age'] = u.last_age + roll
    X = pd.DataFrame(dict(race_id=u.race_id, horse_id=u.horse_id, date=u.date, track=u.venue, distance=u.distance, going=u.going, wpr=np.nan,
                          weightCarried=u.weight_carried, weight_allowance=np.nan, barrier=u.barrier, field_size=u.field_size, race_class=u.race_class,
                          trackGrading=pd.to_numeric(u.track_grading, errors='coerce'), horse_age=u.horse_age, horse_sex=u.horse_sex, jockey=u.jockey,
                          trainer=u.trainer, positionFinish=np.nan, marginFinish=np.nan, priceStarting=np.nan, position800m=np.nan, margin800m=np.nan,
                          is_target=1, run_id=u.run_id))
    return X, done, u


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--today', default=os.environ.get('PROJECTION_TODAY') or au_today())
    ap.add_argument('--out', default=os.path.join(ROOT, 'wpr_projection_new.json'))
    ap.add_argument('--backfill-days', type=int, default=0, help='also project runners of races from the last N days that ran before the log existed and whose WPR has not settled yet (still out of sample)')
    ap.add_argument('--fast', action='store_true', help='re-score using cached jockey/trainer/field tables (run after a going change); needs --build-cache first')
    ap.add_argument('--build-cache', action='store_true', help='build the cached tables from full history (run once a day after the authoritative results)')
    a = ap.parse_args()
    levels = json.load(open(os.path.join(M, 'levels.json')))
    main_info = json.load(open(os.path.join(M, 'main_info.json')))
    light_info = json.load(open(os.path.join(M, 'light_info.json')))
    print('loading history ...', flush=True)
    H = F.load_history()
    if a.build_cache:
        store = {}
        rr = F.build_main(H, levels, store=store)
        F.build_light(rr, store=store)
        F.build_suit(F.load_results_all(), F.build_pos_hist(rr), bias_since='2100-01-01', store=store)
        store['built_through'] = str(H.date.max().date())
        os.makedirs(CACHE, exist_ok=True)
        pd.to_pickle(store, os.path.join(CACHE, 'tables.pkl'))
        print('cache built through', store['built_through'])
        return
    tables = pd.read_pickle(os.path.join(CACHE, 'tables.pkl')) if a.fast else None
    T, done, raw = load_upcoming(a.today, H, a.backfill_days)
    print('upcoming runners', len(T), 'races', T.race_id.nunique(), flush=True)
    if T.empty:
        json.dump(dict(generated=datetime.now(timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ'), races={}), open(a.out, 'w'))
        return
    Hu = H[H.horse_id.isin(T.horse_id)] if a.fast else H     # fast: only the runners' own history (everything else comes from the cache)
    X = pd.concat([Hu, T.drop(columns=['run_id'])], ignore_index=True)
    r = F.build_main(X, levels, tables=tables)
    tg = r.is_target == 1
    ph = F.build_pos_hist(r)
    fld = F.build_field(r)
    tri = F.build_trials(r)
    t3 = F.build_trials3(r)
    lt = F.build_light(r, tables=tables)
    tf, svd = F.load_text(os.path.join(M, 'text_svd.joblib'))
    txt = F.text_features(r, tg, tf, svd)
    R = pd.concat([r, fld, tri, t3, lt, txt], axis=1)
    R['sex'] = pd.Categorical(R.horse_sex, categories=levels['sex'])
    R = R[tg.values].copy()
    R = R.merge(T[['race_id', 'horse_id', 'run_id']], on=['race_id', 'horse_id'], how='left')

    # ---- main model
    boosters = [booster(os.path.join(M, f'main_seed{i}.txt.gz')) for i in range(1, 6)]
    base, coef, feats = main_info['base_cols'], np.array(main_info['linear_coefs']), main_info['features']
    use_main = (R.nruns >= 3) & R[base].notna().all(axis=1)
    R['p0'] = np.nan
    if use_main.any():
        D = R.loc[use_main, feats]
        lin = np.c_[np.ones(use_main.sum()), R.loc[use_main, base].values] @ coef
        R.loc[use_main, 'p0'] = lin + np.mean([b.predict(D) for b in boosters], axis=0)
    # ---- light model
    lb = [booster(os.path.join(M, f'light_seed{i}.txt.gz')) for i in range(1, 6)]
    use_light = (R.nruns <= 2)
    if use_light.any():
        pl = np.mean([b.predict(R.loc[use_light, light_info['features']]) for b in lb], axis=0)
        R.loc[use_light, 'p0'] = pl
    # ---- suitability adjustment (main-model runners only)
    Y = F.load_results_all()
    if a.fast:
        Y = Y[Y.horse_id.isin(T.horse_id) | (Y.date >= pd.Timestamp(a.today) - pd.Timedelta(days=3))]
    yt = R[['date', 'track', 'race_id', 'horse_id', 'jockey', 'trainer', 'barrier', 'field_size']].copy()
    if len(done):
        d2 = pd.DataFrame(dict(date=done.date, track=done.venue, race_id=done.race_id, horse_id=done.horse_id.fillna(-1).astype('int64'), jockey=done.jockey, trainer=done.trainer,
                               barrier=done.barrier, field_size=done.groupby('race_id').run_id.transform('size'), positionFinish=pd.to_numeric(done.finish_position, errors='coerce')))
        yt = pd.concat([yt, d2], ignore_index=True)
    Y2 = pd.concat([Y, yt], ignore_index=True)
    lo = pd.Timestamp(a.today) - pd.Timedelta(days=a.backfill_days)
    S = F.build_suit(Y2, ph, bias_since=lo - pd.Timedelta(days=2), tables=tables)
    S = S[S.date >= lo].drop_duplicates(['race_id', 'horse_id'])
    Z = R[['race_id', 'horse_id', 'bf', 'field_size', 'dist', 'going_num']].merge(S, on=['race_id', 'horse_id'], how='left', suffixes=('', '_s'))
    Z = Z.merge(ph[['race_id', 'horse_id', 'm800_hist3', 'own_rel']], on=['race_id', 'horse_id'], how='left')
    Z['sty'] = Z.pos_hist3 - 0.5
    Z['i_front'], Z['i_front2'] = Z.fa_cum * Z.sty, Z.fa_last * Z.sty
    Z['i_out'], Z['i_out2'] = Z.oa_cum * (Z.bf - 0.5), Z.oa_last * (Z.bf - 0.5)
    Z['j_style'], Z['j_p8_x'] = Z.j_dev * Z.sty, Z.j_p8 - Z.pos_hist3
    sfeats = json.load(open(os.path.join(M, 'suitability_features.json')))
    sm = lgb.Booster(model_file=os.path.join(M, 'suitability_model.txt'))
    for c in sfeats:
        if c not in Z.columns:
            Z[c] = np.nan
    Z['adj'] = sm.predict(Z[sfeats])
    R = R.merge(Z[['race_id', 'horse_id', 'adj']], on=['race_id', 'horse_id'], how='left')
    R['routed'] = np.where((R.nruns >= 3) & R.p0.notna(), 'main', np.where(R.nruns <= 2, 'light', 'none'))
    # weight carried: measured on the model's own out-of-sample projections, each kg above the field average costs about 0.4 to 0.6 WPR
    # (atw-target slope 0.38, winner-ranking slope 0.62 with 90% interval 0.44 to 0.82), beyond anything the base model learned from wt/wt_rel
    R['wtadj'] = -WT_K * R.wt_rel.fillna(0.0)
    R['proj'] = np.where(R.routed == 'main', R.p0 + R.adj.fillna(0), R.p0) + R.wtadj
    sd_main = lambda p: 7.96 if p >= 70 else 9.43 if p >= 60 else 11.90
    R['sd'] = [sd_main(p) if m == 'main' else light_info['stage_sd'].get(str(int(n)), 11.0) for p, m, n in zip(R.proj, R.routed, R.nruns)]
    races = {}
    for rid, z in R.groupby('race_id'):
        first = z.iloc[0]
        races[str(rid)] = dict(venue=first.track, date=str(first.date.date()), going=None if pd.isna(first.going) else str(first.going), fs=int(len(z)),
                               runners={str(int(r.run_id)): dict(p=None if pd.isna(r.proj) else round(float(r.proj), 1), base=None if pd.isna(r.p0) else round(float(r.p0), 1),
                                                                  adj=None if (r.routed != 'main' or pd.isna(r.adj)) else round(float(r.adj), 2), wt=round(float(r.wtadj), 2), sd=round(float(r.sd), 1),
                                                                  m=r.routed, n=int(r.nruns)) for r in z.itertuples() if pd.notna(r.run_id)})
    made = datetime.now(timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ')
    rows = R[R.proj.notna() & R.run_id.notna()].copy()
    rows = pd.DataFrame(dict(run_id=rows.run_id.astype('int64'), race_id=rows.race_id.astype('int64'), date=rows.date, proj=rows.proj, base=rows.p0,
                             adj=np.where(rows.routed == 'main', rows.adj, np.nan), wtadj=rows.wtadj, sd=rows.sd, model=rows.routed, nruns=rows.nruns, src='backfill' if a.backfill_days else 'live', made=made))
    if len(rows) and not os.environ.get('PROJECTION_NO_LOG'):
        projlog.update(rows)
    payload = dict(generated=datetime.now(timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ'), trainThrough=main_info.get('train_through'), races=races)
    with open(a.out, 'w') as f:
        json.dump(payload, f, separators=(',', ':'))
    print('wrote', a.out, len(races), 'races', os.path.getsize(a.out) // 1024, 'KB')


if __name__ == '__main__':
    sys.exit(main())
