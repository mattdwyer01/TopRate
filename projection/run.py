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

sys.path.append(F.ROOT)
import atw_offsets  # noqa: E402

ROOT, M = F.ROOT, F.MODELS
CACHE = os.path.join(os.path.dirname(__file__), 'cache')
SUIT_BASE = ['pos_hist3', 'own_rel', 'm800_hist3', 'bf', 'field_size', 'dist', 'going_num']


WT_K = 0.4   # WPR per kg above the field average; out-of-sample fit on 4,551 races: 0.41 (90% interval 0.35 to 0.47). Set 0 to switch the term off (then rerun projection/add_weight_adj.py)


# Main-model projection = recent-form anchor (the linear part) + a gradient-boosted correction. The correction is split per feature with
# TreeSHAP and summed into these groups for the horse page's "why this projection" breakdown; anchor + groups equals the main-model base exactly.
GROUPS = {
    'form': ['exp', 'w1', 'w2', 'w3', 'm5', 'cm', 'ff3', 'mg3', 'std5', 'max5', 'peak', 'd12', 'd13', 'nruns', 'jh_n'],
    'rest': ['gap', 'run_in_prep', 'trial_days', 'trial_fin_frac', 'trial_margin', 'trial_n90', 'trial_since_run', 'fu_adv', 'fu_adv_n'],
    'class': ['cls_level', 'cls_level_prev', 'class_chg', 'grade', 'grade_chg', 'track_level'],
    'going': ['going_num', 'going_chg', 'going_adv', 'going_adv_n', 'lad_r25_going', 'lad_r25_going_rel'],
    'dist_track': ['dist', 'dist_chg', 'dist_adv', 'dist_adv_n', 'track_adv', 'track_adv_n', 'lad_r25_dist', 'lad_r25_dist_rel', 'lad_r25_both', 'lad_r25_both_rel'],
    'connections': ['jock_eff', 'jock_eff_n', 'trn_eff', 'trn_eff_n', 'jock_chg', 'jd_eff', 'jd_eff_n', 'jt_eff', 'jt_eff_n', 'jock_form', 'jock_form_n',
                    'td_eff', 'td_eff_n', 'tfu_eff', 'tfu_eff_n', 'trn_form', 'trn_form_n', 'lad_r26_stable_chg'],
    'weight_age': ['wt', 'wt_chg', 'wt_rel', 'weight_allowance', 'horse_age', 'sex', 'lad_r27_sire', 'lad_r27_sire_n', 'lad_r27_sire_d', 'lad_r27_sire_g'],
    'field': ['barrier', 'bf', 'field_size', 'f_exp', 'exp_rel', 'exp_rank', 'top_exp', 'exp_gap_top', 'lad_r30_pos3', 'lad_r30_own_rel', 'lad_r30_m800',
              'lad_r22_n_leaders', 'lad_r22_n_onpace', 'lad_r22_min', 'lad_r22_std', 'lad_r22_rank', 'lad_r22_lead_x_n'],   # plus every fs_* feature
    'comments': [],                                                                                            # every last_tx* / m3_tx* feature
}   # every other lad_* feature (recency base, placings, sectionals, job, past prices) falls into 'form'


def group_of(feat):
    if feat.startswith('last_tx') or feat.startswith('m3_tx'):
        return 'comments'
    if feat.startswith('fs_'):
        return 'field'
    for g, fs in GROUPS.items():
        if feat in fs:
            return g
    return 'form'


# Runners whose jockey is not declared yet have every jockey feature at its "never seen" value (effect 0 on 0 rides, no jockey change), which the
# model learned to read as an obscure rider: on the 8 Oct live set blank-jockey runners carried a connections step of -3.5 WPR against +0.2 for the
# declared ones (Lady Shenandoah, Waller, 13th of 15 off 100-rated form). An undeclared jockey is unknown, not poor, so the main model's jockey features are
# set to typical values (an average jockey, no change of rider) until the jockey is declared. Blanking a random half of the declared jockeys on the 8 Oct
# live set: main-model shift -3.70 (rmse 3.84) without the fix, -0.02 (rmse 1.02) with it. The light model is left alone (shift -0.35 without the fix, +0.42 with).
JOCKEY_MAIN = ['jock_eff', 'jock_eff_n', 'jd_eff', 'jd_eff_n', 'jt_eff', 'jt_eff_n', 'jock_form', 'jock_form_n', 'jh_n']
IMPUTE_BLANK_JOCKEY = True
# Going and track grading are blank for races more than a day or two out (60% of the 8 Oct upcoming runners). A blank went through the model as an
# unusual track (going step -0.8 and class step -1.0 against +0.2 and 0.0 for races with a known going), lowering every runner in the race together.
ASSUME_GOING = True
# Day-of track bias. The suitability model reads how the earlier races at the same meeting ran (draw and, when 800m positions exist, front-runner bias). Intraday
# only the finishing order is known (TAB's interim feed carries positions 1 to 4; the rest are set to the mean of the remaining positions), so only the inside/outside
# draw bias can be read and the front-bias inputs stay blank until the authoritative results land overnight. BIAS_FEATS are the inputs that carry it; `badj` in the log is
# the suitability adjustment with them minus the adjustment with them blanked, i.e. what the earlier races at the meeting changed. Display only, it is already inside adj.
BIAS_FEATS = ['fa_cum', 'oa_cum', 'fa_last', 'oa_last', 'n_prev', 'i_front', 'i_front2', 'i_out', 'i_out2']
INTRADAY_BIAS = True
ASSUMED_GOING, ASSUMED_GRADE = 'Good 4', 4.0


def impute_blank_jockey(R):
    """Replaces the jockey features of runners with no declared jockey by typical values (models/jockey_impute.json, medians over the declared runners
    of a live scoring pass; falls back to the declared runners of this pass). Returns the blank mask."""
    blank = R.jockey.isna().values
    if not IMPUTE_BLANK_JOCKEY or not blank.any():
        return blank
    path = os.path.join(M, 'jockey_impute.json')
    med = json.load(open(path)) if os.path.exists(path) else {c: R.loc[~blank, c].median() for c in JOCKEY_MAIN if c in R.columns and (~blank).sum() >= 20}
    for c, v in med.items():
        if c in R.columns and pd.notna(v):
            R.loc[blank, c] = v
    if 'jock_chg' in R.columns:
        R.loc[blank, 'jock_chg'] = 0.0
    return blank


def calibrate(R, cal):
    """Post-hoc calibration measured on the log's 44,297 out-of-sample projections (1 Jul to 5 Oct 2026, fit Jul-Aug, checked Sep-Oct; models/calibration.json):
    the main model under-projects the top of the range (actual above projected by about 0.12 WPR per point above 85) and the light-history model runs low by
    0.8 to 1.3 WPR depending on the number of prior runs (intercepts shrunk by a quarter). The correction is added to the base so base + suitability + weight = projection
    still holds on the horse page. Returns the per-runner correction."""
    top, light = cal['top'], cal['light']
    c = np.zeros(len(R))
    main = (R.routed == 'main').values
    c[main] = top['slope'] * np.maximum(R.proj.values[main] - top['knot'], 0)
    for n, p in light.items():
        s = ((R.routed == 'light') & (R.nruns == int(n))).values
        c[s] = p['a'] + p['b'] * (R.proj.values[s] - 70)
    return np.where(np.isnan(R.proj.values), 0.0, c)


def au_today():
    return (datetime.now(timezone.utc) + timedelta(hours=10)).strftime('%Y-%m-%d')


def booster(path):
    with gzip.open(path, 'rt') as f:
        return lgb.Booster(model_str=f.read())


def clean_name(s):
    return s.astype(str).str.lower().str.replace(r'\s*\([a-z]{2,3}\)\s*$', '', regex=True).str.replace(r'[^a-z0-9 ]', '', regex=True).str.strip()


def load_upcoming(today, hist, backfill_days=0):
    cols = ['date', 'venue', 'race_id', 'race', 'distance', 'going', 'track_grading', 'race_class', 'run_id', 'horse_id', 'barrier', 'horse', 'jockey', 'trainer',
            'weight_carried', 'scratched', 'finish_position', 'interim_resulted', 'resulted', 'fixed_win_price', 'starting_price_sp']
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
                          trainer=u.trainer, positionFinish=np.nan, marginFinish=np.nan,
                          priceStarting=pd.to_numeric(u.starting_price_sp, errors='coerce').where(lambda v: v > 1).fillna(pd.to_numeric(u.fixed_win_price, errors='coerce').where(lambda v: v > 1)), position800m=np.nan, margin800m=np.nan,
                          is_target=1, run_id=u.run_id))
    return X, done, u


def score(a, H, T, done, levels, main_info, light_info, tables, standin=None):
    """Projects every runner in T. standin: {run_id: projection} used as the rating of an earlier, not yet run entry of the same horse."""
    Hu = H[H.horse_id.isin(T.horse_id)] if a.fast else H     # fast: only the runners' own history (everything else comes from the cache)
    Tx = T.drop(columns=['run_id'])
    assumed = set(Tx.race_id[Tx.going.isna()]) if ASSUME_GOING else set()
    if assumed:     # going and track grading are not known until a day or two out: project on a typical track, not on a blank
        Tx['going'] = Tx.going.fillna(ASSUMED_GOING)
        Tx['trackGrading'] = Tx.trackGrading.fillna(ASSUMED_GRADE)
    if standin:
        Tx['wpr'] = T.run_id.map(standin)
    X = pd.concat([Hu, Tx], ignore_index=True)
    r = F.build_main(X, levels, tables=tables)
    tg = r.is_target == 1
    ph = F.build_pos_hist(r)
    fld = F.build_field(r)
    tri = F.build_trials(r)
    t3 = F.build_trials3(r)
    if a.fast and 'prk' not in tables:
        sys.exit('cache predates the ladder features: run --build-cache first')
    lad = F.build_ladder(r, ph=ph, tables=tables)
    lt = F.build_light(r, tables=tables)
    tf, svd = F.load_text(os.path.join(M, 'text_svd.joblib'))
    txt = F.text_features(r, tg, tf, svd)
    R = pd.concat([r, fld, tri, t3, lt, txt, lad], axis=1)
    R['lp'] = np.log(R.priceStarting.where(R.priceStarting > 1))     # live win price (fixed price, or SP for a backfilled race): read by the light model only
    R['sex'] = pd.Categorical(R.horse_sex, categories=levels['sex'])
    R = R[tg.values].copy()
    R = R.merge(T[['race_id', 'horse_id', 'run_id']], on=['race_id', 'horse_id'], how='left')
    impute_blank_jockey(R)

    # ---- main model
    boosters = [booster(os.path.join(M, f'main_seed{i}.txt.gz')) for i in range(1, 6)]
    base, coef, feats = main_info['base_cols'], np.array(main_info['linear_coefs']), main_info['features']
    use_main = (R.nruns >= 3) & R[base].notna().all(axis=1)
    R['p0'] = np.nan
    R['grp'] = None
    if use_main.any():
        D = R.loc[use_main, feats]
        lin = np.c_[np.ones(use_main.sum()), R.loc[use_main, base].values] @ coef
        R.loc[use_main, 'p0'] = lin + np.mean([b.predict(D) for b in boosters], axis=0)
        C = np.mean([b.predict(D, pred_contrib=True) for b in boosters], axis=0)
        gcols = {}
        for j, f in enumerate(feats):
            gcols.setdefault(group_of(f), []).append(j)
        grp = pd.DataFrame({g: C[:, js].sum(axis=1) for g, js in gcols.items()}, index=D.index)
        grp['anchor'] = lin + C[:, -1]    # linear part plus the booster's constant, so anchor + sum(groups) = base
        R.loc[use_main, 'grp'] = [json.dumps({k: round(float(v), 2) for k, v in row.items()}) for row in grp.to_dict('records')]
    # ---- light model
    lb = [booster(os.path.join(M, f'light_seed{i}.txt.gz')) for i in range(1, 6)]
    lnp = [booster(os.path.join(M, f'light_np_seed{i}.txt.gz')) for i in range(1, 6)]
    use_light = (R.nruns <= 2)
    R['light_priced'] = False
    for priced, models, info in [(True, lb, light_info), (False, lnp, light_info['np'])]:
        sel = use_light & (R.lp.notna() if priced else R.lp.isna())
        if sel.any():
            R.loc[sel, 'p0'] = np.mean([b.predict(R.loc[sel, info['features']]) for b in models], axis=0)
            R.loc[sel, 'light_priced'] = priced
    # ---- suitability adjustment (main-model runners only)
    Y = F.load_results_all()
    if a.fast:
        Y = Y[Y.horse_id.isin(T.horse_id) | (Y.date >= pd.Timestamp(a.today) - pd.Timedelta(days=3))]
    yt = R[['date', 'track', 'race_id', 'horse_id', 'jockey', 'trainer', 'barrier', 'field_size']].copy()
    if len(done) and INTRADAY_BIAS:
        d2 = pd.DataFrame(dict(date=done.date, track=done.venue, race_id=done.race_id, horse_id=done.horse_id.fillna(-1).astype('int64'), jockey=done.jockey, trainer=done.trainer,
                               barrier=done.barrier, field_size=done.groupby('race_id').run_id.transform('size'), positionFinish=pd.to_numeric(done.finish_position, errors='coerce')))
        # TAB's interim feed carries positions 1 to 4 only: a race counts once all four are known, and the unplaced runners get the mean of the remaining positions
        # (the same view the intraday test used, wpr_bias_intraday_test.py), so the draw bias is read over the whole field and not just the placegetters.
        known4 = d2.groupby('race_id').positionFinish.transform(lambda s: (s <= 4).sum() >= 4 or s.notna().sum() >= 4)
        d2 = d2[known4].copy()
        unk = d2.positionFinish.isna() | (d2.positionFinish > 4)
        d2.loc[unk, 'positionFinish'] = (5 + d2.field_size[unk]) / 2
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
    Znb = Z.copy()
    for c in BIAS_FEATS:
        if c in Znb.columns:
            Znb[c] = np.nan
    Z['badj'] = Z.adj - sm.predict(Znb[sfeats])
    R = R.merge(Z[['race_id', 'horse_id', 'adj', 'badj']], on=['race_id', 'horse_id'], how='left')
    R['going_assumed'] = R.race_id.isin(assumed)
    R['routed'] = np.where((R.nruns >= 3) & R.p0.notna(), 'main', np.where(R.nruns <= 2, 'light', 'none'))
    # weight carried: measured on the model's own out-of-sample projections, each kg above the field average costs about 0.4 to 0.6 WPR
    # (atw-target slope 0.38, winner-ranking slope 0.62 with 90% interval 0.44 to 0.82), beyond anything the base model learned from wt/wt_rel
    R['wtadj'] = -WT_K * R.wt_rel.fillna(0.0)
    R['proj'] = np.where(R.routed == 'main', R.p0 + R.adj.fillna(0), R.p0) + R.wtadj
    sd_main = lambda p: 7.96 if p >= 70 else 9.43 if p >= 60 else 11.90
    R['cal'] = calibrate(R, json.load(open(os.path.join(M, 'calibration.json'))))
    R['proj'] = R.proj + R.cal
    R['p0'] = R.p0 + R.cal
    R['sd'] = [sd_main(p) if m == 'main' else (light_info if pr else light_info['np'])['stage_sd'].get(str(int(n)), 11.0) for p, m, n, pr in zip(R.proj, R.routed, R.nruns, R.light_priced)]
    m = R.grp.notna()
    if m.any():     # keep anchor + groups = base: the calibration rides on the anchor
        R.loc[m, 'grp'] = [json.dumps({k: (round(v + c, 2) if k == 'anchor' else v) for k, v in json.loads(g).items()}) for g, c in zip(R.loc[m, 'grp'], R.loc[m, 'cal'])]
    return R


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
        F.build_ladder(rr, store=store)
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
    R = score(a, H, T, done, levels, main_info, light_info, tables)
    # a horse entered twice before its first entry has run has no rated previous run for the later entry: stand in the earlier entry's own
    # projection as that run's rating and score again, keeping the second pass only for the runners the first pass could not route
    for _ in range(3):
        todo = R.routed.eq('none')
        if not todo.any():
            break
        pr = R[R.proj.notna() & R.run_id.notna()]
        standin = dict(zip(pr.run_id.astype('int64'), pr.proj))
        R2 = score(a, H, T, done, levels, main_info, light_info, tables, standin).set_index(['race_id', 'horse_id'])
        keys = R.loc[todo, ['race_id', 'horse_id']].itertuples(index=False, name=None)
        fix = [k for k in keys if k in R2.index and R2.loc[k, 'routed'] != 'none']
        if not fix:
            break
        idx = R.index[todo & pd.Series([(r, h) in set(fix) for r, h in zip(R.race_id, R.horse_id)], index=R.index)]
        for c in R.columns:
            if c in R2.columns:
                R.loc[idx, c] = [R2.loc[(r, h), c] for r, h in zip(R.loc[idx, 'race_id'], R.loc[idx, 'horse_id'])]
    races = {}
    for rid, z in R.groupby('race_id'):
        first = z.iloc[0]
        races[str(rid)] = dict(venue=first.track, date=str(first.date.date()), going=None if (pd.isna(first.going) or first.going_assumed) else str(first.going), fs=int(len(z)),
                               runners={str(int(r.run_id)): dict(p=None if pd.isna(r.proj) else round(float(r.proj), 1), base=None if pd.isna(r.p0) else round(float(r.p0), 1),
                                                                  adj=None if (r.routed != 'main' or pd.isna(r.adj)) else round(float(r.adj), 2), wt=round(float(r.wtadj), 2), sd=round(float(r.sd), 1),
                                                                  m=r.routed, n=int(r.nruns)) for r in z.itertuples() if pd.notna(r.run_id)})
    made = datetime.now(timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ')
    rows = R[R.proj.notna() & R.run_id.notna()].copy()
    # each horse's ATW offset (form feed rating minus results rating) at the time of projecting, frozen in the log so the result card and Review can put the
    # projection on the scale of the feed's actual rating for a race that has since run
    off = atw_offsets.load_offsets(raw.horse.dropna().unique(), os.path.join(ROOT, 'wpr_form_history.csv.gz'))
    atwo_by_run = dict(zip(raw.run_id.dropna().astype('int64'), raw.loc[raw.run_id.notna(), 'horse'].astype(str).str.strip().str.lower().map(off)))
    rows = pd.DataFrame(dict(run_id=rows.run_id.astype('int64'), race_id=rows.race_id.astype('int64'), date=rows.date, proj=rows.proj, base=rows.p0,
                             adj=np.where(rows.routed == 'main', rows.adj, np.nan), sadj=np.where(rows.routed == 'light', rows.adj, np.nan), badj=np.where(rows.routed == 'main', rows.badj, np.nan), wtadj=rows.wtadj, sd=rows.sd, model=rows.routed, nruns=rows.nruns, grp=rows.grp, src='backfill' if a.backfill_days else 'live', made=made,
                             atwo=rows.run_id.map(atwo_by_run)))
    if len(rows) and not os.environ.get('PROJECTION_NO_LOG'):
        projlog.update(rows)
    payload = dict(generated=datetime.now(timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ'), trainThrough=main_info.get('train_through'), races=races)
    with open(a.out, 'w') as f:
        json.dump(payload, f, separators=(',', ':'))
    print('wrote', a.out, len(races), 'races', os.path.getsize(a.out) // 1024, 'KB')


if __name__ == '__main__':
    sys.exit(main())
