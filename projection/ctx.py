"""Context correction for the formula Proj (21 Oct 2026). ATW figures only: every rating read here is a runner-page rating as TopRate gives it
(`features.runner_page_runs()`, weight adjusted to the horse's next start); nothing from the results files and no plain-scale WPR (owner rule).

Proj = formula (models_tr/formula.json) + a LightGBM correction learned from context (models_tr/ctx_model.txt, ctx.json): distance and its change, going and its
change, class code, track grading, field size, barrier fraction, weight carried and its change, days since the last run, the last run's margin and finish, the spread
of the last four ratings, and the jockey's effect as of the day (shrunk mean formula residual of the jockey's earlier page runs). Trained by train_ctx.py.
`predict(T)` is the live path: T has one row per runner to project; history is the runner-page store strictly before each row's date."""
import json
import os
import sys

import numpy as np
import pandas as pd

try:
    import features as F
except ImportError:      # imported as projection.ctx from the repo root
    from projection import features as F

K = 8
M = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'models_tr')
JOCKEY_K = 20.0
REL_MIN_RUNS = 3          # the relevance model is used for horses with at least this many earlier page runs; fewer keep the plain context model
OWN_K = 5.0               # shrink for the horse's own earlier misses under the same conditions
LAGS = 4                  # earlier runs given their own context columns
# Venue effect (22 Oct 2026, owner's call, research/venue_feature_test.py): shrunk mean formula residual of the venue's page runs in [date - 186 days, date - 6 days).
# The newest 6 days are left out because a page rating for a run a few days old can still be Preliminary live but is Final in the training history.
# Held-out 2026 (35,081 runs): paired MSE gain +0.158 (95% +0.082 to +0.232) at K 200, against +0.143 at K 100 and +0.084 at K 50.
VEN_K, VEN_WINDOW, VEN_GAP = 200.0, 180, 6
BASE_FEATS = ['f', 'n', 'mean3', 'max4', 'std4', 'ldays', 'distance', 'dist_chg', 'going_n', 'going_chg', 'grade', 'field_size', 'barr_f', 'weightCarried', 'wt_chg',
              'l_mgn', 'l_posf', 'jock_eff', 'cn', 'cls_c', 'ven_eff']
# 23 Oct 2026 (owner's go-ahead, research/proj_unused_fields.py, proj_change_flags.py, proj_horse_conditions.py): race value (log prize money and its change from the last run),
# how often the horse has run with today's jockey and at today's track, and the rest of the field (mean formula figure of the other runners of the race who have a page history,
# and the runner's formula figure against it). The field mean is read over the runners the page store has: in training that is only part of an earlier field, live it is the declared field.
NEW_FEATS = ['lprize', 'prize_chg', 'pair_n', 'trk_n', 'fld_other', 'f_vs_fld']
FEATS = BASE_FEATS + NEW_FEATS
# 27 Oct 2026 (option 2, research/proj_speed_joint.py): jockey and trainer as-of win rates (projection/rates.py) and the runner's figures against the rest of its field
RATE_FEATS = ['jw', 'jw90', 'tw', 'tw90']
FLD_BASE = ['f', 'mean3', 'jw', 'jw90', 'tw', 'tw90', 'jock_eff']
FLD_FEATS = [p + c for c in FLD_BASE for p in ('r_', 'k_')]
FLD_REL_BASE = ['c_ewm3', 'sim_all']
FLD_REL_FEATS = [p + c for c in FLD_REL_BASE for p in ('r_', 'k_')]
# 6 Nov 2026: momentum inputs (rise3, rise_old, up3, step1) were tested for rising, lightly raced horses (research/momentum_ab.py) and did NOT help held-out: overall RMSE 8.486 to 8.495
# (paired gain -0.155, se 0.024), rising-light group 8.405 to 8.396, no bias in that group to correct. The columns are still built in context_columns but not used.
FEATS2 = FEATS + RATE_FEATS + FLD_FEATS


LAG_NAMES = [f'{nm}{k}' for k in range(1, LAGS + 1) for nm in ('dd', 'gd', 'trk', 'jk', 'cl', 'wd', 'dg', 'mg', 'pf', 'dev')]
CAR_NAMES = ['c_mean', 'c_max', 'c_sd', 'c_ewm3', 'c_near', 'c_vs_f', 'cmax_vs_f']
SIM_NAMES = ['sim_dist', 'sim_going', 'sim_track', 'sim_jock', 'sim_class', 'sim_days', 'sim_all']
OWN_NAMES = ['h_dist', 'h_dist_n', 'h_going', 'h_going_n', 'h_track', 'h_track_n', 'h_spell', 'h_spell_n', 'h_jock', 'h_jock_n']
REL_FEATS = LAG_NAMES + CAR_NAMES + SIM_NAMES + OWN_NAMES
REL_FEATS2 = REL_FEATS + FLD_REL_FEATS
# 9 Nov 2026 (research/proj_fit_feats_test.py): where today sits in the preparation against the horse's usual prep length, today's distance against the distance of its
# best three ratings, how much better its best runs on OTHER going are than on today's going group, and its usual running position (fraction of the field ahead at 800m).
FIT_FEATS = ['prep_no', 'prep_days', 'typ_prep_len', 'prep_vs_typ', 'best_dist', 'dist_from_best', 'dist_seen', 'going_best_gap', 'going_seen', 'style', 'style_sd']
PREP_GAP = 60      # days between runs that start a new preparation
# 9 Nov 2026 (research/proj_trials_test.py): barrier trials and jump-outs. Live they come from the runner pages (data/tr_form); training also reads the results files' trials so the
# converted-history rows see the trials those horses had. Lengths behind the venue/distance trial par use 0.147 s a length (the speed-figure conversion).
TRIAL_FEATS = ['tr_n_prep', 'tr_n90', 'tr_days', 'tr_fin', 'tr_won', 'tr_mgn', 'tr_trel', 'tr_best_fin', 'tr_best_trel', 'tr_jo']
_TRIALS = {}
# names of the extra inputs built by projection/ctx_ext.py (kept here so predict() can tell whether a model uses them without importing that module)
EXT_NAMES = set(['sire_eff', 'sire_lvl', 'sire_n', 'sire_dist_eff', 'sire_wet_eff', 'dsire_eff', 'dsire_lvl', 'dam_eff', 'dam_lvl', 'dam_n', 'trn_yng_eff', 'trn_yng_n',
                 'age', 'sex_c', 'win8', 'plc8', 'm4_finpct', 'm4_mfin', 'm8', 'max8', 'trn_eff', 'trn_n', 'trn_fu_eff', 'trn_fu_n', 'trn_ven_eff', 'trn_ven_n', 'jk_ven_eff',
                 'tj_eff', 'tj_n', 'trn_db_eff', 'trn_wet_eff', 'rl_w', 'fk_w'] + [f'{p}{k}' for k in (1, 2, 3) for p in ('rl', 'rln', 'fk', 'fkd', 'fkn')]
                + [p + c for c in ('age', 'win8', 'plc8', 'm4_finpct', 'm4_mfin', 'm8', 'max8', 'weightCarried', 'barr_f') for p in ('r_', 'k_')])
SPD_FEATS = ['sp1', 'sp2', 'sp3', 'sp4', 'n_sp', 'sp_ewm4', 'sp_max4', 'sp_std4', 'spd_vs_f', 'sd1', 'sd2', 'sd3', 'sd4', 'sd_mean4']     # the time-based block (speed figures), optional
SPD_A, SPD_B = 79.15, 1.33                         # speed figure (lengths vs par) to the rating scale, lib/speed.ts speedRatingOnScale


def going_num(s):
    s = s.astype(str)
    n = pd.to_numeric(s.str.extract(r'(\d+)')[0], errors='coerce')
    return n.where(n.notna(), np.where(s.str.contains('Synth|Dirt|Poly|Tapeta', case=False), 4, np.nan))


def class_code(s):
    """racing.com / runners.csv class names to the codes the runner pages use (MAI, OPEN, CLS1, BM64, RST55); a code passes through unchanged."""
    s = s.astype(str).str.strip()
    low = s.str.lower()
    out = s.copy()
    out = out.where(~low.eq('maiden'), 'MAI').where(~low.eq('open'), 'OPEN')
    m = low.str.extract(r'^class (\d)$')[0]
    out = out.where(m.isna(), 'CLS' + m.fillna(''))
    m = low.str.extract(r'^benchmark (\d+)$')[0]
    out = out.where(m.isna(), 'BM' + m.fillna(''))
    m = low.str.extract(r'^restricted (\d+)$')[0]
    out = out.where(m.isna(), 'RST' + m.fillna(''))
    return out


def add_speed(rp, first_year=2019):
    """Adds column sp (the run's own speed figure, lengths vs par, from speed_rating.figure_table) to a page frame that has horse (name) and date. NaN where there is no figure."""
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    if root not in sys.path:
        sys.path.insert(0, root)
    import speed_rating as SR
    ft = SR.figure_table(first_year)
    k = rp.horse.astype(str).str.lower().str.strip()
    m = pd.DataFrame({'key': k.values, 'date': pd.to_datetime(rp.date).dt.normalize().values}).merge(ft, on=['key', 'date'], how='left')
    rp = rp.copy()
    rp['sp'] = m['sp'].values
    return rp


def speed_features(T, rp):
    """The speed block for rows to project (or the page runs themselves for training): the horse's earlier speed figures (rp column sp) on their own and against the ratings of the same
    runs, history strictly before the row's date. T needs horse_id, date, f; rp needs horse_id, date, wpr, sp."""
    byh = {h: (x.date.values.astype('datetime64[D]').astype('int64'), x.sp.values.astype(float), x.wpr.values.astype(float)) for h, x in rp.groupby('horse_id')}
    n = len(T)
    out = np.full((n, len(SPD_FEATS)), np.nan)
    col = {c: i for i, c in enumerate(SPD_FEATS)}
    hid = pd.to_numeric(T.horse_id, errors='coerce').values
    dts = pd.to_datetime(T.date).values.astype('datetime64[D]').astype('int64')
    f = T.f.values.astype(float)
    for i in range(n):
        h = hid[i]
        a = None if np.isnan(h) else byh.get(h)
        if a is None or np.isnan(f[i]):
            continue
        j = int(np.searchsorted(a[0], dts[i], side='left'))
        if j == 0:
            continue
        sp, w = a[1][:j][::-1], a[2][:j][::-1]
        have = ~np.isnan(sp)
        out[i, col['n_sp']] = float(have.sum())
        if not have.any():
            continue
        v = sp[have]
        for k in range(min(4, len(sp))):
            out[i, col[f'sp{k + 1}']] = sp[k]
            out[i, col[f'sd{k + 1}']] = (SPD_A + SPD_B * sp[k]) - w[k] if not np.isnan(sp[k]) else np.nan
        ew = 0.5 ** (np.arange(len(v)) / 4.0)
        e = (v * ew).sum() / ew.sum()
        out[i, col['sp_ewm4']] = e
        out[i, col['sp_max4']] = v[:4].max()
        out[i, col['sp_std4']] = v[:4].std() if len(v[:4]) > 1 else np.nan
        out[i, col['spd_vs_f']] = (SPD_A + SPD_B * e) - f[i]
        dd = ((SPD_A + SPD_B * sp) - w)[:4]
        dd = dd[~np.isnan(dd)]
        out[i, col['sd_mean4']] = dd.mean() if len(dd) else np.nan
    return pd.DataFrame(out, columns=SPD_FEATS, index=T.index)


def going_group(g):
    """Going number to 0 (3 or less, firm and good), 1 (Good 4), 2 (5 to 7, soft), 3 (8+, heavy); -1 unknown."""
    g = np.asarray(g, dtype=float)
    return np.where(np.isnan(g), -1, np.digitize(np.nan_to_num(g, nan=-9), [3.5, 4.5, 7.5]))


def venue_key(s):
    """Venue name as a key: sponsor prefixes and aliases removed the same way the field merge does (Sportsbet-Ballarat and Ballarat are one venue)."""
    try:
        import rc_field_rows as RF
        norm = RF.norm_venue
    except ImportError:
        norm = lambda x: x
    cleaned = s.astype(str).str.replace('-', ' ', regex=False).str.strip()
    return cleaned.map(lambda x: norm(x).strip().lower() if x not in ('', 'nan', 'None') else '')


def clip_low():
    return json.load(open(os.path.join(M, 'formula.json'))).get('clip_low')


def coefs():
    f = json.load(open(os.path.join(M, 'formula.json')))
    return {int(k): np.array(v) for k, v in f['coef'].items()}


def page_frame():
    """Every rated, non-trial page run, sorted, with the history features (lags, days since, last-run details) built by shifting within the horse."""
    rp = F.runner_page_runs().copy()
    rp['going_n'] = going_num(rp.going)
    rp['grade'] = pd.to_numeric(rp.trackGrading, errors='coerce')
    for c in ('distance', 'weightCarried', 'barrier', 'field_size', 'marginFinish', 'positionFinish'):
        rp[c] = pd.to_numeric(rp[c], errors='coerce')
    rp['cls'] = class_code(rp.race_class)
    rp['vn'] = venue_key(rp.venue.where(rp.venue.notna(), rp.track))
    rp['venue'] = venue_key(rp.venue)
    rp = rp.sort_values(['horse_id', 'date']).reset_index(drop=True)
    g = rp.groupby('horse_id')
    for k in range(1, K + 1):
        # converted history (research/conv_history.py per_row): the plain rating of the earlier run plus THIS row's own shift c_t (the page is struck for this race)
        rp[f'r{k}'] = g.wpr_plain.shift(k) + rp.c_t if 'c_t' in rp.columns else g.wpr.shift(k)
    rp['n'] = g.cumcount().astype(float)
    rp['d_last'] = (rp.date - g.date.shift(1)).dt.days.astype(float)
    rp['l_dist'], rp['l_going'], rp['l_wt'], rp['l_mgn'] = g.distance.shift(1), g.going_n.shift(1), g.weightCarried.shift(1), g.marginFinish.shift(1)
    rp['l_posf'] = (rp.positionFinish / rp.field_size).groupby(rp.horse_id).shift(1)
    rp['lprize'] = np.log1p(pd.to_numeric(rp['prize'], errors='coerce')) if 'prize' in rp.columns else np.nan
    rp['l_lprize'] = rp.groupby('horse_id').lprize.shift(1)
    rp['pair_n'] = rp.groupby(['horse_id', rp.jockey.fillna('').astype(str)]).cumcount().astype(float)
    rp['trk_n'] = rp.groupby(['horse_id', 'vn']).cumcount().astype(float)
    return rp


def target_history(T, rp):
    """The same history features for the rows to project: the horse's page runs strictly before the row's date."""
    byh = {h: x for h, x in rp.groupby('horse_id')}
    cols = [f'r{k}' for k in range(1, K + 1)] + ['n', 'd_last', 'l_dist', 'l_going', 'l_wt', 'l_mgn', 'l_posf', 'l_lprize', 'pair_n', 'trk_n']
    out = np.full((len(T), len(cols)), np.nan)
    out[:, cols.index('n')] = 0.0
    out[:, cols.index('pair_n')] = 0.0
    out[:, cols.index('trk_n')] = 0.0
    tjk = T.jockey.fillna('').astype(str).values if 'jockey' in T.columns else np.full(len(T), '')
    tvn = T.vn.values if 'vn' in T.columns else np.full(len(T), '')
    hid = pd.to_numeric(T.horse_id, errors='coerce').values
    dts = pd.to_datetime(T.date).values
    for i, (h, d) in enumerate(zip(hid, dts)):
        x = byh.get(h) if not np.isnan(h) else None
        if x is None:
            continue
        xd = x.date.values
        j = np.searchsorted(xd, d, side='left')
        out[i, cols.index('n')] = j
        if j == 0:
            continue
        take = x.wpr.values[max(0, j - K):j][::-1]
        out[i, :len(take)] = take
        out[i, cols.index('d_last')] = (d - xd[j - 1]) / np.timedelta64(1, 'D')
        out[i, cols.index('l_dist')] = x.distance.values[j - 1]
        out[i, cols.index('l_going')] = x.going_n.values[j - 1]
        out[i, cols.index('l_wt')] = x.weightCarried.values[j - 1]
        out[i, cols.index('l_mgn')] = x.marginFinish.values[j - 1]
        out[i, cols.index('l_posf')] = (x.positionFinish.values[j - 1] / x.field_size.values[j - 1])
        out[i, cols.index('l_lprize')] = x.lprize.values[j - 1]
        out[i, cols.index('pair_n')] = float((x.jockey.fillna('').astype(str).values[:j] == tjk[i]).sum())
        out[i, cols.index('trk_n')] = float((x.vn.values[:j] == tvn[i]).sum())
    return pd.DataFrame(out, columns=cols, index=T.index)


def formula_pred(df, co, clip='default'):
    """clip: the outlier trim for the rating formula (formula.json clip_low); None for a target on another scale (the speed model passes None)."""
    f = np.full(len(df), np.nan)
    kk = df.n.clip(upper=K).values
    rc = F.clip_low_lags(df[[f'r{k}' for k in range(1, K + 1)]].values, clip_low() if isinstance(clip, str) else clip)   # outlier trim, same as features.formula_projection
    for n in range(1, K + 1):
        m = kk == n
        X = rc[m, :n]
        ok = ~np.isnan(X).any(axis=1)
        idx = np.where(m)[0][ok]
        f[idx] = co[n][0] + X[ok] @ co[n][1:]
    return f


def context_columns(df):
    r = df[[f'r{k}' for k in range(1, K + 1)]].values
    with np.errstate(all='ignore'):
        df['mean3'] = np.nanmean(r[:, :3], axis=1)
        df['max4'] = np.nanmax(np.where(np.isnan(r[:, :4]), -1e9, r[:, :4]), axis=1)
        df['std4'] = np.nanstd(r[:, :4], axis=1)
    df.loc[df.max4 < -1e8, 'max4'] = np.nan
    with np.errstate(all='ignore'):
        df['rise3'] = r[:, 0] - r[:, 2]
        df['step1'] = r[:, 0] - r[:, 1]
        df['rise_old'] = r[:, 0] - np.nanmean(r[:, 3:8], axis=1)
        df['up3'] = ((r[:, 0] > r[:, 1]) & (r[:, 1] > r[:, 2])).astype(float)
    df.loc[np.isnan(r[:, 2]), 'up3'] = np.nan
    df['dist_chg'] = df.distance - df.l_dist
    df['going_chg'] = df.going_n - df.l_going
    df['wt_chg'] = df.weightCarried - df.l_wt
    df['barr_f'] = df.barrier / df.field_size
    df['ldays'] = np.log1p(df.d_last)
    df['prize_chg'] = df.lprize - df.l_lprize
    return df


def jockey_table(pg):
    """Cumulative residual and count per (jockey, date) over the page runs, strictly before each date (cs, cn) and including it (cs_in, cn_in)."""
    t = pg[pg.resid.notna()].groupby(['jockey', 'date']).resid.agg(['sum', 'count']).reset_index().sort_values(['jockey', 'date'])
    t['cs_in'] = t.groupby('jockey')['sum'].cumsum()
    t['cn_in'] = t.groupby('jockey')['count'].cumsum()
    t['cs'] = t.cs_in - t['sum']
    t['cn'] = t.cn_in - t['count']
    return t


def add_jockey(df, tab, targets=False):
    if not targets:
        df = df.merge(tab[['jockey', 'date', 'cs', 'cn']], on=['jockey', 'date'], how='left')
    else:
        base = tab[['jockey', 'date', 'cs_in', 'cn_in']].rename(columns={'date': 'd0', 'cs_in': 'cs', 'cn_in': 'cn'}).sort_values('d0')
        t = df[['jockey', 'date']].reset_index().sort_values('date')
        mm = pd.merge_asof(t, base, left_on='date', right_on='d0', by='jockey', direction='backward', allow_exact_matches=False)
        df = df.copy()
        df['cs'] = pd.Series(mm['cs'].values, index=mm['index'].values).reindex(df.index).values
        df['cn'] = pd.Series(mm['cn'].values, index=mm['index'].values).reindex(df.index).values
    df['cn'] = df.cn.fillna(0)
    df['cs'] = df.cs.fillna(0)
    df['jock_eff'] = df.cs / (df.cn + JOCKEY_K)
    return df


def rel_features(T, rp):
    """Relevance features (22 Oct 2026): every earlier page run of the horse judged against TODAY'S race instead of one fixed weighting of the last eight ratings.
    T: rows to project (or, for training, the page runs themselves) with horse_id, date, distance, going_n, weightCarried, vn (venue key), jockey, cls and f (the formula).
    rp: the page frame with f and resid. History = the horse's page runs strictly before the row's date, so a past run and a future one get identical features.
    Families: lag context (how today differs from each of the last four runs and how that run went), career (all earlier runs), similarity-weighted average of the last
    eight ratings (distance, going, track, jockey, class, days, recency kernels, as the gap to f), and the horse's own earlier misses under the same conditions."""
    byh = {}
    for h, x in rp.groupby('horse_id'):
        byh[h] = dict(d=x.date.values.astype('datetime64[D]').astype('int64'), w=(x.wpr_plain if 'c_t' in x.columns else x.wpr).values, dist=x.distance.values, gn=x.going_n.values, wt=x.weightCarried.values,
                      vn=x.vn.values, jk=x.jockey.values.astype(object), cl=x.cls.values.astype(object), mg=x.marginFinish.values,
                      pf=(x.positionFinish / x.field_size).values, res=x.resid.values)
    n = len(T)
    out = np.full((n, len(REL_FEATS)), np.nan)
    col = {c: i for i, c in enumerate(REL_FEATS)}
    hid = pd.to_numeric(T.horse_id, errors='coerce').values
    dts = pd.to_datetime(T.date).values.astype('datetime64[D]').astype('int64')
    dist, gn, wt = T.distance.values.astype(float), T.going_n.values.astype(float), T.weightCarried.values.astype(float)
    vn, jk, cl, f = T.vn.values, T.jockey.astype(object).values, T.cls.astype(object).values, T.f.values.astype(float)
    tg = going_group(gn)
    shift = T['c_t'].values.astype(float) if 'c_t' in T.columns else np.zeros(n)   # per-row converted-history shift (0 for real page runs)
    for i in range(n):
        h = hid[i]
        a = None if np.isnan(h) else byh.get(h)
        if a is None or np.isnan(f[i]):
            continue
        j = int(np.searchsorted(a['d'], dts[i], side='left'))
        if j == 0:
            continue
        L = min(K, j)
        sl = slice(j - L, j)
        R = a['w'][sl][::-1] + shift[i]
        dd = dist[i] - a['dist'][sl][::-1]
        gd = gn[i] - a['gn'][sl][::-1]
        wd = wt[i] - a['wt'][sl][::-1]
        dg = (dts[i] - a['d'][sl][::-1]).astype(float)
        trk = (a['vn'][sl][::-1] == vn[i]).astype(float)
        sj = (a['jk'][sl][::-1] == jk[i]).astype(float)
        sc = (a['cl'][sl][::-1] == cl[i]).astype(float)
        mg, pf = a['mg'][sl][::-1], a['pf'][sl][::-1]
        rmean = R.mean()
        for k in range(min(LAGS, L)):
            k1 = k + 1
            for nm, v in (('dd', dd[k]), ('gd', gd[k]), ('trk', trk[k]), ('jk', sj[k]), ('cl', sc[k]), ('wd', wd[k]), ('dg', dg[k]), ('mg', mg[k]), ('pf', pf[k]), ('dev', R[k] - rmean)):
                out[i, col[f'{nm}{k1}']] = v
        # career: every earlier run
        w_all = a['w'][:j] + shift[i]
        out[i, col['c_mean']] = w_all.mean()
        out[i, col['c_max']] = w_all.max()
        out[i, col['c_sd']] = w_all.std(ddof=1) if j > 1 else np.nan
        ew = 0.5 ** (np.arange(j) / 3.0)
        out[i, col['c_ewm3']] = (w_all[::-1] * ew).sum() / ew.sum()
        out[i, col['c_near']] = float((w_all >= 0.95 * np.maximum.accumulate(w_all)).sum())
        out[i, col['c_vs_f']] = out[i, col['c_ewm3']] - f[i]
        out[i, col['cmax_vs_f']] = out[i, col['c_max']] - f[i]
        # similarity-weighted average of the last eight ratings (gap to the formula)
        rec = np.exp(-np.arange(L) / 4.0)
        ddn, gdn, dgn = np.abs(np.nan_to_num(dd, nan=1e4)), np.abs(np.nan_to_num(gd, nan=1e4)), np.nan_to_num(dg, nan=1e4)
        kern = {'sim_dist': np.exp(-ddn / 300.0), 'sim_going': np.exp(-gdn / 1.5), 'sim_track': 1.0 + 3.0 * trk, 'sim_jock': 1.0 + 3.0 * sj, 'sim_class': 1.0 + 3.0 * sc,
                'sim_days': np.exp(-dgn / 120.0), 'sim_all': np.exp(-ddn / 400.0) * np.exp(-gdn / 2.0) * (1 + 1.5 * trk) * (1 + sj) * (1 + sc)}
        for nm, kw in kern.items():
            ww = kw * rec
            sw = ww.sum()
            out[i, col[nm]] = (ww * R).sum() / sw - f[i] if sw > 0 else np.nan
        # the horse's own earlier formula misses under the same conditions (shrunk)
        res = a['res'][:j]
        okr = ~np.isnan(res)
        keys = (('h_dist', np.round(a['dist'][:j] / 200.0) == np.round(dist[i] / 200.0)), ('h_going', going_group(a['gn'][:j]) == tg[i]),
                ('h_track', a['vn'][:j] == vn[i]), ('h_jock', a['jk'][:j] == jk[i]))
        for nm, eq in keys:
            m = okr & eq
            out[i, col[nm]] = res[m].sum() / (m.sum() + OWN_K)
            out[i, col[nm + '_n']] = float(m.sum())
        prior_gap = np.concatenate([[np.nan], np.diff(a['d'][:j])]).astype(float)
        fu_hist = prior_gap > 60
        fu_now = (dts[i] - a['d'][j - 1]) > 60
        m = okr & (fu_hist == fu_now) & ~np.isnan(prior_gap)
        out[i, col['h_spell']] = res[m].sum() / (m.sum() + OWN_K)
        out[i, col['h_spell_n']] = float(m.sum())
    return pd.DataFrame(out, columns=REL_FEATS, index=T.index)


def trial_table(results_files=True):
    """Every barrier trial and jump-out: runner pages (data/tr_form) plus, by default, the results files. One row per horse and date."""
    key = 'all' if results_files else 'page'
    if key in _TRIALS:
        return _TRIALS[key]
    import glob, gzip
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    rows = []
    for f in sorted(glob.glob(os.path.join(root, 'data', 'tr_form', '*.json.gz'))):
        with gzip.open(f, 'rt') as fh:
            d = json.load(fh)
        for x in d.values():
            for r in (x.values() if isinstance(x, dict) else x):
                if isinstance(r, dict) and (r.get('isBarrierTrial') or r.get('isJumpout')) and r.get('horse_id') is not None:
                    rows.append((r['horse_id'], r['date'], r.get('positionFinish'), r.get('starters'), r.get('marginFinish'), r.get('winnersTime'), r.get('distance'),
                                 str(r.get('venue') or r.get('track') or ''), bool(r.get('isJumpout'))))
    t = pd.DataFrame(rows, columns=['horse_id', 'date', 'pos', 'st', 'mgn', 'wt', 'dist', 'venue', 'jo'])
    if results_files:
        cols = ['horse_id', 'date', 'positionFinish', 'field_size', 'marginFinish', 'winners_time', 'distance', 'venue', 'track', 'isBarrierTrial', 'is_jumpout', 'race_class']
        parts = []
        for f in sorted(glob.glob(os.path.join(root, 'race_results_20[0-9][0-9].csv.gz'))):
            x = pd.read_csv(f, usecols=lambda c: c in cols, low_memory=False)
            tri = (x.get('isBarrierTrial') == True) | (x.get('is_jumpout') == True) | x.race_class.astype(str).str.contains('Jumpout|Trial', case=False, na=False)
            x = x[tri]
            parts.append(pd.DataFrame({'horse_id': x.horse_id, 'date': x.date, 'pos': x.positionFinish, 'st': x.field_size, 'mgn': x.marginFinish, 'wt': x.winners_time,
                                       'dist': x.distance, 'venue': x.venue.where(x.venue.notna(), x.track).astype(str),
                                       'jo': (x.get('is_jumpout') == True) | x.race_class.astype(str).str.contains('Jumpout', case=False, na=False)}))
        t = pd.concat([t] + parts, ignore_index=True)
    t['horse_id'] = pd.to_numeric(t.horse_id, errors='coerce')
    t['date'] = pd.to_datetime(t.date, errors='coerce')
    t = t.dropna(subset=['horse_id', 'date']).drop_duplicates(['horse_id', 'date'], keep='first')
    for c in ('pos', 'st', 'mgn', 'wt', 'dist'):
        t[c] = pd.to_numeric(t[c], errors='coerce')
    t['mgn0'] = np.where(t.pos == 1, 0.0, t.mgn.clip(lower=0))
    t['par'] = t.groupby([t.venue.str.lower(), 'dist']).wt.transform('median')
    t['trel'] = (t.wt + 0.147 * t.mgn0 - t.par) / 0.147
    t['fin'] = (t.pos - 1) / (t.st - 1).clip(lower=1)
    t['d'] = t.date.values.astype('datetime64[D]').astype('int64')
    t = t.sort_values(['horse_id', 'd']).reset_index(drop=True)
    _TRIALS[key] = t
    return t


def trial_features(T, tt=None):
    """TRIAL_FEATS for the rows of T (horse_id, date, d_last = days since the last rated run): trials strictly before the date; 'since' = after the last rated run."""
    tt = trial_table() if tt is None else tt
    byh = {h: (g.d.values, g.fin.values, g.pos.values, g.mgn0.values, g.trel.values, g.jo.values.astype(float)) for h, g in tt.groupby('horse_id')}
    n = len(T)
    out = np.full((n, len(TRIAL_FEATS)), np.nan)
    col = {c: i for i, c in enumerate(TRIAL_FEATS)}
    out[:, col['tr_n_prep']] = 0
    out[:, col['tr_n90']] = 0
    hid = pd.to_numeric(T.horse_id, errors='coerce').values
    dd = pd.to_datetime(T.date).values.astype('datetime64[D]').astype('int64')
    dl = pd.to_numeric(T.d_last, errors='coerce').values.astype(float) if 'd_last' in T.columns else np.full(n, np.nan)
    for i in range(n):
        a = None if np.isnan(hid[i]) else byh.get(hid[i])
        if a is None:
            continue
        j = int(np.searchsorted(a[0], dd[i], side='left'))
        if j == 0:
            continue
        since = a[0][:j] > dd[i] - (dl[i] if not np.isnan(dl[i]) else 99999)
        out[i, col['tr_n_prep']] = since.sum()
        out[i, col['tr_n90']] = (a[0][:j] >= dd[i] - 90).sum()
        k = j - 1
        if dd[i] - a[0][k] > 180:
            continue
        out[i, col['tr_days']] = dd[i] - a[0][k]
        out[i, col['tr_fin']], out[i, col['tr_won']], out[i, col['tr_mgn']] = a[1][k], float(a[2][k] == 1), a[3][k]
        out[i, col['tr_trel']], out[i, col['tr_jo']] = a[4][k], a[5][k]
        if since.any():
            out[i, col['tr_best_fin']] = np.nanmin(a[1][:j][since]) if (~np.isnan(a[1][:j][since])).any() else np.nan
            out[i, col['tr_best_trel']] = np.nanmin(a[4][:j][since]) if (~np.isnan(a[4][:j][since])).any() else np.nan
    return pd.DataFrame(out, columns=TRIAL_FEATS, index=T.index)


def _gg(g):
    out = np.asarray(going_group(np.asarray(g, dtype=float)), dtype=float)
    return np.where(out < 0, np.nan, out)


def fit_features(T, rp):
    """FIT_FEATS for the rows in T from the horse's page runs in rp strictly before each row's date (one builder for training, T = rp, and for live targets).
    Ratings are only ranked or differenced within the horse, so the converted-history shift (c_t) does not matter here."""
    byh = {}
    for h, x in rp.groupby('horse_id'):
        d = x.date.values.astype('datetime64[D]').astype('int64')
        gap = np.r_[99999, np.diff(d)]
        pid = np.cumsum(gap > PREP_GAP)
        pno = np.ones(len(d), int); pst = d.copy()
        for i in range(1, len(d)):
            if pid[i] == pid[i - 1]:
                pno[i], pst[i] = pno[i - 1] + 1, pst[i - 1]
        fs = pd.to_numeric(x.field_size, errors='coerce').values.astype(float)
        p8 = (pd.to_numeric(x.position800m, errors='coerce').values - 1) / np.clip(fs - 1, 1, None) if 'position800m' in x.columns else np.full(len(d), np.nan)
        byh[h] = dict(d=d, pid=pid, pno=pno, pst=pst, w=(x.wpr_plain if 'wpr_plain' in x.columns else x.wpr).values.astype(float),
                      dist=x.distance.values.astype(float), gg=_gg(x.going_n.values), p8=p8)
    n = len(T)
    out = np.full((n, len(FIT_FEATS)), np.nan)
    col = {c: i for i, c in enumerate(FIT_FEATS)}
    hid = pd.to_numeric(T.horse_id, errors='coerce').values
    dts = pd.to_datetime(T.date).values.astype('datetime64[D]').astype('int64')
    dist = T.distance.values.astype(float)
    tgg = _gg(T.going_n.values)
    for i in range(n):
        h = hid[i]
        a = None if np.isnan(h) else byh.get(h)
        j = 0 if a is None else int(np.searchsorted(a['d'], dts[i], side='left'))
        if j == 0:
            out[i, col['prep_no']], out[i, col['prep_days']] = 1, 0
            continue
        new = dts[i] - a['d'][j - 1] > PREP_GAP
        pno = 1 if new else a['pno'][j - 1] + 1
        out[i, col['prep_no']] = pno
        out[i, col['prep_days']] = 0 if new else dts[i] - a['pst'][j - 1]
        cur = a['pid'][j - 1] + (1 if new else 0)
        done = a['pid'][:j] < cur
        if done.any():
            _, lens = np.unique(a['pid'][:j][done], return_counts=True)
            tl = float(np.median(lens))
            out[i, col['typ_prep_len']], out[i, col['prep_vs_typ']] = tl, pno - tl
        if j < 2:
            continue
        w = a['w'][:j]
        top = np.argsort(w)[::-1][:3]
        bd = float(np.median(a['dist'][:j][top]))
        out[i, col['best_dist']], out[i, col['dist_from_best']] = bd, dist[i] - bd
        out[i, col['dist_seen']] = float((np.abs(a['dist'][:j] - dist[i]) <= 100).sum())
        if not np.isnan(tgg[i]):
            g = a['gg'][:j]
            same, oth = g == tgg[i], (g != tgg[i]) & ~np.isnan(g)
            out[i, col['going_seen']] = float(same.sum())
            if same.any() and oth.any():
                out[i, col['going_best_gap']] = np.mean(np.sort(w[oth])[::-1][:3]) - np.mean(np.sort(w[same])[::-1][:3])
        p = a['p8'][:j]
        ok = ~np.isnan(p)
        if ok.sum() >= 2:
            out[i, col['style']], out[i, col['style_sd']] = float(np.median(p[ok])), float(p[ok].std())
    return pd.DataFrame(out, columns=FIT_FEATS, index=T.index)


def add_field(df):
    """fld_other and f_vs_fld: for each row with a formula figure, the mean formula figure of the OTHER rows of the same race that also have one (race = date, venue key, distance,
    field size, class), and its own figure against that. NaN when no other runner of the race has a figure."""
    k = df.date.astype(str) + '|' + df.vn.astype(str) + '|' + df.distance.astype(str) + '|' + df.field_size.astype(str) + '|' + df.cls.astype(str)
    has = df.f.notna()
    fv = df.f.where(has)
    cnt = has.astype(float).groupby(k).transform('sum')
    ssum = fv.groupby(k).transform('sum')
    others = cnt - has.astype(float)
    df = df.copy()
    df['fld_other'] = np.where(has & (others > 0), (ssum - df.f.fillna(0)) / others.where(others > 0), np.nan)
    df['f_vs_fld'] = df.f - df.fld_other
    return df


def _race_key(df):
    return df.date.astype(str) + '|' + df.vn.astype(str) + '|' + df.distance.astype(str) + '|' + df.field_size.astype(str) + '|' + df.cls.astype(str)


def add_field_rel(df, cols):
    """r_<c> (the runner's value minus the race mean) and k_<c> (its percentile rank in the race) for each column in cols; race = date, venue key, distance, field size, class."""
    k = _race_key(df)
    df = df.copy()
    new = {}
    for c in cols:
        g = df[c].groupby(k)
        new['r_' + c] = df[c] - g.transform('mean')
        new['k_' + c] = g.rank(pct=True)
    return pd.concat([df.drop(columns=[c for c in new if c in df.columns]), pd.DataFrame(new, index=df.index)], axis=1)


def add_trainer(rp):
    """Page runs carry no trainer: take it from the results files by (horse_id, date). Runs the results files do not cover (the last weeks) keep a blank trainer."""
    import glob
    if 'trainer' in rp.columns:
        return rp
    parts = []
    for f in sorted(glob.glob(os.path.join(os.path.dirname(M), '..', 'race_results_20[12]?.csv.gz'))) + [os.path.join(os.path.dirname(M), '..', 'race_results_2026.csv.gz')]:
        if os.path.exists(f):
            parts.append(pd.read_csv(f, usecols=lambda c: c in ('horse_id', 'date', 'trainer'), low_memory=False))
    t = pd.concat(parts, ignore_index=True)
    t['horse_id'] = pd.to_numeric(t.horse_id, errors='coerce')
    t['date'] = pd.to_datetime(t.date)
    t = t.dropna(subset=['horse_id', 'trainer']).drop_duplicates(['horse_id', 'date'], keep='last')
    return rp.merge(t[['horse_id', 'date', 'trainer']], on=['horse_id', 'date'], how='left')


def add_v2(df):
    """Option 2 columns on a frame that has date, jockey, trainer, f, mean3, jock_eff: rates and the field-relative block."""
    import rates
    df = rates.add_rates(df)
    return add_field_rel(df, FLD_BASE)


def add_venue(df, rp):
    """ven_eff for every row of df (columns venue, date): shrunk mean formula residual of the venue's page runs in the window before the date (rp carries resid)."""
    t = rp[rp.resid.notna()].groupby(['venue', 'date']).resid.agg(['sum', 'count']).reset_index().sort_values(['venue', 'date'])
    arr = {}
    for v, d in t.groupby('venue'):
        arr[v] = (d.date.values, np.concatenate([[0.0], np.cumsum(d['sum'].values)]), np.concatenate([[0.0], np.cumsum(d['count'].values)]))
    vs = np.zeros(len(df))
    vn = np.zeros(len(df))
    dts = pd.to_datetime(df.date).values
    for v, idx in df.groupby('venue').indices.items():
        a = arr.get(v)
        if a is None:
            continue
        dd, cs, cc = a
        hi = np.searchsorted(dd, dts[idx] - np.timedelta64(VEN_GAP, 'D'), side='left')
        lo = np.searchsorted(dd, dts[idx] - np.timedelta64(VEN_GAP + VEN_WINDOW, 'D'), side='left')
        vs[idx] = cs[hi] - cs[lo]
        vn[idx] = cc[hi] - cc[lo]
    df = df.copy()
    df['ven_eff'] = vs / (vn + VEN_K)
    df['ven_n'] = vn
    return df


def training_frame(v2=False):
    """Page runs with formula, residual and every context feature (training rows: runs with at least one earlier run). v2 adds the option 2 columns (rates, field-relative)."""
    co = coefs()
    rp = page_frame()
    if v2:
        rp = add_trainer(rp)
    rp['f'] = formula_pred(rp, co)
    rp = context_columns(rp)
    rp['resid'] = rp.wpr - rp.f
    rp = add_jockey(rp, jockey_table(rp))
    rp = add_venue(rp, rp)
    rp = add_field(rp)
    if v2:
        rp = add_v2(rp)
    rp = pd.concat([rp.drop(columns=[c for c in TRIAL_FEATS if c in rp.columns]), trial_features(rp)], axis=1)
    return rp


def training_frame_rel(v2=False):
    """training_frame plus the relevance features (rel_features run on the page runs themselves, history strictly before each run's date)."""
    rp = training_frame(v2)
    rp = pd.concat([rp, rel_features(rp, rp), fit_features(rp, rp)], axis=1)
    if v2:
        rp = add_field_rel(rp, FLD_REL_BASE)
    return rp


def _cls(series, classes):
    return pd.Categorical(series, categories=classes)


def predict(T, meta=None, booster=None, rp=None, rel_booster=None, co=None, clip='default', want_risk=False, src=None):
    """T: one row per runner to project, columns horse_id, date, jockey, venue, distance, going, weightCarried, barrier, field_size, race_class, trackGrading.
    Returns (formula projection, correction), both NaN where the horse has no earlier page run; with want_risk=True a third array: the chance of a bad run (rating more than
    risk.json bad_points below the formula figure, models_tr/risk_model.txt, projection/train_risk.py), NaN where there is no formula figure or no risk model. Horses with REL_MIN_RUNS or more earlier runs take the relevance model
    (models_tr/ctx_rel_model.txt) when it exists, the rest the plain context model."""
    import lightgbm as lgb
    meta = meta or json.load(open(os.path.join(M, 'ctx.json')))
    booster = booster or lgb.Booster(model_file=os.path.join(M, 'ctx_model.txt'))
    relf = os.path.join(M, 'ctx_rel_model.txt')
    if rel_booster is None and os.path.exists(relf) and meta.get('rel_feats'):
        rel_booster = lgb.Booster(model_file=relf)
    co = co or coefs()
    if rp is None:
        rp = page_frame()
        rp['f'] = formula_pred(rp, co)
        rp = context_columns(rp)
        rp['resid'] = rp.wpr - rp.f
    tab = jockey_table(rp)
    X = T.copy()
    X['date'] = pd.to_datetime(X.date)
    X['jockey'] = X.jockey.astype(str).where(X.jockey.notna(), '')
    X['going_n'] = going_num(X.going)
    X['grade'] = pd.to_numeric(X.trackGrading, errors='coerce')
    for c in ('distance', 'weightCarried', 'barrier', 'field_size'):
        X[c] = pd.to_numeric(X[c], errors='coerce')
    X['cls'] = class_code(X.race_class)
    X['vn'] = venue_key(X.venue) if 'venue' in X.columns else ''
    X['venue'] = X.vn
    X['lprize'] = np.log1p(pd.to_numeric(X['prize'], errors='coerce')) if 'prize' in X.columns else np.nan
    h = target_history(X, rp)
    X = pd.concat([X.drop(columns=[c for c in h.columns if c in X.columns]), h], axis=1)
    X['f'] = formula_pred(X, co, clip)
    X = context_columns(X)
    X = add_jockey(X, tab, targets=True)
    X = add_venue(X, rp)
    X = add_field(X)
    if 'jw' in meta.get('feats', FEATS):
        X = add_v2(X)
    if any(c in meta.get('feats', FEATS) + (meta.get('rel_feats') or []) for c in TRIAL_FEATS):
        X = pd.concat([X.drop(columns=[c for c in TRIAL_FEATS if c in X.columns]), trial_features(X)], axis=1)
    X['cls_c'] = _cls(X.cls, meta['classes'])
    corr = np.full(len(X), np.nan)
    ok = X.f.notna().values
    if ok.any() and any(c in EXT_NAMES for c in meta.get('feats', FEATS) + (meta.get('rel_feats') or [])):
        # extra inputs (10 Nov 2026, projection/ctx_ext.py): pedigree, finishing-position, trainer patterns, collateral form; the same builder as training,
        # computed over the runners with a formula figure (the population the field-relative columns compare within)
        import ctx_ext as EXT
        Xe = EXT.add_all(X.loc[ok], rp, src)
        X = pd.concat([X.drop(columns=[c for c in EXT.EXT_FEATS if c in X.columns]), Xe[EXT.EXT_FEATS].reindex(X.index)], axis=1)
    if ok.any():
        corr[ok] = booster.predict(X.loc[ok, meta.get('feats', FEATS)])
    if rel_booster is not None:
        use = ok & (X.n.values >= REL_MIN_RUNS)
        if use.any():
            fld = any(c in meta['rel_feats'] for c in FLD_REL_FEATS)
            # the field-relative columns compare a runner with every other runner that has relevance features, as in training (all page runs), so compute them for every runner with a figure
            Xr = X.loc[ok].copy() if fld else X.loc[use].copy()
            Xr = pd.concat([Xr, rel_features(Xr, rp)], axis=1)
            if fld:
                Xr = add_field_rel(Xr, FLD_REL_BASE)
                Xr = Xr.loc[X.loc[use].index]
            if any(c in meta['rel_feats'] for c in FIT_FEATS):
                Xr = pd.concat([Xr.drop(columns=[c for c in FIT_FEATS if c in Xr.columns]), fit_features(Xr, rp)], axis=1)
            if any(c in meta['rel_feats'] for c in SPD_FEATS):
                Xr = pd.concat([Xr, speed_features(Xr, rp)], axis=1)
            corr[use] = rel_booster.predict(Xr[meta['rel_feats']])
    if want_risk:
        risk = np.full(len(X), np.nan)
        rf, rm = os.path.join(M, 'risk_model.txt'), os.path.join(M, 'risk.json')
        if ok.any() and os.path.exists(rf) and os.path.exists(rm):
            rb = lgb.Booster(model_file=rf)
            risk[ok] = rb.predict(X.loc[ok, json.load(open(rm))['feats']])
        return X.f.values, corr, risk
    return X.f.values, corr
