"""Context correction for the formula Proj (21 Oct 2026). ATW figures only: every rating read here is a runner-page rating as TopRate gives it
(`features.runner_page_runs()`, weight adjusted to the horse's next start); nothing from the results files and no plain-scale WPR (owner rule).

Proj = formula (models_tr/formula.json) + a LightGBM correction learned from context (models_tr/ctx_model.txt, ctx.json): distance and its change, going and its
change, class code, track grading, field size, barrier fraction, weight carried and its change, days since the last run, the last run's margin and finish, the spread
of the last four ratings, and the jockey's effect as of the day (shrunk mean formula residual of the jockey's earlier page runs). Trained by train_ctx.py.
`predict(T)` is the live path: T has one row per runner to project; history is the runner-page store strictly before each row's date."""
import json
import os

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
FEATS = ['f', 'n', 'mean3', 'max4', 'std4', 'ldays', 'distance', 'dist_chg', 'going_n', 'going_chg', 'grade', 'field_size', 'barr_f', 'weightCarried', 'wt_chg',
         'l_mgn', 'l_posf', 'jock_eff', 'cn', 'cls_c']


LAG_NAMES = [f'{nm}{k}' for k in range(1, LAGS + 1) for nm in ('dd', 'gd', 'trk', 'jk', 'cl', 'wd', 'dg', 'mg', 'pf', 'dev')]
CAR_NAMES = ['c_mean', 'c_max', 'c_sd', 'c_ewm3', 'c_near', 'c_vs_f', 'cmax_vs_f']
SIM_NAMES = ['sim_dist', 'sim_going', 'sim_track', 'sim_jock', 'sim_class', 'sim_days', 'sim_all']
OWN_NAMES = ['h_dist', 'h_dist_n', 'h_going', 'h_going_n', 'h_track', 'h_track_n', 'h_spell', 'h_spell_n', 'h_jock', 'h_jock_n']
REL_FEATS = LAG_NAMES + CAR_NAMES + SIM_NAMES + OWN_NAMES


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


def venue_key(s):
    return s.astype(str).str.lower().str.replace(r'[^a-z0-9]+', ' ', regex=True).str.strip()


def going_group(g):
    """Going number to 0 (3 or less, firm and good), 1 (Good 4), 2 (5 to 7, soft), 3 (8+, heavy); -1 unknown."""
    g = np.asarray(g, dtype=float)
    return np.where(np.isnan(g), -1, np.digitize(np.nan_to_num(g, nan=-9), [3.5, 4.5, 7.5]))


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
    rp = rp.sort_values(['horse_id', 'date']).reset_index(drop=True)
    g = rp.groupby('horse_id')
    for k in range(1, K + 1):
        rp[f'r{k}'] = g.wpr.shift(k)
    rp['n'] = g.cumcount().astype(float)
    rp['d_last'] = (rp.date - g.date.shift(1)).dt.days.astype(float)
    rp['l_dist'], rp['l_going'], rp['l_wt'], rp['l_mgn'] = g.distance.shift(1), g.going_n.shift(1), g.weightCarried.shift(1), g.marginFinish.shift(1)
    rp['l_posf'] = (rp.positionFinish / rp.field_size).groupby(rp.horse_id).shift(1)
    return rp


def target_history(T, rp):
    """The same history features for the rows to project: the horse's page runs strictly before the row's date."""
    byh = {h: x for h, x in rp.groupby('horse_id')}
    cols = [f'r{k}' for k in range(1, K + 1)] + ['n', 'd_last', 'l_dist', 'l_going', 'l_wt', 'l_mgn', 'l_posf']
    out = np.full((len(T), len(cols)), np.nan)
    out[:, cols.index('n')] = 0.0
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
    return pd.DataFrame(out, columns=cols, index=T.index)


def formula_pred(df, co):
    f = np.full(len(df), np.nan)
    kk = df.n.clip(upper=K).values
    for n in range(1, K + 1):
        m = kk == n
        c = [f'r{k}' for k in range(1, n + 1)]
        X = df.loc[m, c].values
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
    df['dist_chg'] = df.distance - df.l_dist
    df['going_chg'] = df.going_n - df.l_going
    df['wt_chg'] = df.weightCarried - df.l_wt
    df['barr_f'] = df.barrier / df.field_size
    df['ldays'] = np.log1p(df.d_last)
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
        byh[h] = dict(d=x.date.values.astype('datetime64[D]').astype('int64'), w=x.wpr.values, dist=x.distance.values, gn=x.going_n.values, wt=x.weightCarried.values,
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
        R = a['w'][sl][::-1]
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
        w_all = a['w'][:j]
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


def training_frame():
    """Page runs with formula, residual and every context feature (training rows: runs with at least one earlier run)."""
    co = coefs()
    rp = page_frame()
    rp['f'] = formula_pred(rp, co)
    rp = context_columns(rp)
    rp['resid'] = rp.wpr - rp.f
    rp = add_jockey(rp, jockey_table(rp))
    return rp


def training_frame_rel():
    """training_frame plus the relevance features (rel_features run on the page runs themselves, history strictly before each run's date)."""
    rp = training_frame()
    return pd.concat([rp, rel_features(rp, rp)], axis=1)


def _cls(series, classes):
    return pd.Categorical(series, categories=classes)


def predict(T, meta=None, booster=None, rp=None, rel_booster=None):
    """T: one row per runner to project, columns horse_id, date, jockey, venue, distance, going, weightCarried, barrier, field_size, race_class, trackGrading.
    Returns (formula projection, correction), both NaN where the horse has no earlier page run. Horses with REL_MIN_RUNS or more earlier runs take the relevance model
    (models_tr/ctx_rel_model.txt) when it exists, the rest the plain context model."""
    import lightgbm as lgb
    meta = meta or json.load(open(os.path.join(M, 'ctx.json')))
    booster = booster or lgb.Booster(model_file=os.path.join(M, 'ctx_model.txt'))
    relf = os.path.join(M, 'ctx_rel_model.txt')
    if rel_booster is None and os.path.exists(relf) and meta.get('rel_feats'):
        rel_booster = lgb.Booster(model_file=relf)
    co = coefs()
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
    h = target_history(X, rp)
    X = pd.concat([X.drop(columns=[c for c in h.columns if c in X.columns]), h], axis=1)
    X['f'] = formula_pred(X, co)
    X = context_columns(X)
    X = add_jockey(X, tab, targets=True)
    X['cls_c'] = _cls(X.cls, meta['classes'])
    corr = np.full(len(X), np.nan)
    ok = X.f.notna().values
    if ok.any():
        corr[ok] = booster.predict(X.loc[ok, FEATS])
    if rel_booster is not None:
        use = ok & (X.n.values >= REL_MIN_RUNS)
        if use.any():
            Xr = X.loc[use].copy()
            Xr = pd.concat([Xr, rel_features(Xr, rp)], axis=1)
            corr[use] = rel_booster.predict(Xr[meta['rel_feats']])
    return X.f.values, corr
