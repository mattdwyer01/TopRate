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
# Venue effect (22 Oct 2026, owner's call, research/venue_feature_test.py): shrunk mean formula residual of the venue's page runs in [date - 186 days, date - 6 days).
# The newest 6 days are left out because a page rating for a run a few days old can still be Preliminary live but is Final in the training history.
# Held-out 2026 (35,081 runs): paired MSE gain +0.158 (95% +0.082 to +0.232) at K 200, against +0.143 at K 100 and +0.084 at K 50.
VEN_K, VEN_WINDOW, VEN_GAP = 200.0, 180, 6
FEATS = ['f', 'n', 'mean3', 'max4', 'std4', 'ldays', 'distance', 'dist_chg', 'going_n', 'going_chg', 'grade', 'field_size', 'barr_f', 'weightCarried', 'wt_chg',
         'l_mgn', 'l_posf', 'jock_eff', 'cn', 'cls_c', 'ven_eff']


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
    rp['venue'] = venue_key(rp.venue)
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
    rc = F.clip_low_lags(df[[f'r{k}' for k in range(1, K + 1)]].values, clip_low())   # outlier trim, same as features.formula_projection
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


def training_frame():
    """Page runs with formula, residual and every context feature (training rows: runs with at least one earlier run)."""
    co = coefs()
    rp = page_frame()
    rp['f'] = formula_pred(rp, co)
    rp = context_columns(rp)
    rp['resid'] = rp.wpr - rp.f
    rp = add_jockey(rp, jockey_table(rp))
    rp = add_venue(rp, rp)
    return rp


def _cls(series, classes):
    return pd.Categorical(series, categories=classes)


def predict(T, meta=None, booster=None, rp=None):
    """T: one row per runner to project, columns horse_id, date, jockey, distance, going, weightCarried, barrier, field_size, race_class, trackGrading.
    Returns (formula projection, correction), both NaN where the horse has no earlier page run."""
    import lightgbm as lgb
    meta = meta or json.load(open(os.path.join(M, 'ctx.json')))
    booster = booster or lgb.Booster(model_file=os.path.join(M, 'ctx_model.txt'))
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
    X['venue'] = venue_key(X.venue) if 'venue' in X.columns else ''
    h = target_history(X, rp)
    X = pd.concat([X.drop(columns=[c for c in h.columns if c in X.columns]), h], axis=1)
    X['f'] = formula_pred(X, co)
    X = context_columns(X)
    X = add_jockey(X, tab, targets=True)
    X = add_venue(X, rp)
    X['cls_c'] = _cls(X.cls, meta['classes'])
    corr = np.full(len(X), np.nan)
    ok = X.f.notna().values
    if ok.any():
        corr[ok] = booster.predict(X.loc[ok, FEATS])
    return X.f.values, corr
