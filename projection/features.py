"""As-of feature builder for the new WPR projection model.

One function builds every feature for a mix of past runs (outcome known) and target runs (races that have not
run yet, outcome blank). Everything is "as of the race date": a feature only uses runs strictly before the
target's date, so the same code gives identical features for a past run and for a future one.

Ported from the research scripts (miss_build.py, miss_build2.py, build_new2.py, build_sire_trial_latent.py,
build_text.py, build_trial3.py); projection/validate.py checks the port reproduces those features row for row.
"""
import glob
import json
import os

import numpy as np
import pandas as pd

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..'))
MODELS = os.path.join(os.path.dirname(__file__), 'models')

HIST_COLS = ['race_id', 'horse_id', 'date', 'track', 'distance', 'going', 'wpr', 'weightCarried', 'weight_allowance', 'barrier', 'field_size',
             'race_class', 'trackGrading', 'horse_age', 'horse_sex', 'jockey', 'trainer', 'positionFinish', 'marginFinish', 'priceStarting', 'position800m', 'margin800m',
             'isBarrierTrial', 'is_jumpout',
             # ladder-review features (Oct 2026): breeding, steward comments, sectionals, race-shape reads of past runs
             'sire_id', 'comments_steward', 'sect_i_time', 'sect_i_early', 'sect_i_l200', 'sect_i_l400', 'raceShapeEarly', 'raceShapeLate']


# Jumps races (hurdles and steeples) are rated on a different scale from the flat and are not projected (11 Oct 2026): their runs are left out of
# every history, and the projection step skips upcoming jumps races. race_class is 'Hurdle' or 'Steeple' in the results and runners files.
JUMPS_CLASSES = ('hurdle', 'steeple')


def is_jumps(race_class):
    return race_class.astype('string').str.strip().str.lower().isin(JUMPS_CLASSES).fillna(False)


def load_history():
    """Rated, non-trial runs from the results files (the same filter the research scripts used)."""
    x = pd.concat([pd.read_csv(f, usecols=lambda c: c in set(HIST_COLS), low_memory=False) for f in sorted(glob.glob(os.path.join(ROOT, 'race_results_20*.csv.gz')))], ignore_index=True)
    x = x[(~x.isBarrierTrial.astype(bool)) & (~x.is_jumpout.fillna(False).astype(bool)) & x.wpr.notna() & ~is_jumps(x.race_class)].drop_duplicates(['race_id', 'horse_id']).copy()
    x['date'] = pd.to_datetime(x['date'])
    x = x.drop(columns=['isBarrierTrial', 'is_jumpout'])
    x['is_target'] = 0
    return x


def _num(s):
    return pd.to_numeric(s.astype(str).str.extract(r'(\d+)')[0], errors='coerce')


def _asof_adv(x, keys, name, minn=2):
    """Horse's mean WPR in this going/distance/track band before today, relative to its career mean."""
    ks = ['horse_id'] + keys
    w = x.wpr.fillna(0.0)
    gg = w.groupby([x[k] for k in ks])
    cs = gg.cumsum() - w
    cn = x.groupby(ks, dropna=False).cumcount()
    x[name] = np.where(cn >= minn, cs / cn.clip(lower=1) - x.cm, np.nan)
    x[name + '_n'] = cn.clip(upper=15)


def _cum_table(x, keys, val='s'):
    a = x[keys + ['date', val]].dropna().groupby(keys + ['date'])[val].agg(['sum', 'count']).reset_index().sort_values(keys + ['date'])
    a['ci'] = a.groupby(keys)['sum'].cumsum()
    a['cni'] = a.groupby(keys)['count'].cumsum()
    return a


def _asof_merge(x, a, keys, cols, shift_days=0, exact=False, suffix=''):
    """For every row of x, the last row of cumulative table `a` with date < (date - shift_days) (or <= when exact)."""
    left = x[keys + ['date']].copy()
    left['_d'] = (left.date - pd.Timedelta(days=shift_days)).astype('datetime64[ns]')
    left['_i'] = np.arange(len(left))
    ok = left[keys].notna().all(axis=1)
    l2 = left[ok].sort_values('_d')
    r = a[keys + ['date'] + cols].copy()
    r['date'] = r.date.astype('datetime64[ns]')
    r = r.sort_values('date').rename(columns={'date': '_d'})
    for k in keys:  # merge_asof needs matching key dtypes
        if r[k].dtype != l2[k].dtype:
            r[k] = r[k].astype(l2[k].dtype)
    m = pd.merge_asof(l2, r, on='_d', by=keys, allow_exact_matches=exact)
    out = pd.DataFrame(index=np.arange(len(left)), columns=cols, dtype=float)
    out.loc[m['_i'].values, cols] = m[cols].values
    out.columns = [c + suffix for c in cols]
    return out.set_index(x.index)


def _table(x, keys, name, tables, store):
    if tables is not None and name in tables:
        return tables[name]
    a = _cum_table(x, keys)
    if store is not None:
        store[name] = a
    return a


def _eff(x, keys, name, k=20, cap=300, tables=None, store=None):
    """Shrunk mean of (wpr - exp) over prior rides for the key (jockey, trainer, jockey x distance...), strictly before today."""
    a = _table(x, keys, name, tables, store)
    m = _asof_merge(x, a, keys, ['ci', 'cni'])
    ok = x[keys].notna().all(axis=1)
    ci = m.ci.where(m.ci.notna() | ~ok, 0.0)
    cn = m.cni.where(m.cni.notna() | ~ok, 0.0)
    x[name] = ci / (cn + k)
    x[name + '_n'] = cn.clip(upper=cap)


def _form(x, key, name, days=90, k=10, tables=None, store=None):
    a = _table(x, [key], name, tables, store)
    now = _asof_merge(x, a, [key], ['ci', 'cni'])
    old = _asof_merge(x, a, [key], ['ci', 'cni'], shift_days=days, exact=True)
    ok = x[key].notna()
    ci1, cn1 = now.ci.where(now.ci.notna() | ~ok, 0.0), now.cni.where(now.cni.notna() | ~ok, 0.0)
    ci0, cn0 = old.ci.fillna(0.0), old.cni.fillna(0.0)
    n = (cn1 - cn0).clip(upper=200)
    x[name + '_n'] = n
    x[name] = (ci1 - ci0) / (n + k)


def build_main(X, levels, tables=None, store=None):
    """The 139 main-model features (minus text, trial and field-strength groups, added by their own functions)."""
    x = X.sort_values(['horse_id', 'date', 'race_id']).reset_index(drop=True).copy()
    g = x.groupby('horse_id')
    x['w1'] = g.wpr.shift(1)
    x['w2'] = g.wpr.shift(2)
    x['w3'] = g.wpr.shift(3)
    x['exp'] = g.wpr.transform(lambda s: s.shift(1).rolling(3, min_periods=2).mean())
    x['m5'] = g.wpr.transform(lambda s: s.shift(1).rolling(5, min_periods=3).mean())
    x['cm'] = g.wpr.transform(lambda s: s.shift(1).expanding(min_periods=3).mean())
    x['ff'] = x.positionFinish / x.field_size
    x['mg'] = x.marginFinish.clip(-5, 25)
    x['ff3'] = g.ff.transform(lambda s: s.shift(1).rolling(3, min_periods=2).mean())
    x['mg3'] = g.mg.transform(lambda s: s.shift(1).rolling(3, min_periods=2).mean())
    x['gap'] = (x.date - g.date.shift(1)).dt.days.clip(upper=200)
    x['nruns'] = g.cumcount().clip(upper=40)
    x['dist'] = x.distance
    # weight, age, sex
    x['wt'] = x.weightCarried
    x['wt_prev'] = g.wt.shift(1)
    x['wt_chg'] = x.wt - x.wt_prev
    x['wt_rel'] = x.wt - x.groupby('race_id').wt.transform('mean')
    x['sex'] = pd.Categorical(x.horse_sex, categories=levels['sex'])
    # class and track levels (learned on <=2022 and frozen)
    x['grade'] = x.trackGrading
    x['grade_prev'] = x.groupby('horse_id').trackGrading.shift(1)
    x['grade_chg'] = x.trackGrading - x.grade_prev
    x['cls_level'] = x.race_class.astype(object).map(levels['class'])
    x['cls_level_prev'] = x.groupby('horse_id').cls_level.shift(1)
    x['class_chg'] = x.cls_level - x.cls_level_prev
    x['track_level'] = x.track.map(levels['track'])
    # going
    x['going_num'] = _num(x.going)
    x['going_prev'] = x.groupby('horse_id').going_num.shift(1)
    x['going_chg'] = x.going_num - x.going_prev
    x['gb'] = pd.cut(x.going_num, [-1, 4, 7, 20], labels=['dry', 'soft', 'heavy']).astype(str)
    _asof_adv(x, ['gb'], 'going_adv')
    # distance and track
    x['dist_prev'] = x.groupby('horse_id').dist.shift(1)
    x['dist_chg'] = x.dist - x.dist_prev
    x['db'] = pd.cut(x.dist, [0, 1150, 1300, 1500, 1700, 1900, 2200, 2700, 9000], labels=False)
    _asof_adv(x, ['db'], 'dist_adv')
    _asof_adv(x, ['track'], 'track_adv')
    # trend and volatility
    g = x.groupby('horse_id')
    x['std5'] = g.wpr.transform(lambda s: s.shift(1).rolling(5, min_periods=3).std())
    x['max5'] = g.wpr.transform(lambda s: s.shift(1).rolling(5, min_periods=3).max())
    x['peak'] = g.wpr.transform(lambda s: s.shift(1).expanding(min_periods=3).max())
    x['d12'] = x.w1 - x.w2
    x['d13'] = x.w1 - x.w3
    # draw and field
    x['bf'] = (x.barrier - 1) / (x.field_size - 1).clip(lower=1)
    x['f_exp'] = x.groupby('race_id').exp.transform('mean')
    x['top_exp'] = x.groupby('race_id').exp.transform('max')
    if store is not None:
        store['race_agg'] = x.drop_duplicates('race_id').set_index('race_id')[['f_exp', 'top_exp']]
    if tables is not None and 'race_agg' in tables:  # past races' field strength comes from the cache (subset runs lack the other runners)
        ra = tables['race_agg']
        old = x.is_target.eq(0) if 'is_target' in x else pd.Series(False, index=x.index)
        x.loc[old, 'f_exp'] = x.loc[old, 'race_id'].map(ra.f_exp)
        x.loc[old, 'top_exp'] = x.loc[old, 'race_id'].map(ra.top_exp)
    x['exp_rel'] = x.exp - x.f_exp
    x['exp_rank'] = x.groupby('race_id').exp.rank(ascending=False, pct=True)
    x['exp_gap_top'] = x.top_exp - x.exp
    # jockey / trainer
    x['s'] = x.wpr - x.exp
    x['spell'] = ((x.gap > 60) | x.gap.isna()).astype(int)
    seg = x.groupby('horse_id').spell.cumsum()
    x['run_in_prep'] = (x.groupby(['horse_id', seg]).cumcount() + 1).clip(upper=4)
    x['fu'] = x.run_in_prep.clip(upper=3).astype(float)
    _eff(x, ['jockey'], 'jock_eff', 20, 500, tables=tables, store=store)
    _eff(x, ['trainer'], 'trn_eff', 20, 500, tables=tables, store=store)
    x['jock_prev'] = x.groupby('horse_id').jockey.shift(1)
    x['jock_chg'] = (x.jockey != x.jock_prev).astype(float).where(x.jock_prev.notna())
    x['jh_n'] = x.groupby(['horse_id', 'jockey']).cumcount().clip(upper=10)
    _eff(x, ['jockey', 'db'], 'jd_eff', 20, 300, tables=tables, store=store)
    _eff(x, ['jockey', 'trainer'], 'jt_eff', 10, 300, tables=tables, store=store)
    _eff(x, ['trainer', 'db'], 'td_eff', 20, 300, tables=tables, store=store)
    _eff(x, ['trainer', 'fu'], 'tfu_eff', 20, 300, tables=tables, store=store)
    _form(x, 'jockey', 'jock_form', tables=tables, store=store)
    _form(x, 'trainer', 'trn_form', tables=tables, store=store)
    # first-up / second-up record
    w = x.wpr.fillna(0.0)
    cs = w.groupby([x.horse_id, x.fu]).cumsum() - w
    cn = x.groupby(['horse_id', 'fu']).cumcount()
    x['fu_adv'] = np.where(cn >= 1, cs / cn.clip(lower=1) - x.cm, np.nan)
    x['fu_adv_n'] = cn.clip(upper=10)
    return x


def build_field(x):
    """Past-field strength: how strong the fields this horse recently beat were (needs f_exp, top_exp, exp_rel)."""
    b = x[['race_id', 'horse_id', 'date']].copy()
    b['beat'] = x.wpr - x.f_exp
    b['f_exp'], b['top_exp'], b['exp_rel'] = x.f_exp, x.top_exp, x.exp_rel
    g = b.groupby('horse_id')
    out = {}
    for c, n in [('f_exp', 'fs_fexp'), ('top_exp', 'fs_top'), ('beat', 'fs_beat'), ('exp_rel', 'fs_exprel')]:
        out[n + '3'] = g[c].transform(lambda s: s.shift(1).rolling(3, min_periods=2).mean())
        out[n + '1'] = g[c].shift(1)
    return pd.DataFrame(out, index=x.index)


def build_trials(x):
    """Barrier trial / jump-out features: days since the last trial, its result, trials in 90 days, and whether it came after the last run."""
    tc = pd.concat([pd.read_csv(f, usecols=['race_id', 'horse_id', 'date', 'positionFinish', 'marginFinish', 'field_size', 'isBarrierTrial', 'is_jumpout'], low_memory=False)
                    for f in sorted(glob.glob(os.path.join(ROOT, 'race_results_20*.csv.gz')))])
    tc = tc[(tc.isBarrierTrial.astype(bool)) | (tc.is_jumpout.fillna(False).astype(bool))].copy()
    tc['date'] = pd.to_datetime(tc['date'])
    tc['tf'] = ((tc.positionFinish - 1) / (tc.field_size - 1).clip(lower=1)).clip(0, 1)
    tc['tmg'] = tc.marginFinish.clip(-5, 25)
    tc = tc.sort_values(['horse_id', 'date']).drop_duplicates(['horse_id', 'date', 'race_id'])
    tc['cum'] = tc.groupby('horse_id').cumcount() + 1
    tc['horse_id'] = tc.horse_id.astype('int64')
    q = x[['race_id', 'horse_id', 'date', 'gap']].copy()
    q['horse_id'] = q.horse_id.astype('int64')
    q['d1'] = (q.date - pd.Timedelta(days=1)).astype('datetime64[ns]')
    q['d90'] = (q.date - pd.Timedelta(days=91)).astype('datetime64[ns]')
    q['_i'] = np.arange(len(q))
    b = tc[['horse_id', 'date', 'tf', 'tmg', 'cum']].rename(columns={'date': 'tdate'})
    b['d1'] = b.tdate.astype('datetime64[ns]')
    m = pd.merge_asof(q.sort_values('d1'), b.sort_values('d1'), on='d1', by='horse_id').rename(columns={'cum': 'cum_last'})
    b2 = b[['horse_id', 'd1', 'cum']].rename(columns={'d1': 'd90', 'cum': 'cum90'})
    m = pd.merge_asof(m.sort_values('d90'), b2.sort_values('d90'), on='d90', by='horse_id')
    m = m.sort_values('_i')
    out = pd.DataFrame(index=x.index)
    out['trial_days'] = (m.date - m.tdate).dt.days.clip(upper=400).values
    out['trial_fin_frac'] = m.tf.values
    out['trial_margin'] = m.tmg.values
    out['trial_n90'] = (m.cum_last.fillna(0) - m.cum90.fillna(0)).clip(lower=0).values
    out['trial_since_run'] = np.where(m.gap.notna() & m.tdate.notna(), (m.tdate > (m.date - pd.to_timedelta(m.gap, unit='D'))).astype(float), np.nan)
    return out


# ------------------------------------------------------------------ comment text (TF-IDF -> 30 SVD components)
def _comments(keys=None):
    parts = []
    for f in sorted(glob.glob(os.path.join(ROOT, 'race_results_20*.csv.gz'))):
        c = pd.read_csv(f, usecols=['race_id', 'horse_id', 'date', 'wpr', 'isBarrierTrial', 'is_jumpout', 'comments_steward', 'comments_video', 'race_class'], low_memory=False)
        c = c[(~c.isBarrierTrial.astype(bool)) & (~c.is_jumpout.fillna(False).astype(bool)) & c.wpr.notna() & ~is_jumps(c.race_class)]
        c['txt'] = (c.comments_video.astype('string').fillna('') + ' . ' + c.comments_steward.astype('string').fillna('')).str.lower().astype(str)
        c['date'] = pd.to_datetime(c['date'])
        parts.append(c[['race_id', 'horse_id', 'date', 'txt']])
    return pd.concat(parts).drop_duplicates(['race_id', 'horse_id']).reset_index(drop=True)


def fit_text(path=None):
    """Fit the TF-IDF + SVD on 300k pre-2023 comments (same recipe and seed as the research model) and save it."""
    import joblib
    from sklearn.decomposition import TruncatedSVD
    from sklearn.feature_extraction.text import TfidfVectorizer
    T = _comments()
    fit = T[(T.date < '2023-01-01') & (T.txt.str.len() > 8)].sample(300000, random_state=1)
    tf = TfidfVectorizer(max_features=30000, ngram_range=(1, 2), min_df=100, stop_words='english', sublinear_tf=True, dtype=np.float32)
    Xf = tf.fit_transform(fit.txt)
    svd = TruncatedSVD(30, random_state=1)
    svd.fit(Xf)
    if path:
        joblib.dump((tf, svd), path, compress=3)
    return tf, svd


def load_text(path=None):
    import joblib
    return joblib.load(path or os.path.join(MODELS, 'text_svd.joblib'))


def text_features(x, need, tf, svd):
    """last_tx0..29 (previous run's comment vector) and m3_tx0..29 (mean of the previous three). x must be sorted by horse, date;
    need = boolean mask of rows to compute (only their three predecessors are read and transformed)."""
    pos = np.arange(len(x))
    hid = x.horse_id.values
    idx = {}
    for k in (1, 2, 3):
        prev = pos - k
        ok = (prev >= 0)
        ok[ok] = hid[prev[ok]] == hid[ok]
        idx[k] = np.where(ok, prev, -1)
    needp = np.where(need.values)[0]
    union = np.unique(np.concatenate([idx[k][needp] for k in (1, 2, 3)]))
    union = union[union >= 0]
    T = _comments()
    key = x.iloc[union][['race_id', 'horse_id']].copy()
    key['_p'] = union
    key = key.merge(T[['race_id', 'horse_id', 'txt']], on=['race_id', 'horse_id'], how='left')
    txt = key.txt.fillna('')
    has = (txt.str.len() > 8).values
    V = np.full((len(key), 30), np.nan, dtype=np.float32)
    if has.any():
        V[has] = svd.transform(tf.transform(txt[has]))
    vec = {int(p): V[i] for i, p in enumerate(key._p.values)}
    nan = np.full(30, np.nan, dtype=np.float32)
    last = np.full((len(needp), 30), np.nan, dtype=np.float32)
    m3 = np.full((len(needp), 30), np.nan, dtype=np.float32)
    import warnings
    with warnings.catch_warnings():
        warnings.simplefilter('ignore')
        for r, i in enumerate(needp):
            vs = [vec.get(int(idx[k][i]), nan) if idx[k][i] >= 0 else nan for k in (1, 2, 3)]
            last[r] = vs[0]
            m3[r] = np.nanmean(np.stack(vs), axis=0)
    cols = [f'last_tx{i}' for i in range(30)] + [f'm3_tx{i}' for i in range(30)]
    out = pd.DataFrame(np.nan, index=x.index, columns=cols, dtype=float)
    out.iloc[needp] = np.hstack([last, m3])
    return out


# ------------------------------------------------------------------ normalised, typed trial / jump-out features
def build_trials3(x):
    """Last barrier trial and last jump-out: normalised speed (winner's speed for the track, distance and going), finish, margin,
    days since, trials in 30/60 days. Prefix t3_ = either kind, bt_ = barrier trial, jo_ = jump-out."""
    cols = ['race_id', 'horse_id', 'date', 'track', 'going', 'distance', 'winners_time', 'positionFinish', 'marginFinish', 'field_size', 'isBarrierTrial', 'is_jumpout']
    t = pd.concat([pd.read_csv(f, usecols=cols, low_memory=False) for f in sorted(glob.glob(os.path.join(ROOT, 'race_results_20*.csv.gz')))])
    t['date'] = pd.to_datetime(t['date']).astype('datetime64[ns]')
    t['gnum'] = _num(t.going)
    t['gb'] = pd.cut(t.gnum, [-1, 4, 7, 20], labels=['dry', 'soft', 'heavy']).astype(str)
    isjo = t.is_jumpout.fillna(False).astype(bool)
    isbt = t.isBarrierTrial.astype(bool) & ~isjo
    istr = isjo | isbt
    races = t[~istr].drop_duplicates('race_id').copy()
    races['spd'] = races.distance / races.winners_time
    races = races[(races.spd > 10) & (races.spd < 20)]
    races['db'] = (races.distance / 100).round()
    rt = races[races.date < '2024-01-01']
    E0 = rt.groupby('db').spd.mean()

    def hier(df, keys, parent, k=15):
        a = rt.groupby(keys).spd.agg(['sum', 'count']).reset_index()
        m = df[keys].merge(a, on=keys, how='left')
        w = (m['count'].fillna(0) / (m['count'].fillna(0) + k)).values
        cell = (m['sum'] / m['count']).values
        return np.where(np.isfinite(cell), w * cell + (1 - w) * parent, parent)

    def expected(df):
        d = df.copy()
        d['db'] = (d.distance / 100).round()
        p0 = d.db.map(E0).fillna(E0.mean()).values
        p1 = hier(d, ['track', 'db'], p0)
        return hier(d, ['track', 'db', 'gb'], p1)

    tc = t[istr].copy()
    tc['typ'] = np.where(isjo[istr], 'jo', 'bt')
    tc = tc.drop_duplicates(['horse_id', 'date', 'race_id']).sort_values(['horse_id', 'date']).reset_index(drop=True)
    tc['t_mg'] = tc.marginFinish.clip(-5, 25)
    tc['t_fin'] = ((tc.positionFinish - 1) / (tc.field_size - 1).clip(lower=1)).clip(0, 1)
    tc['wspd'] = tc.distance / tc.winners_time
    tc['hspd'] = tc.distance / (tc.winners_time + 0.146 * tc.t_mg.clip(lower=0))
    tc.loc[(tc.wspd < 8) | (tc.wspd > 20), ['wspd', 'hspd']] = np.nan
    tc['E'] = expected(tc)
    tc['wratio'] = tc.wspd / tc.E
    tc['hratio'] = tc.hspd / tc.E
    for c in ('wratio', 'hratio'):
        mu = tc[tc.date < '2024-01-01'].groupby('typ')[c].mean()
        tc[c + '_rel'] = tc[c] - tc.typ.map(mu)
    g = tc.groupby('horse_id')
    tc['p_hr'] = g.hratio_rel.shift(1)
    tc['m2_hr'] = g.hratio_rel.transform(lambda s: s.rolling(2, min_periods=1).mean())
    base = x[['race_id', 'horse_id', 'date', 'gap']].copy()
    base['date'] = base.date.astype('datetime64[ns]')
    base['horse_id'] = base.horse_id.astype('int64')
    base['_i'] = np.arange(len(base))

    def last_event(sub, pre, feats):
        sub = sub.sort_values(['horse_id', 'date']).copy()
        sub['horse_id'] = sub.horse_id.astype('int64')
        sub['cum'] = sub.groupby('horse_id').cumcount() + 1
        tt = base.copy()
        tt['d1'] = tt.date - pd.Timedelta(days=1)
        tt = tt.sort_values('d1')
        s = sub[['horse_id', 'date', 'cum'] + feats].rename(columns={'date': 'tdate'})
        s['d1'] = s.tdate
        m = pd.merge_asof(tt, s.sort_values('d1'), on='d1', by='horse_id')
        for days in (31, 61):
            b = s[['horse_id', 'd1', 'cum']].rename(columns={'d1': 'dd', 'cum': f'c{days}'}).sort_values('dd')
            mm = pd.merge_asof(tt.assign(dd=tt.date - pd.Timedelta(days=days)).sort_values('dd'), b, on='dd', by='horse_id')[['_i', f'c{days}']]
            m = m.merge(mm, on='_i', how='left')
            m[pre + f'n{days - 1}'] = (m.cum.fillna(0) - m[f'c{days}'].fillna(0)).clip(lower=0)
        m[pre + 'days'] = (m.date - m.tdate).dt.days.clip(upper=400)
        m[pre + 'to_run'] = np.where(m.gap.notna() & m.tdate.notna(), (m.tdate - (m.date - pd.to_timedelta(m.gap, unit='D'))).dt.days, np.nan)
        m = m.rename(columns={f: pre + f for f in feats}).sort_values('_i')
        return m[[pre + 'days', pre + 'to_run', pre + 'n30', pre + 'n60'] + [pre + f for f in feats]].reset_index(drop=True)

    out = last_event(tc, 't3_', ['t_fin', 't_mg', 'hratio', 'hratio_rel', 'wratio', 'wratio_rel', 'p_hr', 'm2_hr', 'distance'])
    for typ, pre in (('bt', 'bt_'), ('jo', 'jo_')):
        o = last_event(tc[tc.typ == typ], pre, ['t_fin', 't_mg', 'hratio_rel', 'wratio_rel'])
        out = pd.concat([out, o], axis=1)
    out.index = x.index
    return out


# ------------------------------------------------------------------ light-history extras (debut, 2nd and 3rd start)
def _level_eff(x, key, name, k, mask=None, tables=None, store=None):
    tn = 'lvl_' + name
    if tables is not None and tn in tables:
        a = tables[tn]
    else:
        sel = x[key].notna() & x.lvl.notna()
        if mask is not None:
            sel &= mask
        a = x.loc[sel, [key, 'date', 'lvl']].groupby([key, 'date']).lvl.agg(['sum', 'count']).reset_index().sort_values([key, 'date'])
        a['ci'] = a.groupby(key)['sum'].cumsum()
        a['cni'] = a.groupby(key)['count'].cumsum()
        if store is not None:
            store[tn] = a
    m = _asof_merge(x, a, [key], ['ci', 'cni'])
    x[name] = m.ci / (m.cni + k)
    x[name + '_n'] = m.cni.fillna(0).clip(upper=300)


def build_light(x, tables=None, store=None):
    """Own-history, trainer/jockey level effects and race-context features for horses with 0-2 prior rated runs (needs build_main output)."""
    out = pd.DataFrame(index=x.index)
    g = x.groupby('horse_id')
    ff = ((x.positionFinish - 1) / (x.field_size - 1).clip(lower=1)).clip(0, 1)
    mg = x.marginFinish.clip(-5, 25)
    out['ff1'] = ff.groupby(x.horse_id).shift(1)
    out['mg1'] = mg.groupby(x.horse_id).shift(1)
    out['mean_prev'] = g.wpr.transform(lambda s: s.shift(1).expanding(min_periods=1).mean())
    out['best_prev'] = g.wpr.transform(lambda s: s.shift(1).expanding(min_periods=1).max())
    out['is_maiden'] = x.race_class.astype(str).str.upper().str.startswith('MAI').astype(float)
    y = x[['horse_id', 'date', 'trainer', 'jockey', 'nruns']].copy()
    y['lvl'] = x.wpr - x.cls_level
    e2 = y.nruns <= 2
    e0 = y.nruns == 0
    for key, pre, ks in [('trainer', 'trn', (30, 15, 10)), ('jockey', 'jock', (30, 15, 10))]:
        _level_eff(y, key, pre + '_lvl', ks[0], tables=tables, store=store)
        _level_eff(y, key, pre + '_early_lvl', ks[1], e2, tables=tables, store=store)
        _level_eff(y, key, pre + '_debut_lvl', ks[2], e0, tables=tables, store=store)
    for c in [c for c in y.columns if c.endswith('_lvl') or c.endswith('_lvl_n')]:
        out[c] = y[c]
    return out


def build_pos_hist(x):
    """Settling-style history (x sorted by horse, date): average 800m position share and margin of the last three runs, and the horse's
    style relative to the other runners in the race."""
    p800f = (x.position800m - 1) / (x.field_size - 1).clip(lower=1)
    m800 = x.margin800m.clip(0, 40)
    g = x.groupby('horse_id')
    out = pd.DataFrame({'race_id': x.race_id.values, 'horse_id': x.horse_id.values}, index=x.index)
    out['pos_hist3'] = p800f.groupby(x.horse_id).transform(lambda s: s.shift(1).rolling(3, min_periods=2).mean())
    out['m800_hist3'] = m800.groupby(x.horse_id).transform(lambda s: s.shift(1).rolling(3, min_periods=2).mean())
    out['own_rel'] = out.pos_hist3 - out.groupby('race_id').pos_hist3.transform('mean')
    return out


# ------------------------------------------------------------------ suitability features (comments, finishing profile, jockey/trainer tendencies, day-of bias)
COMMENT_PATTERNS = {
    'held': r'held up|no clear run|not clear|denied a run|short of room|shuffled|no room|trapped|blocked|inconvenienc|crowded|steadied|checked|clipped heels|buffeted|tightened|raced three deep|forced wide|bumped|bumping',
    'wide': r'raced wide|three wide|four wide|wide throughout|wide on the turn|ran wide|drifted out|hung out|forced wide|laid out|lay out',
    'slow': r'slow(ly)? (to begin|away|out)|started slowly|missed the start|fumbled|dwelt|began awkwardly|stumbled',
    'fell_away': r'weakened|tired|faded|failed to sustain|fell away|ran out of',
    'lug': r'lugg?ed|shifted (in|out)|hung in|hung out|laid in|laid out|tongue'}
SUIT_COLS = ['date', 'track', 'race_id', 'horse_id', 'jockey', 'trainer', 'barrier', 'field_size', 'position800m', 'positionFinish', 'comments_steward', 'comments_video',
             'sect_i_l400', 'sect_i_l200', 'sect_i_early', 'sect_i_l600', 'isBarrierTrial', 'is_jumpout', 'race_class']


def load_results_all():
    """All non-trial runs (rated or not) with in-run positions, sectionals and comments, for the suitability features."""
    x = pd.concat([pd.read_csv(f, usecols=lambda c: c in set(SUIT_COLS), low_memory=False) for f in sorted(glob.glob(os.path.join(ROOT, 'race_results_20*.csv.gz')))]).drop_duplicates(['race_id', 'horse_id'])
    x = x[(x.isBarrierTrial != True) & (x.is_jumpout != True) & ~is_jumps(x.race_class)].drop(columns=['isBarrierTrial', 'is_jumpout', 'race_class']).copy()
    x['date'] = pd.to_datetime(x.date)
    return x[x.field_size >= 4]


def build_suit(Y, pos_hist, bias_since=None, tables=None, store=None):
    """Y: all-runs frame (history + target rows with blank outcomes; columns as SUIT_COLS) ; pos_hist: DataFrame race_id, horse_id, pos_hist3
    (the main model's settle-style history). Returns a frame indexed like Y with the suitability model's inputs."""
    x = Y.copy()
    x['raceNumber'] = x.groupby(['date', 'track']).race_id.rank(method='dense')
    x['fp'] = ((x.positionFinish - 1) / (x.field_size - 1)).clip(0, 1)
    x['p8'] = ((x.position800m - 1) / (x.field_size - 1)).clip(0, 1)
    x['bf'] = (x.barrier - 1) / (x.field_size - 1)
    txt = (x.comments_steward.fillna('') + ' ' + x.comments_video.fillna('')).str.lower()
    for k, p in COMMENT_PATTERNS.items():
        x['c_' + k] = txt.str.contains(p, regex=True).astype(float)
    x['has_cmt'] = (txt.str.len() > 3).astype(float)
    x = x.sort_values(['horse_id', 'date', 'race_id']).reset_index(drop=True)
    g = x.groupby('horse_id')
    for k in COMMENT_PATTERNS:
        x['h_' + k + '5'] = g['c_' + k].transform(lambda s: s.shift(1).rolling(5, min_periods=2).sum())
        x['h_' + k + 'rate'] = g['c_' + k].transform(lambda s: s.shift(1).expanding(min_periods=3).mean())
    x['h_cmtn'] = g['has_cmt'].transform(lambda s: s.shift(1).rolling(5, min_periods=1).sum())
    scols = ['sect_i_l400', 'sect_i_l200', 'sect_i_l600', 'sect_i_early']
    if tables is not None and 'sect_race' in tables:
        sr = tables['sect_race']
        rm = {c: x.race_id.map(sr[c]) for c in scols}
        for c in scols:   # races already in the cache keep their full-field mean; new races use their own runners
            own = x.groupby('race_id')[c].transform('mean')
            rm[c] = rm[c].where(rm[c].notna(), own)
    else:
        rm = {c: x.groupby('race_id')[c].transform('mean') for c in scols}
        if store is not None:
            store['sect_race'] = x.drop_duplicates('race_id').assign(**{c: rm[c][x.drop_duplicates('race_id').index] for c in scols}).set_index('race_id')[scols]
    for c in scols:
        x['fz_' + c] = x[c] - rm[c]
        x['h_' + c] = x.groupby('horse_id')['fz_' + c].transform(lambda s: s.shift(1).rolling(4, min_periods=2).mean())
    x['late_minus_early'] = x.h_sect_i_l400 - x.h_sect_i_early
    x = x.merge(pos_hist[['race_id', 'horse_id', 'pos_hist3']], on=['race_id', 'horse_id'], how='left')
    x.loc[x.field_size < 6, 'pos_hist3'] = np.nan  # the model was trained on fields of 6 or more
    x['dev'] = x.p8 - x.pos_hist3
    x = x.sort_values(['date', 'race_id']).reset_index(drop=True)
    pm = tables['p8_mean'] if tables is not None and 'p8_mean' in tables else x.p8.mean()
    if store is not None:
        store['p8_mean'] = pm
    for key, pre in [('jockey', 'j'), ('trainer', 't')]:
        for v, nm in [('p8', 'p8'), ('dev', 'dev')]:
            t = x[[key, 'date', v]].copy()
            t['ok'] = t[v].notna().astype(float)
            t['v0'] = t[v].fillna(0)
            tn = f'suit_{pre}_{nm}'
            if tables is not None and tn in tables:
                d = tables[tn]
            else:
                d = t.groupby([key, 'date'])[['v0', 'ok']].sum().reset_index().sort_values([key, 'date'])
                d['ci'] = d.groupby(key).v0.cumsum()
                d['cni'] = d.groupby(key).ok.cumsum()
                if store is not None:
                    store[tn] = d
            m = _asof_merge(x, d, [key], ['ci', 'cni'])
            ci, cn = m.ci.fillna(0.0), m.cni.fillna(0.0)
            x[f'{pre}_{nm}'] = (ci + 30 * (pm if nm == 'p8' else 0)) / (cn + 30)
            x[f'{pre}_{nm}_n'] = cn
    # day-of track bias from earlier races at the same meeting
    f = x[['date', 'track', 'raceNumber', 'fp', 'p8', 'bf']].copy()
    f['front'], f['back'], f['inb'], f['outb'] = f.p8 <= 0.33, f.p8 >= 0.67, f.bf <= 0.33, f.bf >= 0.67
    rows = []
    if bias_since is not None:
        f = f[f.date >= pd.Timestamp(bias_since)]
    for (d, tk), z in f.groupby(['date', 'track']):
        per = []
        for rn, zz in z.groupby('raceNumber'):
            fa = zz.fp[zz.front].mean() - zz.fp[zz.back].mean() if zz.front.any() and zz.back.any() else np.nan
            oa = zz.fp[zz.outb].mean() - zz.fp[zz.inb].mean() if zz.outb.any() and zz.inb.any() else np.nan
            per.append((rn, fa, oa))
        per = pd.DataFrame(per, columns=['rn', 'fa', 'oa'])
        per['fa_cum'] = per.fa.expanding().mean().shift(1)
        per['oa_cum'] = per.oa.expanding().mean().shift(1)
        per['fa_last'] = per.fa.rolling(2, min_periods=1).mean().shift(1)
        per['oa_last'] = per.oa.rolling(2, min_periods=1).mean().shift(1)
        per['n_prev'] = np.arange(len(per))
        per['date'], per['track'] = d, tk
        rows.append(per)
    if not rows:
        for c in ('fa_cum', 'oa_cum', 'fa_last', 'oa_last', 'n_prev'):
            x[c] = np.nan
        return x
    bias = pd.concat(rows).rename(columns={'rn': 'raceNumber'})
    x = x.merge(bias[['date', 'track', 'raceNumber', 'fa_cum', 'oa_cum', 'fa_last', 'oa_last', 'n_prev']], on=['date', 'track', 'raceNumber'], how='left')
    return x


# ------------------------------------------------------------------ ladder-review features (Oct 2026)
# One block per rung of the Factor Ladder Review that a held-out test (train < 2025, score 2025-01 onward) showed helping the main model;
# R3 (bad-run trim) and R14 (weight over WFA) did not help and are left out. Every feature is as-of: it reads only runs before the target.
LADDER_FEATURES = ['lad_r2', 'lad_r4', 'lad_r5', 'lad_r6', 'lad_r7', 'lad_r9',                       # recency base, then drift, going, wide, lead-in, pre-spell trim
                   'lad_r8_ff', 'lad_r8_win', 'lad_r8_top3',                                       # past placings
                   'lad_r10_job3', 'lad_r11_pvj3', 'lad_r11_pvj1',                                 # job difficulty, performance vs job
                   'lad_r12_l400', 'lad_r12_l200', 'lad_r12_early', 'lad_r12_time',                # sectional speed
                   'lad_r22_n_leaders', 'lad_r22_n_onpace', 'lad_r22_min', 'lad_r22_std', 'lad_r22_rank', 'lad_r22_lead_x_n',   # race shape
                   'lad_r25_dist', 'lad_r25_dist_rel', 'lad_r25_going', 'lad_r25_going_rel', 'lad_r25_both', 'lad_r25_both_rel',  # best rating at today's conditions
                   'lad_r26_stable_chg', 'lad_r27_sire', 'lad_r27_sire_n', 'lad_r27_sire_d', 'lad_r27_sire_g',
                   'lad_r29_pe1', 'lad_r29_pe3', 'lad_c2_lp1', 'lad_c2_lp3',                       # market expectation / price level at past starts
                   'lad_r30_pos3', 'lad_r30_own_rel', 'lad_r30_m800']                              # settle map


def _shifts(g, col, n=10):
    return np.column_stack([g[col].shift(k).values for k in range(1, n + 1)])


def _wavg(A, w=None, minn=2):
    n = A.shape[1]
    base = 1.0 / np.arange(1, n + 1)
    W = np.broadcast_to(base, A.shape) if w is None else w * base
    ok = ~np.isnan(A)
    num = np.nansum(np.where(ok, A, 0.0) * W, axis=1)
    den = (ok * W).sum(1)
    return np.where(ok.sum(1) >= minn, num / np.where(den > 0, den, 1.0), np.nan)


def _nanmean(A, minn=1):
    ok = (~np.isnan(A)).sum(1)
    return np.where(ok >= minn, np.nansum(A, axis=1) / np.maximum(ok, 1), np.nan)


def build_ladder(x, ph=None, tables=None, store=None):
    """The ladder-review features (needs build_main output; x carries the history columns added to HIST_COLS). Indexed like x."""
    info = json.load(open(os.path.join(MODELS, 'ladder.json')))
    out = pd.DataFrame(index=x.index)
    g = x.groupby('horse_id')
    ds = (x.date - pd.Timestamp('2000-01-01')).dt.days.astype(float)
    today = ds.values
    W = _shifts(g, 'wpr')
    D = _shifts(x.assign(_d=ds).groupby('horse_id'), '_d')
    nxt = np.column_stack([today] + [D[:, k] for k in range(9)])
    spell_after = (nxt - D) > 60                                    # run followed by a spell (gap to the next run, or to today, over 60 days)
    # ---- R2 recency, R4 drift, R5 going, R6 wide-run credit, R7 lead-in credit, R9 pre-spell trim (cumulative, as in the ladder, without R3)
    out['lad_r2'] = _wavg(W)
    A = W + 0.005 * (today[:, None] - D)
    out['lad_r4'] = _wavg(A)
    A = A + info['going_slope'] * (x.going_num.values[:, None] - _shifts(g, 'going_num'))
    out['lad_r5'] = _wavg(A)
    wide = x.comments_steward.fillna('').str.contains(COMMENT_PATTERNS['wide'], case=False, regex=True).astype(float)
    A = A + 2.19 * np.nan_to_num(np.column_stack([wide.groupby(x.horse_id).shift(k).values for k in range(1, 11)]))
    out['lad_r6'] = _wavg(A)
    RP = _shifts(g, 'run_in_prep')
    A = A + np.where(RP == 1, 1.5, np.where(RP == 2, 0.75, 0.0))
    out['lad_r7'] = _wavg(A)
    usual = _wavg(A)[:, None]
    out['lad_r9'] = _wavg(A, np.where(spell_after & (A <= usual - 3.0), 0.5, 1.0))
    # ---- past finishing / margin / price reads
    ff = ((x.positionFinish - 1) / (x.field_size - 1).clip(lower=1)).clip(0, 1)
    ffg = ff.groupby(x.horse_id)
    FF = np.column_stack([ffg.shift(k).values for k in range(1, 11)])
    PF = _shifts(g, 'positionFinish')
    out['lad_r8_ff'] = _wavg(FF)
    out['lad_r8_win'] = _wavg(np.where(np.isnan(PF), np.nan, (PF == 1).astype(float)))
    out['lad_r8_top3'] = _wavg(np.where(np.isnan(PF), np.nan, (PF <= 3).astype(float)))
    for c, nm in [('sect_i_l400', 'l400'), ('sect_i_l200', 'l200'), ('sect_i_early', 'early'), ('sect_i_time', 'time')]:
        out['lad_r12_' + nm] = _nanmean(_shifts(g, c, 4), 2)
    # ---- best rating at today's distance / going band (cummax of earlier runs), relative to the career mean
    w = x.wpr.fillna(-np.inf)
    for nm, keys in [('dist', ['db']), ('going', ['gb']), ('both', ['db', 'gb'])]:
        kk = [x.horse_id] + [x[k] for k in keys]
        best = w.groupby(kk, dropna=False).cummax().groupby(kk, dropna=False).shift(1).replace(-np.inf, np.nan)
        out['lad_r25_' + nm] = best
        out['lad_r25_' + nm + '_rel'] = best - x.cm
    # ---- stable change
    pt = g.trainer.shift(1)
    out['lad_r26_stable_chg'] = np.where(pt.notna() & x.trainer.notna(), (pt != x.trainer).astype(float), np.nan)
    # ---- sire (a horse's sire is constant: runners with no sire on the row take it from their earlier runs)
    smap = x.dropna(subset=['sire_id']).drop_duplicates('horse_id', keep='last').set_index('horse_id').sire_id
    Rs = x[['horse_id', 'date', 'race_id', 'db', 'gb', 's', 'nruns']].copy()
    Rs['sire_id'] = x.sire_id.fillna(x.horse_id.map(smap)).astype(float)
    _eff(Rs, ['sire_id'], 'sire_eff', 30, 3000, tables=tables, store=store)
    _eff(Rs, ['sire_id', 'db'], 'sire_d_eff', 20, 1000, tables=tables, store=store)
    _eff(Rs, ['sire_id', 'gb'], 'sire_g_eff', 20, 1000, tables=tables, store=store)
    fade = 1.0 - 0.5 * (Rs.nruns.clip(upper=30) / 30.0)
    out['lad_r27_sire'] = Rs.sire_eff * fade
    out['lad_r27_sire_n'] = Rs.sire_eff_n
    out['lad_r27_sire_d'] = Rs.sire_d_eff * fade
    out['lad_r27_sire_g'] = Rs.sire_g_eff * fade
    # ---- market expectation and price level at the last starts (price rank within each past race: from the cache when only some runners are loaded)
    sp = x.priceStarting.where(x.priceStarting > 1)
    if tables is not None and 'prk' in tables:
        prk = pd.Series(tables['prk'].reindex(pd.MultiIndex.from_arrays([x.race_id.values, x.horse_id.values])).values, index=x.index)
    else:
        prk = (1.0 / sp).groupby(x.race_id).rank(ascending=False, pct=True)         # 0 = shortest price in the race
        if store is not None:
            store['prk'] = prk[x.is_target.eq(0)].set_axis(pd.MultiIndex.from_arrays([x.race_id[x.is_target.eq(0)].values, x.horse_id[x.is_target.eq(0)].values]))
    lpg = np.log(sp).groupby(x.horse_id)
    LP = np.column_stack([lpg.shift(k).values for k in range(1, 4)])
    PR = np.column_stack([prk.groupby(x.horse_id).shift(k).values for k in range(1, 4)])
    FF3 = FF[:, :3]
    out['lad_c2_lp1'] = LP[:, 0]
    out['lad_c2_lp3'] = _nanmean(LP)
    out['lad_r29_pe1'] = FF3[:, 0] - PR[:, 0]            # positive = finished further back than its price said
    out['lad_r29_pe3'] = _nanmean(FF3 - PR)
    # ---- settle map and race shape from the field's own settling history
    if ph is None:
        ph = build_pos_hist(x)
    p = ph.pos_hist3
    out['lad_r30_pos3'] = p
    out['lad_r30_own_rel'] = ph.own_rel
    out['lad_r30_m800'] = ph.m800_hist3
    pg = p.groupby(x.race_id)
    out['lad_r22_n_leaders'] = (p < 0.25).groupby(x.race_id).transform('sum')
    out['lad_r22_n_onpace'] = (p < 0.40).groupby(x.race_id).transform('sum')
    out['lad_r22_min'] = pg.transform('min')
    out['lad_r22_std'] = pg.transform('std')
    out['lad_r22_rank'] = pg.rank(pct=True)
    out['lad_r22_lead_x_n'] = (p < 0.25).astype(float) * out.lad_r22_n_leaders
    # ---- job difficulty and performance vs job of past runs (tempo and position; the 'expected finish' model is frozen in models/pvj_model.txt)
    front = 1 - ((x.position800m - 1) / (x.field_size - 1).clip(lower=1))
    jd = (x.raceShapeEarly * front)
    out['lad_r10_job3'] = _nanmean(np.column_stack([jd.groupby(x.horse_id).shift(k).values for k in range(1, 4)]))
    Z = pd.DataFrame({'p8': 1 - front, 'm8': x.margin800m.clip(0, 40), 'se': x.raceShapeEarly, 'sl': x.raceShapeLate, 'bf': x.bf})
    okz = Z.notna().all(axis=1) & ff.notna()
    import lightgbm as lgb
    pe = pd.Series(np.nan, index=x.index)
    if okz.any():
        pe[okz] = lgb.Booster(model_file=os.path.join(MODELS, 'pvj_model.txt')).predict(Z[okz]) - ff[okz]    # positive = finished ahead of what the job predicted
    PE = np.column_stack([pe.groupby(x.horse_id).shift(k).values for k in range(1, 4)])
    out['lad_r11_pvj3'] = _nanmean(PE)
    out['lad_r11_pvj1'] = PE[:, 0]
    return out[LADDER_FEATURES]
