"""Proj retrained for the top 3 and for tight shortlists (27 Oct 2026).
Objective: a Plackett-Luce loss over the first three finishers (1st, then 2nd among the rest, then 3rd), so the score is trained to put the real top 3 at the top of the field,
instead of the run's rating. The score is turned into a rating on the ATW scale (race mean of the Proj stand-in plus a scaled, race-centred score); the scale is then chosen
on 2024 H2 by looking at shortlists within 2 / 4 rating points of the top rated runner: as many winners (and placegetters) as possible inside the lines for as few runners as possible.
Inputs: results-file history converted to the page ATW scale per target race (AR 168), as in the converted-history Proj. Two input sets: AFE (the Proj's own kind of inputs)
and V3A (adds jockey/trainer rates and field-relative inputs). T1 = 2025 full fields; T2 = the daily log's complete real fields with the dashboard Proj.
  PYTHONPATH=.:projection:research python research/proj_top3_retrain.py   (needs /tmp/direct_ctx_feats.pkl from the direct-v3 artifact)"""
import glob, gzip, json, os, re, sys
import lightgbm as lgb, numpy as np, pandas as pd
from scipy.optimize import minimize
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'projection'))
import wfa_scale as W
import ctx as C
import features as FT

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SEX = {'G': 0, 'M': 1, 'F': 2, 'C': 3, 'H': 4, 'R': 5}


def nk(x):
    if not isinstance(x, str):
        return None
    t = re.sub(r"[^A-Za-z\s'-]", '', x).split()
    return (t[0][0] + t[-1]).lower().replace("'", '').replace('-', '') if t else None


def asof_rate(df, key, value, window_days=None, prior=0.1, k=50):
    v = df[value]
    t = pd.DataFrame({'key': df[key].values, 'date': df.date.values, 'v': v.values}).dropna(subset=['key', 'v'])
    a = t.groupby(['key', 'date']).v.agg(['sum', 'count']).reset_index().sort_values(['key', 'date'])
    a['cs'] = a.groupby('key')['sum'].cumsum()
    a['cn'] = a.groupby('key')['count'].cumsum()
    q = pd.DataFrame({'key': df[key].values, 'date': df.date.values, '_i': np.arange(len(df))}).dropna(subset=['key'])
    m = pd.merge_asof(q.sort_values('date'), a[['key', 'date', 'cs', 'cn']].sort_values('date'), on='date', by='key', allow_exact_matches=False)
    cs, cn = m.cs.fillna(0).values, m.cn.fillna(0).values
    if window_days:
        q2 = q.assign(date=q.date - pd.Timedelta(days=window_days))
        m2 = pd.merge_asof(q2.sort_values('date'), a[['key', 'date', 'cs', 'cn']].sort_values('date'), on='date', by='key', allow_exact_matches=False)
        cs, cn = cs - m2.cs.fillna(0).values, cn - m2.cn.fillna(0).values
    out = np.full(len(df), np.nan)
    out[m._i.values] = (cs + prior * k) / (cn + k)
    return out


cols = ['race_id', 'horse_id', 'date', 'distance', 'going', 'wpr', 'weightCarried', 'barrier', 'marginFinish', 'positionFinish', 'position800m', 'race_class', 'jockey', 'trainer',
        'venue', 'horse_age', 'horse_sex', 'horse_foaled', 'isBarrierTrial', 'is_jumpout', 'priceStarting']
fs = sorted(glob.glob(os.path.join(ROOT, 'race_results_20[12]?.csv.gz')))
r = pd.concat([pd.read_csv(f, usecols=lambda c: c in cols, low_memory=False) for f in fs], ignore_index=True)
r = r[~r.isBarrierTrial.astype(bool) & ~r.is_jumpout.fillna(False).astype(bool)]
r['date'] = pd.to_datetime(r.date)
r = r[(r.date >= '2019-06-01') & (r.date <= '2025-12-31')].drop_duplicates(['race_id', 'horse_id']).sort_values(['horse_id', 'date', 'race_id']).reset_index(drop=True)
r['horse_id'] = pd.to_numeric(r.horse_id, errors='coerce').astype(float)
r['nr'] = r.groupby('race_id').horse_id.transform('size')
r['pos'] = pd.to_numeric(r.positionFinish, errors='coerce')
r['gs'] = pd.to_numeric(r.going.astype(str).str.extract(r'(\d+)')[0], errors='coerce')
r['finpct'] = (r.pos - 1) / (r.nr - 1)
r['mfin'] = pd.to_numeric(r.marginFinish, errors='coerce').clip(0, 30)
r['barfrac'] = (r.barrier - 1) / (r.nr - 1)
r['sex'] = r.horse_sex.astype(str).str.upper().str[:1].map(SEX)
r['wpr'] = pd.to_numeric(r.wpr, errors='coerce')
r['clsc'] = C.class_code(r.race_class)
r['jk'], r['tk'] = r.jockey.map(nk), r.trainer.map(nk)
r['winf'] = np.where(r.pos.notna(), (r.pos == 1).astype(float), np.nan)
r['e0'] = pd.to_numeric(r.position800m, errors='coerce') / r.nr
vmap = {v: C.venue_key(pd.Series([v])).iloc[0] for v in r.venue.dropna().unique()}
r['vk'] = r.venue.map(vmap)


def offs(df):
    out = np.full(len(df), np.nan)
    for i, x in enumerate(df.itertuples()):
        if pd.isna(x.distance) or pd.isna(x.weightCarried):
            continue
        age = W.racing_age(x.horse_foaled, x.date) if isinstance(x.horse_foaled, str) and len(x.horse_foaled) >= 10 else (None if pd.isna(x.horse_age) else int(x.horse_age))
        v = W.atw_offset(age, str(x.horse_sex).upper()[:1], x.date.date(), float(x.distance), x.weightCarried)
        if v is not None:
            out[i] = v
    return out


print('shifts, rates, shape, draw for', len(r), 'runs ...', flush=True)
r['c_t'] = offs(r)
r['jw'] = asof_rate(r, 'jk', 'winf')
r['jw90'] = asof_rate(r, 'jk', 'winf', window_days=90, k=30)
r['tw'] = asof_rate(r, 'tk', 'winf')
r['tw90'] = asof_rate(r, 'tk', 'winf', window_days=90, k=30)
# draw by track: as-of finishing share of the barrier third at venue x distance band, against the venue x band average
r['third'] = np.minimum((r.barfrac * 3).fillna(1).astype(int), 2)
r['dband'] = (r.distance / 200).round()
r['dall'] = r.vk.astype(str) + '|' + r.dband.astype(str)
r['dk'] = r.dall + '|' + r.third.astype(str)
r['draw_eff'] = asof_rate(r, 'dk', 'finpct', prior=0.5, k=100) - asof_rate(r, 'dall', 'finpct', prior=0.5, k=100)
g = r.groupby('horse_id')
lw = pd.concat([g.wpr.shift(k) for k in range(1, 9)], axis=1)
ct = r.c_t.fillna(0.0)
lpos = pd.concat([g.pos.shift(k) for k in range(1, 9)], axis=1)
F = {}
for k in range(6):
    F[f'w{k + 1}'] = lw.iloc[:, k] + ct
F['m3_wpr'] = lw.iloc[:, :3].mean(axis=1) + ct
F['m8_wpr'] = lw.mean(axis=1) + ct
F['max8_wpr'] = lw.max(axis=1) + ct
F['s8_wpr'] = lw.std(axis=1)
F['trend'] = F['w1'] - F['m8_wpr']
for c in ('mfin', 'finpct'):
    lg = pd.concat([g[c].shift(k) for k in range(1, 5)], axis=1)
    F['p1_' + c] = lg.iloc[:, 0]
    F['m4_' + c] = lg.mean(axis=1)
F['win8'] = (lpos == 1).sum(axis=1).where(lpos.notna().any(axis=1)) / lpos.notna().sum(axis=1).replace(0, np.nan)
F['plc8'] = (lpos <= 3).sum(axis=1).where(lpos.notna().any(axis=1)) / lpos.notna().sum(axis=1).replace(0, np.nan)
F['days'] = g.date.diff().dt.days
F['wchg'] = r.weightCarried - g.weightCarried.shift(1)
F['dchg'] = r.distance - g.distance.shift(1)
F['n_runs'] = g.cumcount().astype(float).clip(upper=12)
F['cls_same'] = (r.clsc == g.clsc.shift(1)).astype(float).where(g.clsc.shift(1).notna())
F['jock_chg'] = (r.jk != g.jk.shift(1)).astype(float).where(g.jk.shift(1).notna() & r.jk.notna())
# shape history
le = pd.concat([g.e0.shift(k) for k in range(1, 5)], axis=1)
late = (r.e0 - r.finpct)
ll_ = pd.concat([late.groupby(r.horse_id).shift(k) for k in range(1, 5)], axis=1)
F['e1'] = le.iloc[:, 0]
F['e_m4'] = le.mean(axis=1)
F['e_min4'] = le.min(axis=1)
F['close4'] = ll_.mean(axis=1)
F = pd.DataFrame(F)
d = pd.concat([r, F], axis=1)
d['win'] = (d.pos == 1).astype(float)
d['top3'] = (d.pos <= 3).astype(float)
CTX = pd.read_pickle('/tmp/direct_ctx_feats.pkl')
CTX['horse_id'] = CTX.horse_id.astype(float)
CTX['date'] = pd.to_datetime(CTX.date).astype('datetime64[ns]')
d['date'] = d.date.astype('datetime64[ns]')
CTX = CTX.drop_duplicates(['horse_id', 'date'])
DROP = {'x_distance', 'x_going_n', 'x_field_size', 'x_weightCarried', 'x_barr_f', 'x_dist_chg', 'x_wt_chg', 'x_lprize', 'x_prize_chg', 'x_n', 'x_mean3', 'x_cn'}
XC = [c for c in CTX.columns if c.startswith('x_') and c not in DROP and CTX[c].notna().any()]
d = d.merge(CTX[['horse_id', 'date'] + XC].astype({c: 'float32' for c in XC}), on=['horse_id', 'date'], how='left')
print('ctx features', len(XC), 'matched', d.x_f.notna().mean().round(3), flush=True)
CLASSES = d.loc[d.date < '2024-07-01', 'clsc'].value_counts()
CLASSES = CLASSES[CLASSES >= 200].index.tolist()

BASE2 = [f'w{k}' for k in range(1, 7)] + ['m3_wpr', 'm8_wpr', 'max8_wpr', 's8_wpr', 'trend', 'p1_mfin', 'm4_mfin', 'p1_finpct', 'm4_finpct', 'win8', 'plc8', 'days', 'wchg', 'dchg', 'n_runs',
         'weightCarried', 'barfrac', 'nr', 'distance', 'gs', 'cls', 'horse_age', 'sex', 'cls_same', 'jock_chg', 'jw', 'jw90', 'tw', 'tw90']
REL2 = ['w1', 'm3_wpr', 'm8_wpr', 'max8_wpr', 'm4_mfin', 'm4_finpct', 'days', 'weightCarried', 'barfrac', 'horse_age', 'jw', 'jw90', 'tw', 'tw90', 'win8', 'plc8']
XREL = [c for c in ['x_f', 'x_sim_all', 'x_sim_dist', 'x_sim_going', 'x_sim_track', 'x_c_max', 'x_c_ewm3', 'x_h_dist', 'x_h_going', 'x_h_track', 'x_jock_eff', 'x_sp_ewm4', 'x_sd_mean4', 'x_spd_vs_f'] if c in XC]
SHAPE = ['e1', 'e_m4', 'e_min4', 'close4', 'draw_eff']
SHAPE_FIELD = ['n_lead', 'n_ahead', 'mean_e_field', 'gap_to_lead', 'style_x_draw']


def add_features(df):
    df = df.copy()
    df['cls'] = pd.Categorical(df.clsc, categories=CLASSES).codes.astype(float)
    df.loc[df.cls < 0, 'cls'] = np.nan
    gk = df.groupby('rk')
    rel = {}
    for c in REL2 + XREL + ['e_m4', 'close4', 'draw_eff']:
        if c in df.columns:
            rel['r_' + c] = df[c] - gk[c].transform('mean')
            rel['k_' + c] = gk[c].rank(pct=True)
    rel['gap_top_m3'] = df.m3_wpr - gk.m3_wpr.transform('max')
    rel['gap_top_m8'] = df.m8_wpr - gk.m8_wpr.transform('max')
    # field pace pressure
    em = df.e_m4
    rel['n_lead'] = (em < 0.30).groupby(df.rk).transform('sum').astype(float).where(em.notna() | True)
    rel['mean_e_field'] = gk.e_m4.transform('mean')
    rel['gap_to_lead'] = em - gk.e_m4.transform('min')
    rel['n_ahead'] = gk.e_m4.rank(method='min') - 1
    rel['style_x_draw'] = em * df.barfrac
    return pd.concat([df, pd.DataFrame(rel, index=df.index)], axis=1)


d['rk'] = d.race_id
d = add_features(d)
V2 = BASE2 + [f'r_{c}' for c in REL2] + [f'k_{c}' for c in REL2] + ['gap_top_m3', 'gap_top_m8']
V3A = V2 + XC + [f'r_{c}' for c in XREL] + [f'k_{c}' for c in XREL]
V3B = V3A + SHAPE + SHAPE_FIELD + ['r_e_m4', 'k_e_m4', 'r_close4', 'k_close4', 'r_draw_eff', 'k_draw_eff']
V3B = list(dict.fromkeys(V3B))
nw = d.groupby('race_id').win.transform('sum')
d = d[(nw == 1) & (d.nr >= 5) & d.pos.notna()].copy().sort_values(['date', 'race_id']).reset_index(drop=True)
d['tgt'] = d.wpr + d.c_t.fillna(0.0)
tr = d[(d.date >= '2021-01-01') & (d.date < '2024-07-01')]
va = d[(d.date >= '2024-07-01') & (d.date < '2025-01-01')]
te = d[d.date >= '2025-01-01'].copy()
print(f'fit {len(tr):,} runs / {tr.race_id.nunique():,} races; val {va.race_id.nunique():,}; test (2025) {te.race_id.nunique():,} races; inputs V2 {len(V2)} V3a {len(V3A)} V3b {len(V3B)}', flush=True)


def softmax(df, s, T, key='race_id'):
    z = pd.Series(np.asarray(s) * T, index=df.index)
    e = np.exp(z - z.groupby(df[key]).transform('max'))
    return e / e.groupby(df[key]).transform('sum')


def fit_T(df, s):
    best = None
    for T in np.exp(np.linspace(np.log(0.01), np.log(5), 40)):
        ll = np.log(softmax(df, s, T)[df.win == 1].clip(1e-9)).mean()
        if best is None or ll > best[0]:
            best = (ll, T)
    return best[1]


def group_info(df):
    sizes = df.groupby('race_id', sort=False).size().values
    return sizes, np.concatenate([[0], np.cumsum(sizes)[:-1]])


def softmax_obj(df):
    sizes, starts = group_info(df)
    y = df.win.values.astype(float)

    def fobj(preds, ds):
        z = preds - np.repeat(np.maximum.reduceat(preds, starts), sizes)
        e = np.exp(z)
        p = e / np.repeat(np.add.reduceat(e, starts), sizes)
        return p - y, np.maximum(p * (1 - p), 1e-6)
    return fobj


def softmax_eval(df):
    sizes, starts = group_info(df)
    y = df.win.values.astype(float)

    def feval(preds, ds):
        z = preds - np.repeat(np.maximum.reduceat(preds, starts), sizes)
        e = np.exp(z)
        p = e / np.repeat(np.add.reduceat(e, starts), sizes)
        return 'winner_ll', float(np.log(p[y == 1].clip(1e-9)).mean()), True
    return feval


def train_b3(feats):
    P3 = dict(learning_rate=0.03, num_leaves=63, min_data_in_leaf=200, feature_fraction=0.5, bagging_fraction=0.7, bagging_freq=1, lambda_l2=10, verbose=-1, objective=softmax_obj(tr), metric='None')
    dtr = lgb.Dataset(tr[feats], label=tr.win.values)
    dva = lgb.Dataset(va[feats], label=va.win.values, reference=dtr)
    m = lgb.train(P3, dtr, num_boost_round=3000, valid_sets=[dva], feval=softmax_eval(va), callbacks=[lgb.early_stopping(80, verbose=False)])
    return m, fit_T(va, m.predict(va[feats]))


def metrics(df, p, name, key='race_id'):
    df = df.assign(p=np.asarray(p))
    win_ll = np.log(df.loc[df.win == 1, 'p'].clip(1e-9)).mean()
    rk = df.groupby(key).p.rank(ascending=False, method='first')
    top1 = df.loc[rk == 1, 'win'].mean()
    w3 = df.loc[df.win == 1].assign(rk=rk).rk.le(3).mean()
    w4 = df.loc[df.win == 1].assign(rk=rk).rk.le(4).mean()
    cap = df.assign(rk=rk).loc[lambda x: x.rk <= 3].groupby(key).top3.sum().div(3).mean()
    print(f'{name:34s} winner LL {win_ll:8.4f}  top pick {top1:6.1%}  winner in top3 {w3:6.1%} top4 {w4:6.1%}  top3 captured {cap:6.1%}', flush=True)
    return df.loc[df.win == 1, 'p'].clip(1e-9).apply(np.log).set_axis(df.loc[df.win == 1, key])




# ===================== Plackett-Luce top-3 objective =====================
AFE = [c for c in BASE2 if c not in ('jw', 'jw90', 'tw', 'tw90')] + XC
AFE = list(dict.fromkeys(AFE))
for df in (tr, va, te):
    df['fin'] = df.groupby('race_id').pos.rank(method='first')
trA, vaA = tr[tr.tgt.notna()], va[va.tgt.notna()]
PA = dict(objective='huber', alpha=4.0, learning_rate=0.05, num_leaves=63, min_data_in_leaf=200, feature_fraction=0.6, bagging_fraction=0.7, bagging_freq=1, lambda_l2=10, verbose=-1)
mA = lgb.train(PA, lgb.Dataset(trA[AFE], label=trA.tgt.values), num_boost_round=3000, valid_sets=[lgb.Dataset(vaA[AFE], label=vaA.tgt.values)], callbacks=[lgb.early_stopping(80, verbose=False)])
for df in (tr, va, te):
    df['sA'] = mA.predict(df[AFE])
print(f'Proj stand-in (Huber on rating, {len(AFE)} inputs): {mA.best_iteration} trees', flush=True)


def pl_parts(df, preds, K=3, wts=(1.0, 1.0, 1.0)):
    sizes, starts = group_info(df)
    fin = df.fin.values
    z = preds - np.repeat(np.maximum.reduceat(preds, starts), sizes)
    e = np.exp(z)
    g = np.zeros_like(preds)
    h = np.zeros_like(preds)
    nll = 0.0
    for k in range(1, K + 1):
        m = (fin >= k).astype(float)
        em = e * m
        den = np.repeat(np.add.reduceat(em, starts), sizes)
        p = em / np.maximum(den, 1e-300)
        hit = (fin == k).astype(float)
        g += wts[k - 1] * (p - hit)
        h += wts[k - 1] * p * (1 - p)
        pk = p[fin == k]
        nll += wts[k - 1] * -np.log(np.clip(pk, 1e-12, None)).sum()
    return g, np.maximum(h, 1e-6), nll / len(sizes)


def pl_obj(df, wts):
    def fobj(preds, ds):
        g, h, _ = pl_parts(df, preds, wts=wts)
        return g, h
    return fobj


def pl_eval(df, wts):
    def feval(preds, ds):
        return 'pl_nll', pl_parts(df, preds, wts=wts)[2], False
    return feval


def train_pl(feats, wts, label):
    P = dict(learning_rate=0.03, num_leaves=63, min_data_in_leaf=200, feature_fraction=0.5, bagging_fraction=0.7, bagging_freq=1, lambda_l2=10, verbose=-1, objective=pl_obj(tr, wts), metric='None')
    dtr = lgb.Dataset(tr[feats], label=tr.win.values)
    dva = lgb.Dataset(va[feats], label=va.win.values, reference=dtr)
    m = lgb.train(P, dtr, num_boost_round=3000, valid_sets=[dva], feval=pl_eval(va, wts), callbacks=[lgb.early_stopping(80, verbose=False)])
    print(f'{label}: {m.best_iteration} trees', flush=True)
    return m


MODELS = {
    'PL3 Proj inputs': (train_pl(AFE, (1, 1, 1), 'PL3 on the Proj inputs'), AFE),
    'PL3 all inputs': (train_pl(V3A, (1, 1, 1), 'PL3 on all inputs'), V3A),
    'PL3 win-heavy all inputs': (train_pl(V3A, (2, 1, 1), 'PL3 win x2 on all inputs'), V3A),
}
mD, TD = train_b3(V3A)
for nm, (m, fl) in MODELS.items():
    for df in (va, te):
        df['s_' + nm] = m.predict(df[fl])
for df in (va, te):
    df['s_direct'] = mD.predict(df[V3A])


def race_sd(df, col):
    return df[col].groupby(df.race_id).transform(lambda s: s - s.mean()).std()


def to_rating2(df, col, sd_score, sdA, m=1.0):
    s = df[col]
    c = s - s.groupby(df.race_id).transform('mean')
    return df.sA.groupby(df.race_id).transform('mean') + m * (sdA / sd_score) * c


# ---------- metrics ----------
def pick_metrics(df, score, name):
    d_ = df.assign(p=np.asarray(score))
    d_ = d_[d_.pos.notna()].copy()
    d_['rk'] = d_.groupby('race_id').p.rank(ascending=False, method='first')
    d_['f'] = d_.fin
    ok = d_.groupby('race_id').f.transform(lambda s: len(s) >= 6)
    d_ = d_[ok]
    w = d_.pivot_table(index='race_id', columns='f', values='rk', aggfunc='first')
    top1 = (d_[d_.rk == 1].f == 1).mean()
    wint3 = (w[1] <= 3).mean()
    cap3 = np.mean([(w[j] <= 3).mean() for j in (1, 2, 3)])
    set3 = ((w[1] <= 3) & (w[2] <= 3) & (w[3] <= 3)).mean()
    set4 = ((w[1] <= 4) & (w[2] <= 4) & (w[3] <= 4)).mean()
    q3 = ((w[1] <= 3) & (w[2] <= 3)).mean()
    pk = [(d_[d_.rk == k].f <= 3).mean() for k in (1, 2, 3)]
    print(f'   {name:34s} #1 wins {top1:5.1%} | winner in top3 {wint3:5.1%} | real top3 captured by our top3 {cap3:5.1%} | all of real top3 in our top3 {set3:5.1%} / top4 {set4:5.1%} | quinella (1-2 in our top3) {q3:5.1%} | our #1/#2/#3 finish top3 {pk[0]:5.1%} {pk[1]:5.1%} {pk[2]:5.1%}')


def lines(df, rating, name, pts=(2, 4), quiet=False):
    d_ = df.assign(r=np.asarray(rating))
    d_ = d_[d_.pos.notna() & d_.r.notna()].copy()
    d_['gap'] = d_.groupby('race_id').r.transform('max') - d_.r
    d_ = d_[d_.groupby('race_id').pos.transform(lambda s: len(s) >= 6)]
    nraces = d_.race_id.nunique()
    out = {}
    for k in pts:
        ins = d_[d_.gap <= k]
        size = len(ins) / nraces
        win = (d_[d_.fin == 1].gap <= k).mean()
        t3 = (d_[d_.fin <= 3].gap <= k).mean()
        out[k] = (size, win, t3)
    if not quiet:
        s = '  |  '.join(f'within {k}: {out[k][0]:4.2f} runners, winners {out[k][1]:5.1%}, real top3 inside {out[k][2]:5.1%}, winners per runner {out[k][1] / out[k][0]:5.1%}' for k in pts)
        print(f'   {name:34s} {s}')
    return out


# ---------- scale choice on 2024 H2: same shortlist size as the Proj stand-in, then the capture gain ----------
sdA = race_sd(va, 'sA')
print(f'\nwithin-race sd of the Proj stand-in figure on val: {sdA:.2f}')
base_va = lines(va, va.sA, 'stand-in Proj (val)', quiet=True)
print(f'stand-in Proj on val: within 2 = {base_va[2][0]:.2f} runners, {base_va[2][1]:.1%} winners; within 4 = {base_va[4][0]:.2f} runners, {base_va[4][1]:.1%} winners')

CHOICE = {}
for nm in list(MODELS) + ['direct']:
    col = 's_' + nm
    sd_s = race_sd(va, col)
    best = None
    for m in np.linspace(0.5, 2.5, 41):
        o = lines(va, to_rating2(va, col, sd_s, sdA, m), nm, quiet=True)
        err = abs(o[2][0] - base_va[2][0]) + abs(o[4][0] - base_va[4][0])
        if best is None or err < best[0]:
            best = (err, m)
    CHOICE[nm] = (sd_s, best[1])
    print(f'{nm}: scale multiplier {best[1]:.2f} makes the 2 / 4 point lines hold the same number of runners as the Proj stand-in on val')

print('\n\n===== T1 (2025, full fields): top-3 picking =====')
pick_metrics(te, te.sA, 'Proj stand-in (rating model)')
for nm in list(MODELS) + ['direct']:
    pick_metrics(te, te['s_' + nm], nm)

print('\n===== T1: shortlists within 2 / 4 points, scale matched to the stand-in shortlist size (chosen on val) =====')
lines(te, te.sA, 'stand-in Proj')
for nm in list(MODELS) + ['direct']:
    sd_s, m = CHOICE[nm]
    lines(te, to_rating2(te, 's_' + nm, sd_s, sdA, m), f'{nm} (x{m:.2f})')

print('\n===== T1: the frontier, runners vs winners inside the 2 and 4 point lines, by scale multiplier =====')
for nm in ('PL3 all inputs',):
    sd_s, _ = CHOICE[nm]
    for m in (0.6, 0.8, 1.0, 1.2, 1.5, 2.0):
        lines(te, to_rating2(te, 's_' + nm, sd_s, sdA, m), f'{nm} x{m}')
print('   (stand-in Proj for reference)')
lines(te, te.sA, 'stand-in Proj')

# winners captured at the SAME capture, how many fewer runners: scale chosen on val to match the stand-in's winners captured
print('\n===== T1: scale matched to the stand-in WINNERS captured instead (chosen on val): how many fewer runners =====')
for nm in list(MODELS) + ['direct']:
    col = 's_' + nm
    sd_s = CHOICE[nm][0]
    best = None
    for m in np.linspace(0.5, 3.0, 51):
        o = lines(va, to_rating2(va, col, sd_s, sdA, m), nm, quiet=True)
        err = abs(o[2][1] - base_va[2][1]) + abs(o[4][1] - base_va[4][1])
        if best is None or err < best[0]:
            best = (err, m)
    lines(te, to_rating2(te, col, sd_s, sdA, best[1]), f'{nm} (x{best[1]:.2f})')
# ---------------- T2: real page-scale fields from the log ----------------
rows = []
for f in sorted(glob.glob(os.path.join(ROOT, 'data', 'direct_log', '*.json.gz'))):
    R = json.load(gzip.open(f, 'rt'))['rows']
    for x in (R.values() if isinstance(R, dict) else R):
        rows.append(dict(x))
L = pd.DataFrame(rows)
L = L[L.won.notna()].copy()
import runners_io
rr = runners_io.read_runners()
rr['race_id'] = pd.to_numeric(rr.race_id, errors='coerce')
rr['horse_id'] = pd.to_numeric(rr.horse_id, errors='coerce')
act = rr[rr.scratched.fillna(0).astype(float) == 0]
cnt = act.groupby('race_id').size()
L['race_id'] = pd.to_numeric(L.race_id, errors='coerce')
L['horse_id'] = pd.to_numeric(L.horse_id, errors='coerce')
gl = L.groupby('race_id').agg(n=('won', 'size'), w=('won', 'sum'))
okr = gl[(gl.n == gl.index.map(cnt)) & (gl.w == 1) & (gl.n >= 5)].index
L = L[L.race_id.isin(okr)].copy()
ag = act.drop_duplicates(['race_id', 'horse_id']).set_index(['race_id', 'horse_id'])[['horse_age', 'horse_sex']]
L = L.join(ag, on=['race_id', 'horse_id'])
L['date'] = pd.to_datetime(L.date)
L['nr'] = L.groupby('race_id').horse_id.transform('size').astype(float)
L['jk'], L['tk'] = L.jockey.map(nk), L.trainer.map(nk)
Lr = L.reset_index(drop=True)
rrA = pd.read_csv  # placeholder to keep linters quiet
# jockey / trainer rates: history = results (to 2025-12) plus the rc file for 2026
rc = pd.read_csv(os.path.join(ROOT, 'race_results_2026_rc.csv.gz'), usecols=lambda c: c in ('date', 'jockey', 'trainer', 'positionFinish', 'isBarrierTrial'), low_memory=False)
rc = rc[~rc.isBarrierTrial.astype(str).isin(['True', '1'])]
rc['date'] = pd.to_datetime(rc.date)
rc['pos'] = pd.to_numeric(rc.positionFinish, errors='coerce')
rc['jk'], rc['tk'] = rc.jockey.map(nk), rc.trainer.map(nk)
rc['winf'] = np.where(rc.pos.notna(), (rc.pos == 1).astype(float), np.nan)
r26 = pd.concat([pd.read_csv(os.path.join(ROOT, 'race_results_2026.csv.gz'), usecols=lambda c: c in ('date', 'jockey', 'trainer', 'positionFinish', 'isBarrierTrial'), low_memory=False)], ignore_index=True)
r26 = r26[~r26.isBarrierTrial.astype(str).isin(['True', '1'])]
r26['date'] = pd.to_datetime(r26.date)
r26['pos'] = pd.to_numeric(r26.positionFinish, errors='coerce')
r26['jk'], r26['tk'] = r26.jockey.map(nk), r26.trainer.map(nk)
r26['winf'] = np.where(r26.pos.notna(), (r26.pos == 1).astype(float), np.nan)
H = pd.concat([r[['date', 'jk', 'tk', 'winf']], r26[['date', 'jk', 'tk', 'winf']], rc[rc.date > r26.date.max()][['date', 'jk', 'tk', 'winf']]], ignore_index=True)
LH = pd.concat([H, Lr[['date', 'jk', 'tk']].assign(winf=np.nan)], ignore_index=True)
nH = len(H)
jw = asof_rate(LH, 'jk', 'winf')[nH:]
jw90 = asof_rate(LH, 'jk', 'winf', window_days=90, k=30)[nH:]
tw = asof_rate(LH, 'tk', 'winf')[nH:]
tw90 = asof_rate(LH, 'tk', 'winf', window_days=90, k=30)[nH:]
# draw by track for the live rows (history: results to 2025-12)
Lr['vk'] = C.venue_key(Lr.venue.astype(str))
Lr['barfrac'] = (Lr.barrier - 1) / (Lr.nr - 1)
Lr['third'] = np.minimum((Lr.barfrac * 3).fillna(1).astype(int), 2)
Lr['dband'] = (pd.to_numeric(Lr.distance, errors='coerce') / 200).round()
Lr['dall'] = Lr.vk.astype(str) + '|' + Lr.dband.astype(str)
Lr['dk'] = Lr.dall + '|' + Lr.third.astype(str)
DH = pd.concat([r[['date', 'dk', 'dall', 'finpct']], Lr[['date', 'dk', 'dall']].assign(finpct=np.nan)], ignore_index=True)
nD = len(r)
draw_live = (asof_rate(DH, 'dk', 'finpct', prior=0.5, k=100) - asof_rate(DH, 'dall', 'finpct', prior=0.5, k=100))[nD:]
# shape history from the runner-page store
store = FT.runner_page_runs()[['horse_id', 'date', 'position800m', 'field_size', 'positionFinish']].copy()
store['e'] = pd.to_numeric(store.position800m, errors='coerce') / pd.to_numeric(store.field_size, errors='coerce')
store['fp'] = (pd.to_numeric(store.positionFinish, errors='coerce') - 1) / (pd.to_numeric(store.field_size, errors='coerce') - 1)
store['late'] = store.e - store.fp
store = store.sort_values(['horse_id', 'date'])
byh = {h: x for h, x in store.groupby('horse_id')}
feat_rows = []
for i, x in enumerate(Lr.itertuples()):
    h = list(x.hist or [])[::-1]
    rt = [a.get('wpr') if a.get('wpr') is not None else np.nan for a in h] + [np.nan] * 12
    mf = [min(max(a.get('marginFinish'), 0), 30) if a.get('marginFinish') is not None else np.nan for a in h] + [np.nan] * 4
    fp = [((a['positionFinish'] - 1) / (a['starters'] - 1)) if a.get('positionFinish') and a.get('starters') and a['starters'] > 1 else np.nan for a in h] + [np.nan] * 4
    ps = [a.get('positionFinish') if a.get('positionFinish') is not None else np.nan for a in h][:8]
    last = h[0] if h else None
    arr8 = np.array(rt[:8], dtype=float)
    m8 = np.nanmean(arr8) if np.isfinite(arr8).any() else np.nan
    pk = np.array(ps, dtype=float)
    npk = np.isfinite(pk).sum()
    sx = byh.get(x.horse_id)
    e4 = lt4 = np.array([np.nan])
    if sx is not None:
        j = np.searchsorted(sx.date.values, np.datetime64(x.date), side='left')
        e4 = sx.e.values[max(0, j - 4):j][::-1]
        lt4 = sx.late.values[max(0, j - 4):j][::-1]
    feat_rows.append(dict(w1=rt[0], w2=rt[1], w3=rt[2], w4=rt[3], w5=rt[4], w6=rt[5], m3_wpr=np.nanmean(rt[:3]) if np.isfinite(rt[:3]).any() else np.nan, m8_wpr=m8,
                          max8_wpr=np.nanmax(arr8) if np.isfinite(arr8).any() else np.nan, s8_wpr=np.nanstd(arr8, ddof=1) if np.isfinite(arr8).sum() > 1 else np.nan,
                          trend=(rt[0] - m8) if np.isfinite(rt[0]) else np.nan, p1_mfin=mf[0], m4_mfin=np.nanmean(mf[:4]) if np.isfinite(mf[:4]).any() else np.nan, p1_finpct=fp[0],
                          m4_finpct=np.nanmean(fp[:4]) if np.isfinite(fp[:4]).any() else np.nan,
                          win8=float((pk == 1).sum() / npk) if npk else np.nan, plc8=float((pk <= 3).sum() / npk) if npk else np.nan,
                          days=(x.date - pd.Timestamp(last['date'])).days if last else np.nan,
                          wchg=(x.weight - last['weightCarried']) if last and last.get('weightCarried') is not None and x.weight is not None else np.nan,
                          dchg=(x.distance - last['distance']) if last and last.get('distance') is not None else np.nan, n_runs=float(min(len(h), 12)),
                          cls_same=float(C.class_code(pd.Series([last.get('class')])).iloc[0] == C.class_code(pd.Series([x.race_class])).iloc[0]) if last and last.get('class') else np.nan,
                          jock_chg=float(nk(last.get('jockey')) != x.jk) if last and last.get('jockey') and x.jk else np.nan,
                          jw=jw[i], jw90=jw90[i], tw=tw[i], tw90=tw90[i], draw_eff=draw_live[i],
                          e1=e4[0] if len(e4) else np.nan, e_m4=np.nanmean(e4) if np.isfinite(e4).any() else np.nan, e_min4=np.nanmin(e4) if np.isfinite(e4).any() else np.nan,
                          close4=np.nanmean(lt4) if np.isfinite(lt4).any() else np.nan))
Lf = pd.concat([Lr, pd.DataFrame(feat_rows)], axis=1)
Lf['weightCarried'] = pd.to_numeric(Lf.weight, errors='coerce')
Lf['distance'] = pd.to_numeric(Lf.distance, errors='coerce')
Lf['gs'] = pd.to_numeric(Lf.going.astype(str).str.extract(r'(\d+)')[0], errors='coerce')
Lf['horse_age'] = pd.to_numeric(Lf.horse_age, errors='coerce')
Lf['sex'] = Lf.horse_sex.astype(str).str.upper().str[:1].map(SEX)
Lf['clsc'] = C.class_code(Lf.race_class)
Lf['rk'] = Lf.race_id
# Proj context / relevance / speed block from the live store, exactly as the live Proj builds it
print('building the live context block ...', flush=True)
co = C.coefs()
rp = C.page_frame()
rp['f'] = C.formula_pred(rp, co)
rp = C.context_columns(rp)
rp['resid'] = rp.wpr - rp.f
rp = C.add_speed(rp)
tab = C.jockey_table(rp)
X = pd.DataFrame({'horse_id': Lf.horse_id, 'date': Lf.date, 'jockey': Lf.jockey.fillna('').astype(str), 'venue': Lf.venue, 'distance': Lf.distance, 'going': Lf.going,
                  'weightCarried': Lf.weightCarried, 'barrier': Lf.barrier, 'field_size': Lf.nr, 'race_class': Lf.race_class, 'trackGrading': Lf.grading, 'prize': Lf.prize})
X['going_n'] = C.going_num(X.going)
X['grade'] = pd.to_numeric(X.trackGrading, errors='coerce')
X['cls'] = C.class_code(X.race_class)
X['vn'] = C.venue_key(X.venue.astype(str))
X['venue'] = X.vn
X['lprize'] = np.log1p(pd.to_numeric(X['prize'], errors='coerce'))
h = C.target_history(X, rp)
X = pd.concat([X.drop(columns=[c for c in h.columns if c in X.columns]), h], axis=1)
X['f'] = C.formula_pred(X, co)
X = C.context_columns(X)
X = C.add_jockey(X, tab, targets=True)
X = C.add_venue(X, rp)
X = C.add_field(X)
Xr = pd.concat([X, C.rel_features(X, rp)], axis=1)
Xr = pd.concat([Xr, C.speed_features(Xr, rp)], axis=1)
for c in XC:
    Lf[c] = Xr[c[2:]].values if c[2:] in Xr.columns else np.nan
Lf = add_features(Lf)
Lf['win'] = Lf.won.astype(float)
Lf['pos'] = pd.to_numeric(Lf.finish, errors='coerce')
Lf['top3'] = (Lf.pos <= 3).astype(float)
Lf['pj'] = pd.to_numeric(Lf.proj, errors='coerce')
okp = Lf.groupby('race_id').pj.transform(lambda s: s.notna().all())
S2 = Lf[okp].copy()
S2['fin'] = S2.groupby('race_id').pos.rank(method='first')
for nm, (m, fl) in MODELS.items():
    S2['s_' + nm] = m.predict(S2[fl])
S2['s_direct'] = mD.predict(S2[V3A])
S2['sA'] = S2.pj
print(f'\n\n===== T2: {S2.race_id.nunique()} real complete fields with the dashboard Proj =====')
sdP = S2.pj.groupby(S2.race_id).transform(lambda s: s - s.mean()).std()
pick_metrics(S2, S2.pj, 'dashboard Proj')
for nm in list(MODELS) + ['direct']:
    pick_metrics(S2, S2['s_' + nm], nm)
print('\n  shortlists within 2 / 4 points (scale chosen on T1 val to match the stand-in shortlist size, applied around the real Proj mean)')
lines(S2, S2.pj, 'dashboard Proj')
for nm in list(MODELS) + ['direct']:
    sd_s, m = CHOICE[nm]
    s = S2['s_' + nm]
    c = s - s.groupby(S2.race_id).transform('mean')
    r = S2.pj.groupby(S2.race_id).transform('mean') + m * (sdP / sd_s) * c
    lines(S2, r, f'{nm} (x{m:.2f})')
