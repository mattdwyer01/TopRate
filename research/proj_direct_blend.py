"""Proj improvement test (27 Oct 2026): items 1, 2 and 4.
1. blend the direct finishing-position model into the Proj and turn the result back into a rating on the ATW (runner-page) scale,
2. the Proj stand-in and the direct model are both trained on the plain-rating history converted to the ATW scale (AR 168 shift per target race),
4. a per-runner reliability measure (predicted size of the miss).
T1 = 2025 results-file races (full fields, Proj stand-in = Huber LightGBM on the Proj's own kind of inputs); T2 = the daily log's complete real fields with the dashboard Proj.
  PYTHONPATH=.:projection:research python research/proj_direct_blend.py   (needs /tmp/direct_ctx_feats.pkl from the direct-v3 artifact)"""
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



# ===================== Proj improvement test: direct model blended into the Proj, kept on the ATW scale =====================
AFE = [c for c in BASE2 if c not in ('jw', 'jw90', 'tw', 'tw90')] + XC       # the Proj's own kind of inputs: rating history, class, context/relevance/speed block (no field-relative or connection rates)
AFE = list(dict.fromkeys(AFE))
trA, vaA = tr[tr.tgt.notna()], va[va.tgt.notna()]
PA = dict(objective='huber', alpha=4.0, learning_rate=0.05, num_leaves=63, min_data_in_leaf=200, feature_fraction=0.6, bagging_fraction=0.7, bagging_freq=1, lambda_l2=10, verbose=-1)
mA = lgb.train(PA, lgb.Dataset(trA[AFE], label=trA.tgt.values), num_boost_round=3000, valid_sets=[lgb.Dataset(vaA[AFE], label=vaA.tgt.values)], callbacks=[lgb.early_stopping(80, verbose=False)])
print(f'Proj stand-in (Huber regression on page-scale rating, {len(AFE)} inputs): {mA.best_iteration} trees', flush=True)
for df in (tr, va, te):
    df['sA'] = mA.predict(df[AFE])
TA = fit_T(va, va.sA)
print(f'softmax sharpness for the stand-in on val: {TA:.3f} (live Proj uses 0.20)', flush=True)
mD, TD, _ = None, None, None
mD, TD = train_b3(V3A)
for df in (va, te):
    df['sD'] = mD.predict(df[V3A])
print(f'direct model: {mD.best_iteration} trees, T {TD:.3f}', flush=True)


def lnp(df, s, T):
    return np.log(softmax(df, s, T, 'race_id').clip(1e-9))


def blend_p(df, sA, sD, TA_, TD_, w):
    z = w * TD_ * pd.Series(sD, index=df.index) + (1 - w) * TA_ * pd.Series(sA, index=df.index)
    return softmax(df, z, 1.0, 'race_id')


print('\nT1 (2025, full fields): winner picking by blend weight w on the direct model (0 = Proj stand-in only, 1 = direct only); w chosen on 2024 H2')
best = None
for w in (0, .2, .3, .4, .5, .6, .7, .8, 1.0):
    pv = blend_p(va, va.sA, va.sD, TA, TD, w)
    ll = np.log(pv[va.win == 1].clip(1e-9)).mean()
    if best is None or ll > best[0]:
        best = (ll, w)
    metrics(te, blend_p(te, te.sA, te.sD, TA, TD, w), f'w={w}')
W_STAR = best[1]
print(f'w chosen on val: {W_STAR}')
base_ll = metrics(te, blend_p(te, te.sA, te.sD, TA, TD, 0), 'stand-in Proj alone')
bl_ll = metrics(te, blend_p(te, te.sA, te.sD, TA, TD, W_STAR), f'blend w={W_STAR}')
dd = bl_ll - base_ll
print(f'   blend minus stand-in Proj: {dd.mean():+.4f} (se {dd.std() / np.sqrt(len(dd)):.4f}) over {len(dd)} races')


def to_rating(df, sA, sD, TA_, TD_, w):
    """Rating on the ATW (page) scale: the race mean of the Proj figure plus (blend logit - race mean) / TA, so w = 0 returns the Proj figure itself."""
    sA = pd.Series(np.asarray(sA), index=df.index)
    z = (w * TD_ * pd.Series(np.asarray(sD), index=df.index) + (1 - w) * TA_ * sA)
    z = z - z.groupby(df.race_id).transform('mean')
    return sA.groupby(df.race_id).transform('mean') + z / TA_


rt = to_rating(te, te.sA, te.sD, TA, TD, W_STAR)
ok = te.tgt.notna()
print('\nRating sanity on the ATW scale (2025 runs, target = the run\'s own page-scale rating):')
for lab, v in (('Proj stand-in', te.sA), (f'blend w={W_STAR} as a rating', rt)):
    e = (te.tgt - v)[ok]
    ew = (te.tgt - v)[ok]; ew = ew - ew.groupby(te.race_id[ok]).transform('mean')
    print(f'   {lab:28s} RMSE {np.sqrt((e ** 2).mean()):.3f}  MAE {e.abs().mean():.3f}  bias {(-e).mean():+.3f}  within-race RMSE {np.sqrt((ew ** 2).mean()):.3f}  within-race sd of figure {v.groupby(te.race_id).transform(lambda s: s - s.mean()).std():.2f}')
print(f'   mean figure: stand-in {te.sA.mean():.2f} vs blend {rt.mean():.2f}; corr within race {np.corrcoef(te.sA - te.groupby("race_id").sA.transform("mean"), rt - rt.groupby(te.race_id).transform("mean"))[0, 1]:.3f}; mean |blend - stand-in| {(rt - te.sA).abs().mean():.2f}')
# does the blended rating's spread match how winners are priced? refit beta on the rating
Tr = fit_T(te.assign(r=rt), rt)
print(f'   softmax sharpness that fits the blended rating on 2025: {Tr:.3f} (stand-in {fit_T(te, te.sA):.3f})')

# ---------- item 4: how reliable is each figure (per-runner error size) ----------
print('\nReliability: predicted size of the miss for each runner (model fitted on the 2024 H2 misses of the stand-in, scored on 2025)')
vaR = va[va.tgt.notna()].copy()
vaR['r2'] = (vaR.tgt - vaR.sA) ** 2
RF = list(dict.fromkeys(AFE + ['sA', 'nr']))
PR = dict(objective='regression', learning_rate=0.03, num_leaves=15, min_data_in_leaf=300, feature_fraction=0.7, bagging_fraction=0.7, bagging_freq=1, lambda_l2=20, verbose=-1)
half = vaR.race_id.rank(method='dense') % 2 == 0
mR = lgb.train(PR, lgb.Dataset(vaR[~half][RF], label=vaR[~half].r2.values), num_boost_round=1500, valid_sets=[lgb.Dataset(vaR[half][RF], label=vaR[half].r2.values)], callbacks=[lgb.early_stopping(60, verbose=False)])
teR = te[ok].copy()
teR['sd'] = np.sqrt(np.clip(mR.predict(teR[RF]), 4, None))
teR['res'] = teR.tgt - teR.sA
teR['q'] = pd.qcut(teR.sd.rank(method='first'), 5, labels=False)
nb = teR.n_runs.clip(upper=8).astype(int)
base_sd = teR.groupby(nb).res.transform(lambda s: np.sqrt((s ** 2).mean()))
print(f'   trees {mR.best_iteration}; corr(predicted sd, |miss|) {np.corrcoef(teR.sd, teR.res.abs())[0, 1]:.3f} vs by-run-count sd {np.corrcoef(base_sd, teR.res.abs())[0, 1]:.3f}')
print('   quintile of predicted sd: predicted sd / actual RMSE / share of misses beyond 12 points')
for q, g in teR.groupby('q'):
    print(f'      Q{q + 1}: {g.sd.mean():5.2f} / {np.sqrt((g.res ** 2).mean()):5.2f} / {(g.res.abs() > 12).mean():6.1%}')
cov = (teR.res.abs() <= teR.sd).mean()
print(f'   share of runs inside +-1 predicted sd: {cov:.1%} (normal would be 68%), inside 2 sd {(teR.res.abs() <= 2 * teR.sd).mean():.1%}')
# does the reliability measure help pick winners? shrink the figure of unreliable runners toward the field mean
teS = te.copy()
teS['sd'] = np.sqrt(np.clip(mR.predict(teS[RF]), 4, None))
for g_ in (0.0, 0.5, 1.0):
    z = teS.sA * (teS.sd.mean() / teS.sd) ** g_
    Tg = fit_T(teS, z)
    metrics(teS, softmax(teS, z, Tg, 'race_id'), f'figure / sd^{g_} (stand-in)')

# ---------------- T2 with the real dashboard Proj ----------------
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
Lf['sD'] = mD.predict(Lf[V3A])
okp = Lf.groupby('race_id').pj.transform(lambda s: s.notna().all())
S2 = Lf[okp].copy()
print(f'\nT2: {S2.race_id.nunique()} complete labelled races where every runner has a dashboard Proj')
half2 = (S2.date >= S2.date.median()).values
for w in (0, .2, .3, .4, .5, .6, 1.0):
    metrics(S2, blend_p(S2, S2.pj, S2.sD, 0.20, TD, w), f'real Proj + direct, w={w}')
b0 = metrics(S2, blend_p(S2, S2.pj, S2.sD, 0.20, TD, 0), 'real Proj alone')
bw = metrics(S2, blend_p(S2, S2.pj, S2.sD, 0.20, TD, W_STAR), f'real Proj + direct, w={W_STAR} (from T1)')
dd = bw - b0
print(f'   blend minus Proj alone: {dd.mean():+.4f} (se {dd.std() / np.sqrt(len(dd)):.4f}) over {len(dd)} races')
r2 = to_rating(S2, S2.pj, S2.sD, 0.20, TD, W_STAR)
print(f'   blended rating vs Proj: mean change {(r2 - S2.pj).mean():+.3f}, mean |change| {(r2 - S2.pj).abs().mean():.2f}, max {(r2 - S2.pj).abs().max():.1f}; within-race sd Proj {S2.pj.groupby(S2.race_id).transform(lambda s: s - s.mean()).std():.2f} vs blend {r2.groupby(S2.race_id).transform(lambda s: s - s.mean()).std():.2f}')
print(f'   top pick changes in {(S2.assign(a=S2.pj, b=r2).groupby("race_id").apply(lambda g: g.a.idxmax() != g.b.idxmax())).mean():.1%} of races')


# ---------------- placings: do the 2nd, 3rd and 4th picks and the real placegetters line up better? ----------------
def placings(df, p, name):
    d_ = df.assign(p=np.asarray(p))
    d_ = d_[d_.pos.notna()].copy()
    d_['rk'] = d_.groupby('race_id').p.rank(ascending=False, method='first')
    d_['fin'] = d_.pos
    ok = d_.groupby('race_id').fin.transform(lambda s: (s.nunique() == len(s)) and len(s) >= 6)
    d_ = d_[ok]
    n = d_.race_id.nunique()
    print(f'\n  {name} ({n} races)')
    row = []
    for k in (1, 2, 3, 4):
        g = d_[d_.rk == k]
        row.append(f'our #{k}: wins {(g.fin == 1).mean():5.1%} top3 {(g.fin <= 3).mean():5.1%} avg fin {g.fin.mean():4.1f}')
    print('   ' + '  |  '.join(row))
    row = []
    for j in (1, 2, 3, 4):
        g = d_[d_.fin == j]
        row.append(f'real {j}: in our top4 {(g.rk <= 4).mean():5.1%} avg our rank {g.rk.mean():4.1f}')
    print('   ' + '  |  '.join(row))
    w = d_.pivot_table(index='race_id', columns='fin', values='rk', aggfunc='first')
    q3 = ((w[1] <= 3) & (w[2] <= 3)).mean()
    q4 = ((w[1] <= 4) & (w[2] <= 4)).mean()
    t4 = ((w[1] <= 4) & (w[2] <= 4) & (w[3] <= 4)).mean()
    t5 = ((w[1] <= 5) & (w[2] <= 5) & (w[3] <= 5)).mean()
    f5 = ((w[1] <= 5) & (w[2] <= 5) & (w[3] <= 5) & (w[4] <= 5)).mean()
    f6 = ((w[1] <= 6) & (w[2] <= 6) & (w[3] <= 6) & (w[4] <= 6)).mean()
    print(f'   quinella (1st+2nd both in our top 3 / top 4): {q3:5.1%} / {q4:5.1%}   trifecta (real top 3 all in our top 4 / top 5): {t4:5.1%} / {t5:5.1%}   first four (all in our top 5 / top 6): {f5:5.1%} / {f6:5.1%}')


print('\n\n===== PLACINGS: Proj vs blend (w chosen on val) vs direct alone =====')
print('\nT1 (2025 full fields, Proj stand-in)')
placings(te, te.sA, 'stand-in Proj alone')
placings(te, blend_p(te, te.sA, te.sD, TA, TD, W_STAR), f'blend w={W_STAR}')
placings(te, blend_p(te, te.sA, te.sD, TA, TD, 0.5), 'blend w=0.5')
placings(te, te.sD, 'direct alone')
print('\nT2 (real dashboard Proj, complete fields)')
placings(S2, S2.pj, 'real Proj alone')
placings(S2, blend_p(S2, S2.pj, S2.sD, 0.20, TD, W_STAR), f'blend w={W_STAR}')
placings(S2, blend_p(S2, S2.pj, S2.sD, 0.20, TD, 0.5), 'blend w=0.5')
placings(S2, S2.sD, 'direct alone')
