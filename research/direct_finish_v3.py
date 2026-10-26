"""Direct finishing-position model v3 (26 Oct 2026): Step 1 = Proj's context / relevance / speed-figure inputs, Step 2 = race shape and draw by track.
Three variants of the same softmax-loss model (B3 of direct_finish_v2.py), same fit/validation windows, same test races:
  V2   control: the v2 inputs (converted ratings, jockey/trainer rates, form, field-relative versions)
  V3a  V2 + Proj's context inputs (class, venue effect, field strength, rides together, runs at track), the relevance inputs (each earlier run judged against today's distance, going, track,
       jockey, class, days, similarity-weighted averages, own record under the same conditions) and the speed-figure block (last 4 figures, EWM, spread, speed vs rating)
       [built by direct_ctx_features.py on the converted frame, 2019-06 to 2025-12, so T1 is 2025 only]
  V3b  V3a + race shape (early-position history, closing gain, field pace pressure: how many likely leaders, own rank for early speed, style x draw) and draw by track
       (as-of finishing share of the runner's barrier third at this venue and distance band, against the venue/distance average)
T1: results-file races of 2025 (full fields). T2: the log's complete real-page fields (ratings as TopRate gives them; context/speed from the live store via ctx; shape from the store's
position800m; draw from the results files). Value read: gain over the price (logit of ln price + ln model) for each variant.
  PYTHONPATH=.:projection:research python research/direct_finish_v3.py
"""
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


MODELS = {}
for name, fl in (('V2 control', V2), ('V3a +ctx/relevance/speed', V3A), ('V3b +shape/draw', V3B)):
    m, T = train_b3(fl)
    MODELS[name] = (m, T, fl)
    print(f'{name}: {m.best_iteration} trees, T {T:.3f}', flush=True)
print('\nT1: results-file races of 2025, full fields')
P1, LL1 = {}, {}
for name, (m, T, fl) in MODELS.items():
    P1[name] = softmax(te, m.predict(te[fl]), T, 'rk')
    LL1[name] = metrics(te, P1[name], name)
for name in list(MODELS)[1:]:
    df = LL1[name] - LL1['V2 control']
    print(f'   {name} minus V2 control: {df.mean():+.4f} (se {df.std() / np.sqrt(len(df)):.4f}) over {len(df)} races')
m3, T3, fl3 = MODELS['V3b +shape/draw']
imp = pd.Series(m3.feature_importance('gain'), index=fl3).sort_values(ascending=False)
print('V3b top inputs by gain:', ', '.join(f'{k} {v / imp.sum():.1%}' for k, v in imp.head(15).items()))
for lab, cl in (('ctx / relevance / speed inputs', set(XC) | {f'r_{c}' for c in XREL} | {f'k_{c}' for c in XREL}), ('shape and draw inputs', set(SHAPE + SHAPE_FIELD + ['r_e_m4', 'k_e_m4', 'r_close4', 'k_close4', 'r_draw_eff', 'k_draw_eff']))):
    print(f'   share of V3b gain from {lab}: {imp[[c for c in imp.index if c in cl]].sum() / imp.sum():.1%}')


def cond_logit(df, cols_, key):
    sizes = df.groupby(key, sort=False).size().values
    starts = np.concatenate([[0], np.cumsum(sizes)[:-1]])
    X = df[cols_].values
    y = df.win.values

    def nll(b):
        s = X @ b
        mx = np.repeat(np.maximum.reduceat(s, starts), sizes)
        lse = np.log(np.add.reduceat(np.exp(s - mx), starts))
        return -(s[y == 1] - mx[y == 1] - lse).mean()
    return minimize(nll, np.ones(len(cols_)) * 0.5, method='BFGS').x


def price_gain(df, probs, price, label):
    df = df.assign(pr=pd.to_numeric(price, errors='coerce'))
    ok = df.groupby('race_id').pr.transform(lambda s: s.notna().all() and 1.05 <= (1 / s).sum() <= 2.0)
    df = df[ok].copy()
    ip = 1 / df.pr
    df['lmk'] = np.log(ip / ip.groupby(df.race_id).transform('sum'))
    half = (df.date >= df.date.median()).values
    print(f'\nVALUE READ, {label}: {df.race_id.nunique()} clean-book races; winner LL gain of price+model over price alone (cross-fitted by date halves)')
    for name, p in probs.items():
        df['lm'] = np.log(p[df.index].clip(1e-9))
        out = pd.Series(np.nan, index=df.index)
        for a_, b_ in ((~half, half), (half, ~half)):
            bco = cond_logit(df[a_], ['lmk', 'lm'], 'race_id')
            s = pd.Series(df[b_][['lmk', 'lm']].values @ bco, index=df[b_].index)
            e = np.exp(s - s.groupby(df[b_].race_id).transform('max'))
            out[b_] = e / e.groupby(df[b_].race_id).transform('sum')
        w = df.win == 1
        gain = np.log(out[w].clip(1e-9)) - df.lmk[w]
        print(f'   {name:30s} gain {gain.mean():+.4f} (se {gain.std() / np.sqrt(len(gain)):.4f})')


price_gain(te, P1, te.priceStarting, 'T1 2025 closing price')

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
print(f'\nT2: real page-scale fields, {Lf.race_id.nunique()} complete labelled races, {len(Lf)} runners; context block present on {Lf.x_f.notna().mean():.1%}, shape on {Lf.e_m4.notna().mean():.1%}, draw on {Lf.draw_eff.notna().mean():.1%}')
P2, LL2 = {}, {}
for name, (m, T, fl) in MODELS.items():
    P2[name] = softmax(Lf, m.predict(Lf[fl]), T, 'rk')
    LL2[name] = metrics(Lf, P2[name], name)
for name in list(MODELS)[1:]:
    df = LL2[name] - LL2['V2 control']
    print(f'   {name} minus V2 control: {df.mean():+.4f} (se {df.std() / np.sqrt(len(df)):.4f}) over {len(df)} races')
ok = Lf.groupby('race_id').proj.transform(lambda s: pd.to_numeric(s, errors='coerce').notna().all())
sub = Lf[ok]
print(f'  on the {sub.race_id.nunique()} races where every runner has a dashboard Proj:')
lp = metrics(sub, softmax(sub, pd.to_numeric(sub.proj), 0.20, 'rk'), 'dashboard Proj (beta 0.20)')
for name in MODELS:
    l = metrics(sub, P2[name][sub.index], name)
    df = l - lp
    print(f'      {name} minus Proj: {df.mean():+.4f} (se {df.std() / np.sqrt(len(df)):.4f})')
price_gain(Lf, P2, Lf.price, 'T2 real page-scale fields, logged price')
for nm, (m, T, fl) in MODELS.items():
    m.save_model('/tmp/direct_v3_%s.txt' % nm.split()[0])
json.dump({n: {'T': T, 'feats': fl} for n, (m, T, fl) in MODELS.items()}, open('/tmp/direct_v3_meta.json', 'w'))
Lf.assign(**{('p_' + n.split()[0]): P2[n] for n in MODELS}).drop(columns=['hist']).to_pickle('/tmp/direct_v3_T2.pkl')
te.assign(**{('p_' + n.split()[0]): P1[n] for n in MODELS}).to_pickle('/tmp/direct_v3_T1.pkl')
