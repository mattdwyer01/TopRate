"""Direct finishing-position model v2 (26 Oct 2026): jockey / trainer rates, more form inputs, a listwise winner loss, and a VALUE read, not only top pick.
Builds on direct_finish_converted.py (converted full fields, per-row ATW shift c_t on every rating input, page-scale live fields for the transfer test).
New inputs: jockey and trainer as-of win rates (cumulative and 90 days, names normalised to initial + surname so the log's full names match the results files),
career-ish form (win and place share over the last 8, rating trend, same class as last run, jockey changed). New models: B3 = LightGBM with a custom per-race softmax loss
(directly the winner log-lik), B4 = rank_xendcg. B1 (binary win) and B2 (lambdarank) kept.
Value read (the user's point: a runner near the top that pays well can be the bet): (a) does the model add information to the closing price (conditional logit of ln market + ln model,
cross-fitted by date halves, gain in winner log-lik); (b) calibration by model rank and by price band; (c) flat ROI at SP of blended-probability overlays among the model's top 4, with
the usual halves / excluding-biggest-winners checks. T1 = results files 2025-01 on with clean books; T2 = the log's complete page-scale fields (logged price).
  PYTHONPATH=.:projection python research/direct_finish_v2.py
"""
import glob, gzip, json, os, re, sys
import lightgbm as lgb, numpy as np, pandas as pd
from scipy.optimize import minimize
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'projection'))
import wfa_scale as W
import ctx as C

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SEX = {'G': 0, 'M': 1, 'F': 2, 'C': 3, 'H': 4, 'R': 5}


def nk(x):
    """Name key: first initial + last word, lower case (results files print 'C J Parish' or 'Carleen Hefel', the log prints full names)."""
    if not isinstance(x, str):
        return None
    t = re.sub(r"[^A-Za-z\s'-]", '', x).split()
    if not t:
        return None
    return (t[0][0] + t[-1]).lower().replace("'", '').replace('-', '')


def asof_rate(df, key, value, window_days=None, prior=0.1, k=50):
    v = df[value]
    t = pd.DataFrame({'key': df[key].values, 'date': df.date.values, 'v': v.values}).dropna(subset=['key', 'v'])
    a = t.groupby(['key', 'date']).v.agg(['sum', 'count']).reset_index().sort_values(['key', 'date'])
    a['cs'] = a.groupby('key')['sum'].cumsum()
    a['cn'] = a.groupby('key')['count'].cumsum()
    q = pd.DataFrame({'key': df[key].values, 'date': df.date.values, '_i': np.arange(len(df))})
    q = q.dropna(subset=['key'])
    m = pd.merge_asof(q.sort_values('date'), a[['key', 'date', 'cs', 'cn']].sort_values('date'), on='date', by='key', allow_exact_matches=False)
    cs, cn = m.cs.fillna(0).values, m.cn.fillna(0).values
    if window_days:
        q2 = q.assign(date=q.date - pd.Timedelta(days=window_days))
        m2 = pd.merge_asof(q2.sort_values('date'), a[['key', 'date', 'cs', 'cn']].sort_values('date'), on='date', by='key', allow_exact_matches=False)
        cs, cn = cs - m2.cs.fillna(0).values, cn - m2.cn.fillna(0).values
    out = np.full(len(df), np.nan)
    out[m._i.values] = (cs + prior * k) / (cn + k)
    return out


cols = ['race_id', 'horse_id', 'date', 'distance', 'going', 'wpr', 'weightCarried', 'barrier', 'marginFinish', 'positionFinish', 'race_class', 'jockey', 'trainer',
        'horse_age', 'horse_sex', 'horse_foaled', 'isBarrierTrial', 'is_jumpout', 'priceStarting']
fs = sorted(glob.glob(os.path.join(ROOT, 'race_results_20[12]?.csv.gz')))
r = pd.concat([pd.read_csv(f, usecols=lambda c: c in cols, low_memory=False) for f in fs], ignore_index=True)
r = r[~r.isBarrierTrial.astype(bool) & ~r.is_jumpout.fillna(False).astype(bool)]
r['date'] = pd.to_datetime(r.date)
r = r[r.date >= '2019-06-01'].drop_duplicates(['race_id', 'horse_id']).sort_values(['horse_id', 'date', 'race_id']).reset_index(drop=True)
r['nr'] = r.groupby('race_id').horse_id.transform('size')
r['pos'] = pd.to_numeric(r.positionFinish, errors='coerce')
r['gs'] = pd.to_numeric(r.going.astype(str).str.extract(r'(\d+)')[0], errors='coerce')
r['finpct'] = (r.pos - 1) / (r.nr - 1)
r['mfin'] = pd.to_numeric(r.marginFinish, errors='coerce').clip(0, 30)
r['barfrac'] = (r.barrier - 1) / (r.nr - 1)
r['sex'] = r.horse_sex.astype(str).str.upper().str[:1].map(SEX)
r['wpr'] = pd.to_numeric(r.wpr, errors='coerce')
r['clsc'] = C.class_code(r.race_class)
r['jk'] = r.jockey.map(nk)
r['tk'] = r.trainer.map(nk)
r['winf'] = np.where(r.pos.notna(), (r.pos == 1).astype(float), np.nan)


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


print('shifts and rates for', len(r), 'runs ...', flush=True)
r['c_t'] = offs(r)
# jockey / trainer rates: the results files plus the racing.com results file (9 to 17 Oct) as history for the live rows
rc = pd.read_csv(os.path.join(ROOT, 'race_results_2026_rc.csv.gz'), usecols=lambda c: c in ('date', 'jockey', 'trainer', 'positionFinish', 'isBarrierTrial'), low_memory=False)
rc = rc[~rc.isBarrierTrial.astype(str).isin(['True', '1'])]
rc['date'] = pd.to_datetime(rc.date)
rc['pos'] = pd.to_numeric(rc.positionFinish, errors='coerce')
rc['jk'], rc['tk'] = rc.jockey.map(nk), rc.trainer.map(nk)
rc['winf'] = np.where(rc.pos.notna(), (rc.pos == 1).astype(float), np.nan)
rc = rc[rc.date > r.date.max()]
H = pd.concat([r[['date', 'jk', 'tk', 'winf']], rc[['date', 'jk', 'tk', 'winf']]], ignore_index=True)   # rate history
nr_ = len(r)
r['jw'] = asof_rate(r, 'jk', 'winf')
r['jw90'] = asof_rate(r, 'jk', 'winf', window_days=90, k=30)
r['tw'] = asof_rate(r, 'tk', 'winf')
r['tw90'] = asof_rate(r, 'tk', 'winf', window_days=90, k=30)
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
F = pd.DataFrame(F)
d = pd.concat([r, F], axis=1)
d['win'] = (d.pos == 1).astype(float)
d['top3'] = (d.pos <= 3).astype(float)
d['tgt'] = d.wpr + ct
CLASSES = d.loc[d.date < '2024-07-01', 'clsc'].value_counts()
CLASSES = CLASSES[CLASSES >= 200].index.tolist()
BASE = [f'w{k}' for k in range(1, 7)] + ['m3_wpr', 'm8_wpr', 'max8_wpr', 's8_wpr', 'trend', 'p1_mfin', 'm4_mfin', 'p1_finpct', 'm4_finpct', 'win8', 'plc8', 'days', 'wchg', 'dchg', 'n_runs',
        'weightCarried', 'barfrac', 'nr', 'distance', 'gs', 'cls', 'horse_age', 'sex', 'cls_same', 'jock_chg', 'jw', 'jw90', 'tw', 'tw90']
RELC = ['w1', 'm3_wpr', 'm8_wpr', 'max8_wpr', 'm4_mfin', 'm4_finpct', 'days', 'weightCarried', 'barfrac', 'horse_age', 'jw', 'jw90', 'tw', 'tw90', 'win8', 'plc8']


def finish_features(df):
    df = df.copy()
    df['cls'] = pd.Categorical(df.clsc, categories=CLASSES).codes.astype(float)
    df.loc[df.cls < 0, 'cls'] = np.nan
    gk = df.groupby('rk')
    rel = {}
    for c in RELC:
        rel['r_' + c] = df[c] - gk[c].transform('mean')
        rel['k_' + c] = gk[c].rank(pct=True)
    rel['gap_top_m3'] = df.m3_wpr - gk.m3_wpr.transform('max')
    rel['gap_top_m8'] = df.m8_wpr - gk.m8_wpr.transform('max')
    return pd.concat([df, pd.DataFrame(rel, index=df.index)], axis=1), BASE + list(rel)


d['rk'] = d.race_id
d, feats = finish_features(d)
nw = d.groupby('race_id').win.transform('sum')
d = d[(nw == 1) & (d.nr >= 5) & d.pos.notna()].copy().sort_values(['date', 'race_id']).reset_index(drop=True)
tr = d[(d.date >= '2021-01-01') & (d.date < '2024-07-01')]
va = d[(d.date >= '2024-07-01') & (d.date < '2025-01-01')]
te = d[d.date >= '2025-01-01'].copy()
print(f'fit {len(tr):,} runs / {tr.race_id.nunique():,} races; val {va.race_id.nunique():,}; test {te.race_id.nunique():,} races; {len(feats)} inputs', flush=True)
P = dict(learning_rate=0.05, num_leaves=63, min_child_samples=200, subsample=0.7, subsample_freq=1, colsample_bytree=0.5, reg_lambda=10, verbose=-1, n_estimators=2000)
ES = lambda: [lgb.early_stopping(60, verbose=False)]


def softmax(df, s, T, key='race_id'):
    z = pd.Series(np.asarray(s) * T, index=df.index)
    e = np.exp(z - z.groupby(df[key]).transform('max'))
    return e / e.groupby(df[key]).transform('sum')


def fit_T(df, s):
    best = None
    for T in np.exp(np.linspace(np.log(0.01), np.log(5), 40)):
        p = softmax(df, s, T)
        ll = np.log(p[df.win == 1].clip(1e-9)).mean()
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


def rank_set(df, labels='graded'):
    lab = np.where(df.pos.values <= 1, 4, np.where(df.pos.values <= 2, 3, np.where(df.pos.values <= 3, 2, np.where(df.pos.values <= 4, 1, 0))))
    return lgb.Dataset(df[feats], label=lab, group=df.groupby('race_id', sort=False).size().values)


def metrics(df, p, name, key='race_id', quiet=False):
    df = df.assign(p=np.asarray(p))
    win_ll = np.log(df.loc[df.win == 1, 'p'].clip(1e-9)).mean()
    rk = df.groupby(key).p.rank(ascending=False, method='first')
    top1 = df.loc[rk == 1, 'win'].mean()
    w_top3 = df.loc[df.win == 1].assign(rk=rk).rk.le(3).mean()
    w_top4 = df.loc[df.win == 1].assign(rk=rk).rk.le(4).mean()
    cap = df.assign(rk=rk).loc[lambda x: x.rk <= 3].groupby(key).top3.sum().div(3).mean()
    if not quiet:
        print(f'{name:30s} winner LL {win_ll:8.4f}  top pick {top1:6.1%}  winner in top3 {w_top3:6.1%} top4 {w_top4:6.1%}  top3 captured {cap:6.1%}', flush=True)
    return win_ll


mB1 = lgb.LGBMClassifier(**P).fit(tr[feats], tr.win, eval_set=[(va[feats], va.win)], callbacks=ES())
lgt = lambda m, x: np.log(m.predict_proba(x[feats])[:, 1].clip(1e-9))
T_B1 = fit_T(va, lgt(mB1, va))
Pr = dict(objective='lambdarank', learning_rate=0.05, num_leaves=63, min_data_in_leaf=200, feature_fraction=0.5, bagging_fraction=0.7, bagging_freq=1, lambda_l2=10, verbose=-1,
          lambdarank_truncation_level=5, eval_at=[1], metric='ndcg')
mB2 = lgb.train(Pr, rank_set(tr), num_boost_round=2000, valid_sets=[rank_set(va)], callbacks=ES())
T_B2 = fit_T(va, mB2.predict(va[feats]))
P3 = dict(learning_rate=0.03, num_leaves=63, min_data_in_leaf=200, feature_fraction=0.5, bagging_fraction=0.7, bagging_freq=1, lambda_l2=10, verbose=-1, objective=softmax_obj(tr), metric='None')
dtr = lgb.Dataset(tr[feats], label=tr.win.values)
dva = lgb.Dataset(va[feats], label=va.win.values, reference=dtr)
mB3 = lgb.train(P3, dtr, num_boost_round=3000, valid_sets=[dva], feval=softmax_eval(va), callbacks=[lgb.early_stopping(80, verbose=False)])
T_B3 = fit_T(va, mB3.predict(va[feats]))
P4 = {**Pr, 'objective': 'rank_xendcg'}
mB4 = lgb.train(P4, rank_set(tr), num_boost_round=2000, valid_sets=[rank_set(va)], callbacks=ES())
T_B4 = fit_T(va, mB4.predict(va[feats]))
print(f'trees B1 {mB1.best_iteration_} B2 {mB2.best_iteration} B3 {mB3.best_iteration} B4 {mB4.best_iteration}; T {T_B1:.3f} {T_B2:.3f} {T_B3:.3f} {T_B4:.3f}', flush=True)
MODELS = {'B1 direct win': (lambda x: lgt(mB1, x), T_B1), 'B2 lambdarank': (lambda x: mB2.predict(x[feats]), T_B2),
          'B3 softmax loss': (lambda x: mB3.predict(x[feats]), T_B3), 'B4 xendcg': (lambda x: mB4.predict(x[feats]), T_B4)}


def scores(x, key):
    out = {k: softmax(x, f(x), T, key) for k, (f, T) in MODELS.items()}
    out['avg B1+B3'] = (out['B1 direct win'] + out['B3 softmax loss']) / 2
    out['avg all'] = sum(out[k] for k in MODELS) / len(MODELS)
    return out


print('\nT1: results-file races 2025-01 on, full fields')
s1 = scores(te, 'rk')
for k_, p in s1.items():
    metrics(te, p, k_)
imp = pd.Series(mB3.feature_importance('gain'), index=feats).sort_values(ascending=False)
print('B3 top inputs by gain:', ', '.join(f'{k} {v / imp.sum():.1%}' for k, v in imp.head(12).items()))


# ---------------- value read ----------------
def cond_logit(df, cols_, key):
    """Race-level softmax with one coefficient per column; returns coefficients fitted on df."""
    sizes = df.groupby(key, sort=False).size().values
    starts = np.concatenate([[0], np.cumsum(sizes)[:-1]])
    X = df[cols_].values
    y = df.win.values

    def nll(b):
        s = X @ b
        z = s - np.repeat(np.maximum.reduceat(s, starts), sizes)
        e = np.exp(z)
        lse = np.log(np.add.reduceat(e, starts))
        return -(s[y == 1] - np.repeat(np.maximum.reduceat(s, starts), sizes)[y == 1] - lse).mean()
    res = minimize(nll, np.ones(len(cols_)) * 0.5, method='BFGS')
    return res.x


def apply_cl(df, cols_, b, key):
    s = pd.Series(df[cols_].values @ b, index=df.index)
    e = np.exp(s - s.groupby(df[key]).transform('max'))
    return e / e.groupby(df[key]).transform('sum')


def value_read(df, probs, price, key, label):
    df = df.assign(pr=pd.to_numeric(price, errors='coerce'))
    ok = df.groupby(key).pr.transform(lambda s: s.notna().all() and 1.05 <= (1 / s).sum() <= 2.0)
    df = df[ok].copy()
    nrace = df[key].nunique()
    ip = 1 / df.pr
    df['mk'] = ip / ip.groupby(df[key]).transform('sum')
    df['lmk'] = np.log(df.mk)
    half = (df.date >= df.date.median()).values
    print(f'\nVALUE READ, {label}: {nrace} clean-book races with a price for every runner')
    print('  model vs the price: winner LL of (a) price alone, (b) price + model (conditional logit, fitted on one date half, scored on the other), gain per race with se')
    base_ll = None
    rows = []
    blended = {}
    for name, p in probs.items():
        df['lm'] = np.log(p[df.index].clip(1e-9))
        out = pd.Series(np.nan, index=df.index)
        coefs = []
        for a_, b_ in ((~half, half), (half, ~half)):
            fit = df[a_]
            bco = cond_logit(fit, ['lmk', 'lm'], key)
            out[b_] = apply_cl(df[b_], ['lmk', 'lm'], bco, key)
            coefs.append(bco)
        win = df.win == 1
        ll_b = np.log(out[win].clip(1e-9))
        ll_m = np.log(df.mk[win].clip(1e-9))
        gain = (ll_b - ll_m)
        rows.append((name, ll_m.mean(), ll_b.mean(), gain.mean(), gain.std() / np.sqrt(len(gain)), np.mean([c[1] for c in coefs]), np.mean([c[0] for c in coefs])))
        blended[name] = out
    for name, llm, llb, gn, se, bm, bk in rows:
        print(f'  {name:18s} price only {llm:8.4f}  price+model {llb:8.4f}  gain {gn:+.4f} (se {se:.4f})  weights: price {bk:.2f} model {bm:.2f}')
    best = max(rows, key=lambda x: x[3])[0]
    pb = blended[best]
    print(f'  --- best blend: {best}')
    df['pb'] = pb
    df['rank_m'] = probs[best][df.index].groupby(df[key]).rank(ascending=False, method='first')
    df['ev'] = df.pb * df.pr
    print('  calibration of the blended probability by model rank (predicted vs actual win rate; ROI at the quoted price)')
    for lo, hi in ((1, 1), (2, 2), (3, 3), (4, 4), (5, 99)):
        x = df[(df.rank_m >= lo) & (df.rank_m <= hi)]
        print(f'    model rank {lo}{"" if lo == hi else "-" + str(hi) if hi < 99 else "+"}: n {len(x):6d}  predicted {x.pb.mean():.3f} actual {x.win.mean():.3f}  avg price ${x.pr[x.win == 1].mean():.2f}  flat ROI {(x.win * x.pr - 1).mean():+.1%}')
    print('  overlays on the blended probability (EV = blended p x price), flat $1, with robustness')
    for scope, mask in (('any runner', df.rank_m >= 1), ('model top 4 only', df.rank_m <= 4), ('model rank 2-4 only', (df.rank_m >= 2) & (df.rank_m <= 4))):
        for th in (1.0, 1.05, 1.10, 1.20):
            x = df[mask & (df.ev > th)]
            if len(x) < 40:
                continue
            ret = x.win * x.pr - 1
            hh = (x.date >= df.date.median()).values
            top3 = x[x.win == 1].pr.nlargest(3).sum()
            ex3 = (ret.sum() - (top3 - 3)) / (len(x) - 3) if x.win.sum() >= 3 else np.nan
            print(f'    {scope:19s} EV>{th:.2f}: bets {len(x):5d} ({len(x) / nrace:.2f}/race)  win {x.win.mean():5.1%}  avg price ${x.pr.mean():6.2f}  ROI {ret.mean():+6.1%}  halves {ret[~hh].mean():+6.1%}/{ret[hh].mean():+6.1%}  ex3 {ex3:+6.1%}')
    return df


vr1 = value_read(te, s1, te.priceStarting, 'race_id', 'T1 results files, closing price')

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
# jockey / trainer rates for the live rows: history = results + racing.com rows, then the live rows (value NaN) so they get an as-of rate
LH = pd.concat([H, Lr[['date', 'jk', 'tk']].assign(winf=np.nan)], ignore_index=True)
nH = len(H)
jw = asof_rate(LH, 'jk', 'winf')[nH:]
jw90 = asof_rate(LH, 'jk', 'winf', window_days=90, k=30)[nH:]
tw = asof_rate(LH, 'tk', 'winf')[nH:]
tw90 = asof_rate(LH, 'tk', 'winf', window_days=90, k=30)[nH:]
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
    feat_rows.append(dict(w1=rt[0], w2=rt[1], w3=rt[2], w4=rt[3], w5=rt[4], w6=rt[5], m3_wpr=np.nanmean(rt[:3]) if np.isfinite(rt[:3]).any() else np.nan, m8_wpr=m8,
                          max8_wpr=np.nanmax(arr8) if np.isfinite(arr8).any() else np.nan, s8_wpr=np.nanstd(arr8, ddof=1) if np.isfinite(arr8).sum() > 1 else np.nan,
                          trend=(rt[0] - m8) if np.isfinite(rt[0]) else np.nan,
                          p1_mfin=mf[0], m4_mfin=np.nanmean(mf[:4]) if np.isfinite(mf[:4]).any() else np.nan, p1_finpct=fp[0],
                          m4_finpct=np.nanmean(fp[:4]) if np.isfinite(fp[:4]).any() else np.nan,
                          win8=float((pk == 1).sum() / npk) if npk else np.nan, plc8=float((pk <= 3).sum() / npk) if npk else np.nan,
                          days=(x.date - pd.Timestamp(last['date'])).days if last else np.nan,
                          wchg=(x.weight - last['weightCarried']) if last and last.get('weightCarried') is not None and x.weight is not None else np.nan,
                          dchg=(x.distance - last['distance']) if last and last.get('distance') is not None else np.nan, n_runs=float(min(len(h), 12)),
                          cls_same=float(C.class_code(pd.Series([last.get('class')])).iloc[0] == C.class_code(pd.Series([x.race_class])).iloc[0]) if last and last.get('class') else np.nan,
                          jock_chg=float(nk(last.get('jockey')) != x.jk) if last and last.get('jockey') and x.jk else np.nan,
                          jw=jw[i], jw90=jw90[i], tw=tw[i], tw90=tw90[i]))
Lf = pd.concat([Lr, pd.DataFrame(feat_rows)], axis=1)
Lf['weightCarried'] = pd.to_numeric(Lf.weight, errors='coerce')
Lf['barfrac'] = (Lf.barrier - 1) / (Lf.nr - 1)
Lf['distance'] = pd.to_numeric(Lf.distance, errors='coerce')
Lf['gs'] = pd.to_numeric(Lf.going.astype(str).str.extract(r'(\d+)')[0], errors='coerce')
Lf['horse_age'] = pd.to_numeric(Lf.horse_age, errors='coerce')
Lf['sex'] = Lf.horse_sex.astype(str).str.upper().str[:1].map(SEX)
Lf['clsc'] = C.class_code(Lf.race_class)
Lf['rk'] = Lf.race_id
Lf, _ = finish_features(Lf)
Lf['win'] = Lf.won.astype(float)
Lf['pos'] = pd.to_numeric(Lf.finish, errors='coerce')
Lf['top3'] = (Lf.pos <= 3).astype(float)
print(f'\nT2: real page-scale fields from the log, {Lf.race_id.nunique()} complete labelled races, {len(Lf)} runners, 3+ earlier runs on {(Lf.n_runs >= 3).mean():.1%}, '
      f'jockey rate on {Lf.jw.notna().mean():.1%}, trainer rate on {Lf.tw.notna().mean():.1%}')
s2 = scores(Lf, 'rk')
for k_, p in s2.items():
    metrics(Lf, p, k_)
ok = Lf.groupby('race_id').proj.transform(lambda s: pd.to_numeric(s, errors='coerce').notna().all())
sub = Lf[ok]
print(f'  on the {sub.race_id.nunique()} races where every runner has a dashboard Proj:')
metrics(sub, softmax(sub, pd.to_numeric(sub.proj), 0.20, 'rk'), 'dashboard Proj (beta 0.20)')
for k_ in ('B1 direct win', 'B3 softmax loss', 'avg B1+B3', 'avg all'):
    metrics(sub, s2[k_][sub.index], k_)
vr2 = value_read(Lf, s2, Lf.price, 'race_id', 'T2 real page-scale fields, logged price')
for nm, m in (('B1', mB1.booster_), ('B2', mB2), ('B3', mB3), ('B4', mB4)):
    m.save_model(f'/tmp/direct_v2_{nm}.txt')
json.dump({'T': {'B1': T_B1, 'B2': T_B2, 'B3': T_B3, 'B4': T_B4}, 'feats': feats, 'classes': CLASSES}, open('/tmp/direct_v2_meta.json', 'w'))
Lf.assign(**{('p_' + k.split()[0]): v for k, v in s2.items()}).drop(columns=['hist']).to_pickle('/tmp/direct_v2_T2.pkl')
vr1.to_pickle('/tmp/direct_v2_T1_value.pkl')
