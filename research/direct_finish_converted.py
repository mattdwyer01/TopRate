"""Direct finishing-position model trained on CONVERTED full fields, tested on real page-scale (ATW) fields (26 Oct 2026).
Follow-up to direct_finish_model_study.py (plain ratings, +0.040 nats over the rating-then-softmax route) and to the converted-history Proj test:
 - training: results files 2019-06 on, complete fields. Every rating input of a row (last runs' ratings) is put on the scale a runner page would show for THAT race:
   plain wpr + c_t, c_t = 0.8 x (AR 168 standard weight for the race - weight carried after claim) (wfa_scale.atw_offset). Rating-route target = wpr + c_t.
 - NO jockey / trainer rate inputs (the live log's names are not in the results files' format), class as the page code (ctx.class_code), n_runs capped at 12.
 - models: A rating route (Huber regression, softmax), B1 direct win (binary), B2 lambdarank on finishing position. Fit before 2024-07, early stop 2024 H2.
 - T1: results-file races 2025-01 on (converted inputs, full fields).
 - T2 (the transfer test): data/direct_log races with a result whose whole field is logged: inputs are the REAL page ratings (no conversion), features built exactly as
   in training. Also scored: the dashboard's Proj and Nett at beta 0.20 and the closing price (reference only).
  PYTHONPATH=. python research/direct_finish_converted.py
"""
import glob, gzip, json, os, sys
import lightgbm as lgb, numpy as np, pandas as pd
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'projection'))
import wfa_scale as W
import ctx as C

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SEX = {'G': 0, 'M': 1, 'F': 2, 'C': 3, 'H': 4, 'R': 5}
cols = ['race_id', 'horse_id', 'date', 'distance', 'going', 'wpr', 'weightCarried', 'barrier', 'marginFinish', 'positionFinish', 'race_class',
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


print('computing per-row shifts for', len(r), 'runs ...', flush=True)
r['c_t'] = offs(r)
print(f'c_t known on {r.c_t.notna().mean():.3f}, mean {r.c_t.mean():+.2f} sd {r.c_t.std():.2f}', flush=True)
g = r.groupby('horse_id')
lw = pd.concat([g.wpr.shift(k) for k in range(1, 9)], axis=1)
ct = r.c_t.fillna(0.0)
F = {}
for k in range(6):
    F[f'w{k + 1}'] = lw.iloc[:, k] + ct
F['m3_wpr'] = lw.iloc[:, :3].mean(axis=1) + ct
F['m8_wpr'] = lw.mean(axis=1) + ct
F['max8_wpr'] = lw.max(axis=1) + ct
F['s8_wpr'] = lw.std(axis=1)
for c in ('mfin', 'finpct'):
    lg = pd.concat([g[c].shift(k) for k in range(1, 5)], axis=1)
    F['p1_' + c] = lg.iloc[:, 0]
    F['m4_' + c] = lg.mean(axis=1)
F['days'] = g.date.diff().dt.days
F['wchg'] = r.weightCarried - g.weightCarried.shift(1)
F['dchg'] = r.distance - g.distance.shift(1)
F['n_runs'] = g.cumcount().astype(float).clip(upper=12)
F = pd.DataFrame(F)
d = pd.concat([r, F], axis=1)
d['win'] = (d.pos == 1).astype(float)
d['top3'] = (d.pos <= 3).astype(float)
d['tgt'] = d.wpr + ct
CLASSES = d.loc[d.date < '2024-07-01', 'clsc'].value_counts()
CLASSES = CLASSES[CLASSES >= 200].index.tolist()

BASE = [f'w{k}' for k in range(1, 7)] + ['m3_wpr', 'm8_wpr', 'max8_wpr', 's8_wpr', 'p1_mfin', 'm4_mfin', 'p1_finpct', 'm4_finpct', 'days', 'wchg', 'dchg', 'n_runs',
                                           'weightCarried', 'barfrac', 'nr', 'distance', 'gs', 'cls', 'horse_age', 'sex']
RELC = ['w1', 'm3_wpr', 'm8_wpr', 'max8_wpr', 'm4_mfin', 'm4_finpct', 'days', 'weightCarried', 'barfrac', 'horse_age']


def finish_features(df):
    """df has BASE columns except cls (set from clsc) and a race key `rk`; adds the field-relative columns."""
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
te = d[d.date >= '2025-01-01']
print(f'fit {len(tr):,} runs / {tr.race_id.nunique():,} races; val {va.race_id.nunique():,}; test {te.race_id.nunique():,} races', flush=True)
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


def metrics(df, p, name, key='race_id'):
    df = df.assign(p=np.asarray(p))
    win_ll = np.log(df.loc[df.win == 1, 'p'].clip(1e-9)).mean()
    rk = df.groupby(key).p.rank(ascending=False, method='first')
    top1 = df.loc[rk == 1, 'win'].mean()
    w_top3 = df.loc[df.win == 1].assign(rk=rk).rk.le(3).mean()
    cap = df.assign(rk=rk).loc[lambda x: x.rk <= 3].groupby(key).top3.sum().div(3).mean()
    print(f'{name:34s} winner LL {win_ll:8.4f}  top pick {top1:6.1%}  winner in top3 {w_top3:6.1%}  top3 captured {cap:6.1%}', flush=True)


mA = lgb.LGBMRegressor(objective='huber', alpha=4.0, **P).fit(tr[feats], tr.tgt.fillna(tr.tgt.mean()), eval_set=[(va[feats], va.tgt.fillna(va.tgt.mean()))], callbacks=ES())
T_A = fit_T(va, mA.predict(va[feats]))
mB1 = lgb.LGBMClassifier(**P).fit(tr[feats], tr.win, eval_set=[(va[feats], va.win)], callbacks=ES())
lgt = lambda m, x: np.log(m.predict_proba(x[feats])[:, 1].clip(1e-9))
T_B1 = fit_T(va, lgt(mB1, va))


def rank_set(df):
    lab = np.where(df.pos.values <= 1, 4, np.where(df.pos.values <= 2, 3, np.where(df.pos.values <= 3, 2, np.where(df.pos.values <= 4, 1, 0))))
    return lgb.Dataset(df[feats], label=lab, group=df.groupby('race_id', sort=False).size().values)


Pr = dict(objective='lambdarank', learning_rate=0.05, num_leaves=63, min_data_in_leaf=200, feature_fraction=0.5, bagging_fraction=0.7, bagging_freq=1, lambda_l2=10, verbose=-1,
          lambdarank_truncation_level=5, eval_at=[1], metric='ndcg')
mB2 = lgb.train(Pr, rank_set(tr), num_boost_round=2000, valid_sets=[rank_set(va)], callbacks=ES())
T_B2 = fit_T(va, mB2.predict(va[feats]))
print(f'trees A {mA.best_iteration_} B1 {mB1.best_iteration_} B2 {mB2.best_iteration}; temperatures A {T_A:.3f} B1 {T_B1:.3f} B2 {T_B2:.3f}', flush=True)


def scores(x):
    return dict(A=softmax(x, mA.predict(x[feats]), T_A, 'rk'), B1=softmax(x, lgt(mB1, x), T_B1, 'rk'), B2=softmax(x, mB2.predict(x[feats]), T_B2, 'rk'))


print('\nT1: results-file races 2025-01 on, converted inputs, full fields')
s1 = scores(te)
for k_, nm in (('A', 'A  rating route'), ('B1', 'B1 direct win'), ('B2', 'B2 direct ranking')):
    metrics(te, s1[k_], nm)
metrics(te, (s1['B1'] + s1['B2']) / 2, 'B1+B2 average')

# T2: real page-scale fields from the log
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
feat_rows = []
for x in L.itertuples():
    h = list(x.hist or [])[::-1]            # most recent first
    rt = [a.get('wpr') for a in h]
    rt = [v if v is not None else np.nan for v in rt] + [np.nan] * 12
    mf = [min(max(a.get('marginFinish') if a.get('marginFinish') is not None else np.nan, 0), 30) for a in h] + [np.nan] * 4
    fp = [((a['positionFinish'] - 1) / (a['starters'] - 1)) if a.get('positionFinish') and a.get('starters') and a['starters'] > 1 else np.nan for a in h] + [np.nan] * 4
    last = h[0] if h else None
    arr8 = np.array(rt[:8], dtype=float)
    feat_rows.append(dict(w1=rt[0], w2=rt[1], w3=rt[2], w4=rt[3], w5=rt[4], w6=rt[5], m3_wpr=np.nanmean(rt[:3]) if np.isfinite(rt[:3]).any() else np.nan,
                          m8_wpr=np.nanmean(arr8) if np.isfinite(arr8).any() else np.nan, max8_wpr=np.nanmax(arr8) if np.isfinite(arr8).any() else np.nan,
                          s8_wpr=np.nanstd(arr8, ddof=1) if np.isfinite(arr8).sum() > 1 else np.nan,
                          p1_mfin=mf[0], m4_mfin=np.nanmean(mf[:4]) if np.isfinite(mf[:4]).any() else np.nan,
                          p1_finpct=fp[0], m4_finpct=np.nanmean(fp[:4]) if np.isfinite(fp[:4]).any() else np.nan,
                          days=(x.date - pd.Timestamp(last['date'])).days if last else np.nan,
                          wchg=(x.weight - last['weightCarried']) if last and last.get('weightCarried') is not None and x.weight is not None else np.nan,
                          dchg=(x.distance - last['distance']) if last and last.get('distance') is not None else np.nan,
                          n_runs=float(min(len(h), 12))))
Lf = pd.concat([L.reset_index(drop=True), pd.DataFrame(feat_rows)], axis=1)
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
print(f'\nT2: real page-scale fields from the log, {Lf.race_id.nunique()} complete labelled races, {len(Lf)} runners, 3+ earlier runs on {(Lf.n_runs >= 3).mean():.1%}')
s2 = scores(Lf)
for k_, nm in (('A', 'A  rating route'), ('B1', 'B1 direct win'), ('B2', 'B2 direct ranking')):
    metrics(Lf, s2[k_], nm)
metrics(Lf, (s2['B1'] + s2['B2']) / 2, 'B1+B2 average')
for col, nm in (('proj', 'dashboard Proj (beta 0.20)'), ('nett', 'Nett (beta 0.20)')):
    ok = Lf.groupby('race_id')[col].transform(lambda s: s.notna().all())
    sub = Lf[ok]
    if sub.race_id.nunique() > 50:
        metrics(sub, softmax(sub, pd.to_numeric(sub[col]), 0.20, 'rk'), f'{nm}, {sub.race_id.nunique()} races')
        metrics(sub, s2['B1'][sub.index], 'B1 on those races')
        metrics(sub, s2['A'][sub.index], 'A  on those races')
pr = pd.to_numeric(Lf.price, errors='coerce')
okp = pr.groupby(Lf.race_id).transform(lambda s: s.notna().all())
sub = Lf[okp]
if sub.race_id.nunique() > 50:
    ip = 1 / pr[okp]
    metrics(sub, ip / ip.groupby(sub.race_id).transform('sum'), f'market (logged price), {sub.race_id.nunique()} races')
Lf.assign(pA=s2['A'], pB1=s2['B1'], pB2=s2['B2']).drop(columns=['hist']).to_pickle('/tmp/direct_conv_T2.pkl')
for nm, m in (('A', mA.booster_), ('B1', mB1.booster_), ('B2', mB2)):
    m.save_model(f'/tmp/direct_conv_{nm}.txt')
json.dump({'T_A': T_A, 'T_B1': T_B1, 'T_B2': T_B2, 'feats': feats, 'classes': CLASSES}, open('/tmp/direct_conv_meta.json', 'w'))
