"""Direct finishing-position model vs the rating-then-softmax route (26 Oct 2026).
Same as-of inputs for every model (horse's own earlier ratings, margins and finishing percentiles, days, weight, barrier, distance, going, class, age, sex,
jockey and trainer as-of effects, each also relative to the field), NO price. Results files 2020 to 8 Oct 2026, all states, races of 5+ with one winner.
  A  rating route: LightGBM Huber regression on the run's own wpr, then softmax over the field (temperature fitted on 2024 H2), the Proj method
  B1 direct win: binary win LightGBM, probabilities normalised in the race (power fitted on 2024 H2)
  B2 direct ranking: LightGBM lambdarank on finishing position, softmax temperature fitted on 2024 H2
  P  direct place: binary top-3 LightGBM (for the place capture metric of B1/B2/A)
Fit before 2024-07, early stop on 2024 H2, scored on 2025-01 to 8 Oct 2026. Metrics: winner log-lik, top pick win %, winner in top 3, share of the real top 3 captured
by the model's top 3; the closing-price winner log-lik on the same races (clean books) as a reference only.
NB the rating route here uses the results files' plain wpr history, a method test, not the ATW-only Proj of record.
  PYTHONPATH=. python research/direct_finish_model_study.py
"""
import glob, os, sys
import lightgbm as lgb, numpy as np, pandas as pd
sys.path.insert(0, os.path.dirname(__file__))
import closing_stage_study as CS
import last400_predictors_study as S
ROOT = CS.ROOT
cols = ['race_id', 'horse_id', 'date', 'distance', 'going', 'wpr', 'weightCarried', 'barrier', 'marginFinish', 'positionFinish', 'race_class', 'jockey', 'trainer',
        'horse_age', 'horse_sex', 'isBarrierTrial', 'is_jumpout', 'priceStarting']
fs = sorted(glob.glob(os.path.join(ROOT, 'race_results_20[12]?.csv.gz')))
r = pd.concat([pd.read_csv(f, usecols=lambda c: c in cols, low_memory=False) for f in fs], ignore_index=True)
r = r[~r.isBarrierTrial.astype(bool) & ~r.is_jumpout.fillna(False).astype(bool)]
r['date'] = pd.to_datetime(r.date)
r = r[r.date >= '2019-06-01'].drop_duplicates(['race_id', 'horse_id']).sort_values(['horse_id', 'date', 'race_id']).reset_index(drop=True)
r['nr'] = r.groupby('race_id').horse_id.transform('size')
r['pos'] = pd.to_numeric(r.positionFinish, errors='coerce')
r['gs'] = pd.to_numeric(r.going.astype(str).str.extract(r'(\d+)')[0], errors='coerce')
r['finpct'] = (r.pos - 1) / (r.nr - 1)
r['mfin'] = r.marginFinish.clip(0, 30)
r['barfrac'] = (r.barrier - 1) / (r.nr - 1)
r['cls'] = r.race_class.astype('category').cat.codes.astype(float)
r['sex'] = r.horse_sex.astype('category').cat.codes.astype(float)
g = r.groupby('horse_id')
F = {}
lw = pd.concat([g.wpr.shift(k) for k in range(1, 9)], axis=1)
for k in range(6):
    F[f'w{k + 1}'] = lw.iloc[:, k]
F['m3_wpr'] = lw.iloc[:, :3].mean(axis=1); F['m8_wpr'] = lw.mean(axis=1); F['max8_wpr'] = lw.max(axis=1); F['s8_wpr'] = lw.std(axis=1)
for c in ('mfin', 'finpct'):
    lg = pd.concat([g[c].shift(k) for k in range(1, 5)], axis=1)
    F['p1_' + c] = lg.iloc[:, 0]; F['m4_' + c] = lg.mean(axis=1)
F['days'] = g.date.diff().dt.days
F['wchg'] = r.weightCarried - g.weightCarried.shift(1)
F['dchg'] = r.distance - g.distance.shift(1)
F['n_runs'] = g.cumcount().astype(float)
F = pd.DataFrame(F)
d = pd.concat([r, F], axis=1)
r['win'] = (r.pos == 1).astype(float); d['win'] = r.win; d['top3'] = (r.pos <= 3).astype(float)
d['jw'], _ = S.asof_rate(d.assign(k=d.jockey.astype(str)), 'k', None, prior=0.1, k=50, value='win')
d['tw'], _ = S.asof_rate(d.assign(k=d.trainer.astype(str)), 'k', None, prior=0.1, k=50, value='win')
base = [f'w{k}' for k in range(1, 7)] + ['m3_wpr', 'm8_wpr', 'max8_wpr', 's8_wpr', 'p1_mfin', 'm4_mfin', 'p1_finpct', 'm4_finpct', 'days', 'wchg', 'dchg', 'n_runs',
        'weightCarried', 'barfrac', 'nr', 'distance', 'gs', 'cls', 'horse_age', 'sex', 'jw', 'tw']
gk = d.groupby('race_id')
rel = {}
for c in ['w1', 'm3_wpr', 'm8_wpr', 'max8_wpr', 'm4_mfin', 'm4_finpct', 'days', 'weightCarried', 'jw', 'tw', 'barfrac', 'horse_age']:
    rel['r_' + c] = d[c] - gk[c].transform('mean'); rel['k_' + c] = gk[c].rank(pct=True)
rel['gap_top_m3'] = d.m3_wpr - gk.m3_wpr.transform('max'); rel['gap_top_m8'] = d.m8_wpr - gk.m8_wpr.transform('max')
d = pd.concat([d, pd.DataFrame(rel)], axis=1)
feats = base + list(rel)
# races: one winner, 5+ runners, winner and all runners finishing known
nw = gk.win.transform('sum'); d = d[(nw == 1) & (d.nr >= 5) & d.pos.notna()].copy()
d = d.sort_values(['date', 'race_id']).reset_index(drop=True)
tr = d[(d.date >= '2021-01-01') & (d.date < '2024-07-01')]; va = d[(d.date >= '2024-07-01') & (d.date < '2025-01-01')]; te = d[d.date >= '2025-01-01']
print(f'fit {len(tr):,} runs / {tr.race_id.nunique():,} races; val {va.race_id.nunique():,}; test {te.race_id.nunique():,} races', flush=True)
P = dict(learning_rate=0.05, num_leaves=63, min_child_samples=200, subsample=0.7, subsample_freq=1, colsample_bytree=0.5, reg_lambda=10, verbose=-1, n_estimators=2000)
ES = lambda: [lgb.early_stopping(60, verbose=False)]


def softmax_ll(df, s, T):
    z = (df.assign(_s=s * T)).groupby('race_id')._s
    e = np.exp(df.assign(_s=s * T)._s - z.transform('max'))
    return e / e.groupby(df.race_id).transform('sum')


def fit_T(df, s):
    best = None
    for T in np.exp(np.linspace(np.log(0.01), np.log(5), 40)):
        p = softmax_ll(df, s, T); ll = np.log(p[df.win == 1].clip(1e-9)).mean()
        if best is None or ll > best[0]:
            best = (ll, T)
    return best[1]


def metrics(df, p, name):
    df = df.assign(p=p)
    win_ll = np.log(df.loc[df.win == 1, 'p'].clip(1e-9)).mean()
    rk = df.groupby('race_id').p.rank(ascending=False, method='first')
    top1 = df.loc[rk == 1, 'win'].mean()
    w_top3 = df.loc[(df.win == 1)].assign(rk=rk).rk.le(3).mean()
    cap = df.assign(rk=rk).loc[lambda x: x.rk <= 3].groupby('race_id').top3.sum().div(3).mean()
    print(f'{name:34s} winner LL {win_ll:8.4f}  top pick {top1:6.1%}  winner in top3 {w_top3:6.1%}  top3 captured {cap:6.1%}', flush=True)
    return win_ll


# A: rating route
mA = lgb.LGBMRegressor(objective='huber', alpha=4.0, **P).fit(tr[feats], tr.wpr.fillna(tr.wpr.mean()), eval_set=[(va[feats], va.wpr.fillna(va.wpr.mean()))], callbacks=ES())
T_A = fit_T(va, mA.predict(va[feats])); pA = softmax_ll(te, mA.predict(te[feats]), T_A)
# B1: direct win
mB1 = lgb.LGBMClassifier(**P).fit(tr[feats], tr.win, eval_set=[(va[feats], va.win)], callbacks=ES())
sB1 = np.log(mB1.predict_proba(va[feats])[:, 1].clip(1e-9)); T_B1 = fit_T(va, sB1)
pB1 = softmax_ll(te, np.log(mB1.predict_proba(te[feats])[:, 1].clip(1e-9)), T_B1)
# B2: lambdarank on finishing position
def rank_set(df):
    lab = np.clip(df.nr.values - df.pos.values, 0, 30).astype(int)
    return lgb.Dataset(df[feats], label=np.where(df.pos.values <= 1, 4, np.where(df.pos.values <= 2, 3, np.where(df.pos.values <= 3, 2, np.where(df.pos.values <= 4, 1, 0)))),
                       group=df.groupby('race_id', sort=False).size().values)
Pr = dict(objective='lambdarank', learning_rate=0.05, num_leaves=63, min_data_in_leaf=200, feature_fraction=0.5, bagging_fraction=0.7, bagging_freq=1, lambda_l2=10, verbose=-1,
          lambdarank_truncation_level=5, eval_at=[1], metric='ndcg')
mB2 = lgb.train(Pr, rank_set(tr), num_boost_round=2000, valid_sets=[rank_set(va)], callbacks=ES())
T_B2 = fit_T(va, mB2.predict(va[feats])); pB2 = softmax_ll(te, mB2.predict(te[feats]), T_B2)
# P: direct place
mP = lgb.LGBMClassifier(**P).fit(tr[feats], tr.top3, eval_set=[(va[feats], va.top3)], callbacks=ES())
pP = pd.Series(mP.predict_proba(te[feats])[:, 1], index=te.index)
print(f'trees A {mA.best_iteration_}  B1 {mB1.best_iteration_}  B2 {mB2.best_iteration}  P {mP.best_iteration_}; temperatures A {T_A:.3f} B1 {T_B1:.3f} B2 {T_B2:.3f}')
print('\nALL TEST RACES (2025-01 to 8 Oct 2026)')
metrics(te, pA, 'A  rating route (Proj method)')
metrics(te, pB1, 'B1 direct win')
metrics(te, pB2, 'B2 direct ranking (lambdarank)')
metrics(te, pP, 'P  direct place (top-3 capture only)')
metrics(te, (pB1 + pB2) / 2, 'B1+B2 average')
# reference: closing price on clean-book races with every price known
te = te.assign(pr=pd.to_numeric(te.priceStarting, errors='coerce'))
ok = te.groupby('race_id').pr.transform(lambda s: s.notna().all() and 1.05 <= (1 / s).sum() <= 2.0)
sub = te[ok]
mk = (1 / sub.pr) / (1 / sub.pr).groupby(sub.race_id).transform('sum')
print(f'\nCLEAN-BOOK SUBSET {sub.race_id.nunique():,} races (closing price for reference only, not a model input)')
for nm, p in (('market (closing price)', mk), ('A  rating route', pA[sub.index]), ('B1 direct win', pB1[sub.index]), ('B2 direct ranking', pB2[sub.index])):
    metrics(sub, p, nm)
