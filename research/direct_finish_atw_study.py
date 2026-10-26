"""Direct finishing-position model on ATW runner-page data (26 Oct 2026).
The runner-page store covers only ~26% of runners of past races (64% in early Oct 2026), so full-field comparisons are impossible. Clean design instead:
rows = results-file runs (2025-01 to 8 Oct 2026) whose own run is also in the page store with 3+ earlier page runs ('covered' runners). Every model is fitted,
tuned and scored on exactly the same covered runners and the same races (4+ covered runners, the winner among them), with win probabilities normalised among the
covered runners. Selection (a horse is covered if it raced again after mid Oct 2026) is identical for every model, so it cancels in the comparison.
  ATW models: ratings, margins and finishing percentiles of earlier runs ALL come from the page store (ratings as TopRate gives them, owner's ATW rule); target for the
  rating route = the page rating of the run itself.
  Plain models: the same features from the results files' full history (plain wpr).
Models: A rating route (Huber regression then softmax), B1 direct win (binary, normalised), B2 lambdarank. Train 2025-01 to 2026-03, early stop 2026-04..06, test 2026-07-01 to 10-08.
  PYTHONPATH=.. python direct_finish_atw_study.py   (from research/)
"""
import glob, os, sys
import lightgbm as lgb, numpy as np, pandas as pd
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__))); sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import closing_stage_study as CS
import last400_predictors_study as S
from projection import features as PF
ROOT = CS.ROOT
cols = ['race_id', 'horse_id', 'horse', 'date', 'distance', 'going', 'wpr', 'weightCarried', 'barrier', 'marginFinish', 'positionFinish', 'race_class', 'jockey', 'trainer',
        'horse_age', 'horse_sex', 'isBarrierTrial', 'is_jumpout', 'priceStarting']
r = pd.concat([pd.read_csv(f, usecols=lambda c: c in cols, low_memory=False) for f in sorted(glob.glob(os.path.join(ROOT, 'race_results_20[12]?.csv.gz')))], ignore_index=True)
r = r[~r.isBarrierTrial.astype(bool) & ~r.is_jumpout.fillna(False).astype(bool)]
r['date'] = pd.to_datetime(r.date)
r = r[r.date >= '2019-06-01'].drop_duplicates(['race_id', 'horse_id']).sort_values(['horse_id', 'date', 'race_id']).reset_index(drop=True)
r['hk'] = CS.clean(r.horse)
r['nr'] = r.groupby('race_id').horse_id.transform('size')
r['pos'] = pd.to_numeric(r.positionFinish, errors='coerce')
r['gs'] = pd.to_numeric(r.going.astype(str).str.extract(r'(\d+)')[0], errors='coerce')
r['barfrac'] = (r.barrier - 1) / (r.nr - 1)
r['cls'] = r.race_class.astype('category').cat.codes.astype(float)
r['sex'] = r.horse_sex.astype('category').cat.codes.astype(float)
r['win'] = (r.pos == 1).astype(float); r['top3'] = (r.pos <= 3).astype(float)


def lag_feats(df, key, pos_col='pos', nr_col='nr'):
    """df sorted by key,date: rating/margin/finish lags within the horse's own history."""
    g = df.groupby(key)
    fin = (df[pos_col] - 1) / (df[nr_col] - 1)
    mf = df.marginFinish.clip(0, 30)
    tmp = df.assign(_fin=fin, _mf=mf)
    g = tmp.groupby(key)
    F = {}
    lw = pd.concat([g.wpr.shift(k) for k in range(1, 9)], axis=1)
    for k in range(6):
        F[f'w{k + 1}'] = lw.iloc[:, k]
    F['m3_wpr'] = lw.iloc[:, :3].mean(axis=1); F['m8_wpr'] = lw.mean(axis=1); F['max8_wpr'] = lw.max(axis=1); F['s8_wpr'] = lw.std(axis=1)
    for c, nm in (('_mf', 'mfin'), ('_fin', 'finpct')):
        lg = pd.concat([g[c].shift(k) for k in range(1, 5)], axis=1)
        F['p1_' + nm] = lg.iloc[:, 0]; F['m4_' + nm] = lg.mean(axis=1)
    F['days'] = g.date.diff().dt.days
    F['wchg'] = tmp.weightCarried - g.weightCarried.shift(1)
    F['dchg'] = tmp.distance - g.distance.shift(1)
    F['n_prior'] = g.cumcount().astype(float)
    return pd.DataFrame(F, index=df.index)


FP = lag_feats(r, 'horse_id')                          # plain, from results history
rp = PF.runner_page_runs(); rp['date'] = pd.to_datetime(rp['date']); rp['hk'] = CS.clean(rp.horse)
rp = rp[(rp.isBarrierTrial == 0) & (~rp.is_jumpout.astype(bool))].drop_duplicates(['hk', 'date']).sort_values(['hk', 'date']).reset_index(drop=True)
rp['pos'] = pd.to_numeric(rp.positionFinish, errors='coerce'); rp['nr'] = pd.to_numeric(rp.field_size, errors='coerce')
FA = lag_feats(rp, 'hk')                               # ATW, from the page store
FA = FA.assign(hk=rp.hk.values, date=rp.date.values, page_wpr=rp.wpr.values)
base = r[['race_id', 'horse_id', 'hk', 'date', 'nr', 'pos', 'win', 'top3', 'wpr', 'weightCarried', 'barfrac', 'distance', 'gs', 'cls', 'horse_age', 'sex', 'jockey', 'trainer', 'priceStarting']].copy()
base['jw'], _ = S.asof_rate(base.assign(k=base.jockey.astype(str)), 'k', None, prior=0.1, k=50, value='win')
base['tw'], _ = S.asof_rate(base.assign(k=base.trainer.astype(str)), 'k', None, prior=0.1, k=50, value='win')
FPd = pd.concat([base, FP], axis=1)
FAd = base.merge(FA, on=['hk', 'date'], how='inner', suffixes=('', '_pg'))
# covered: run is in the page store with 3+ earlier page runs; same rows for plain
FAd = FAd[(FAd.n_prior >= 3) & (FAd.date >= '2025-01-01')]
FPd = FPd.loc[FPd.set_index(['race_id', 'horse_id']).index.isin(FAd.set_index(['race_id', 'horse_id']).index)]
FAd = FAd.sort_values(['race_id', 'horse_id']).reset_index(drop=True); FPd = FPd.sort_values(['race_id', 'horse_id']).reset_index(drop=True)
assert (FAd.race_id.values == FPd.race_id.values).all() and (FAd.horse_id.values == FPd.horse_id.values).all()
FAd['tgt'] = FAd.page_wpr; FPd['tgt'] = FPd.wpr          # rating-route target: the page (ATW) rating vs the results (plain) rating
print(f'covered runs {len(FAd):,}', flush=True)
fc = [f'w{k}' for k in range(1, 7)] + ['m3_wpr', 'm8_wpr', 'max8_wpr', 's8_wpr', 'p1_mfin', 'm4_mfin', 'p1_finpct', 'm4_finpct', 'days', 'wchg', 'dchg', 'n_prior',
      'weightCarried', 'barfrac', 'nr', 'distance', 'gs', 'cls', 'horse_age', 'sex', 'jw', 'tw']


def prep(d):
    d = d.copy()
    d['ncov'] = d.groupby('race_id').horse_id.transform('size'); d['nw'] = d.groupby('race_id').win.transform('sum')
    gk = d.groupby('race_id'); rel = {}
    for c in ['w1', 'm3_wpr', 'm8_wpr', 'max8_wpr', 'm4_mfin', 'm4_finpct', 'days', 'weightCarried', 'jw', 'tw', 'barfrac', 'horse_age']:
        rel['r_' + c] = d[c] - gk[c].transform('mean'); rel['k_' + c] = gk[c].rank(pct=True)
    rel['gap_top_m3'] = d.m3_wpr - gk.m3_wpr.transform('max'); rel['gap_top_m8'] = d.m8_wpr - gk.m8_wpr.transform('max')
    d = pd.concat([d, pd.DataFrame(rel, index=d.index)], axis=1)
    return d[(d.ncov >= 4) & (d.nw == 1)].reset_index(drop=True), fc + list(rel) + ['ncov']


A_d, feats = prep(FAd); P_d, _ = prep(FPd)
keep = set(zip(A_d.race_id, A_d.horse_id)) & set(zip(P_d.race_id, P_d.horse_id))
A_d = A_d[[k in keep for k in zip(A_d.race_id, A_d.horse_id)]].reset_index(drop=True); P_d = P_d[[k in keep for k in zip(P_d.race_id, P_d.horse_id)]].reset_index(drop=True)
split = lambda d: (d[d.date < '2026-04-01'], d[(d.date >= '2026-04-01') & (d.date < '2026-07-01')], d[d.date >= '2026-07-01'])
for nm, d in (('ATW', A_d),):
    a, b, c = split(d); print(f'races: fit {a.race_id.nunique():,} val {b.race_id.nunique():,} test {c.race_id.nunique():,}; avg covered runners per race {d.groupby("race_id").size().mean():.1f}', flush=True)
Pm = dict(learning_rate=0.04, num_leaves=15, min_child_samples=80, subsample=0.8, subsample_freq=1, colsample_bytree=0.5, reg_lambda=20, verbose=-1, n_estimators=1500)
ES = lambda: [lgb.early_stopping(60, verbose=False)]


def sm(df, s, T):
    z = df.assign(_s=s * T); e = np.exp(z._s - z.groupby('race_id')._s.transform('max'))
    return e / e.groupby(df.race_id).transform('sum')


def fitT(df, s):
    best = max(((np.log(sm(df, s, T)[df.win == 1].clip(1e-9)).mean(), T) for T in np.exp(np.linspace(np.log(0.01), np.log(5), 40))))
    return best[1]


def metr(df, p, name):
    df = df.assign(p=p.values if hasattr(p, 'values') else p)
    ll = np.log(df.loc[df.win == 1, 'p'].clip(1e-9)).mean(); rk = df.groupby('race_id').p.rank(ascending=False, method='first')
    top1 = df.loc[rk == 1, 'win'].mean(); w3 = df.loc[df.win == 1].assign(rk=rk).rk.le(3).mean()
    rnd = np.log(1 / df.groupby('race_id').size()).mean()
    print(f'{name:36s} winner LL {ll:8.4f}  top pick {top1:6.1%}  winner in top3 {w3:6.1%}', flush=True); return ll, rnd


def run(d, tag):
    tr, va, te = split(d)
    tr = tr; mA = lgb.LGBMRegressor(objective='huber', alpha=4.0, **Pm).fit(tr[feats], tr.tgt, eval_set=[(va[feats], va.tgt)], callbacks=ES())
    TA = fitT(va, mA.predict(va[feats])); pA = sm(te, mA.predict(te[feats]), TA)
    m1 = lgb.LGBMClassifier(**Pm).fit(tr[feats], tr.win, eval_set=[(va[feats], va.win)], callbacks=ES())
    T1 = fitT(va, np.log(m1.predict_proba(va[feats])[:, 1].clip(1e-9))); p1 = sm(te, np.log(m1.predict_proba(te[feats])[:, 1].clip(1e-9)), T1)
    lab = lambda df: np.where(df.pos <= 1, 4, np.where(df.pos <= 2, 3, np.where(df.pos <= 3, 2, np.where(df.pos <= 4, 1, 0))))
    rs = lambda df: lgb.Dataset(df[feats], label=lab(df), group=df.groupby('race_id', sort=False).size().values)
    Pr = dict(objective='lambdarank', learning_rate=0.04, num_leaves=15, min_data_in_leaf=80, feature_fraction=0.5, bagging_fraction=0.8, bagging_freq=1, lambda_l2=20, verbose=-1,
              lambdarank_truncation_level=5, eval_at=[1], metric='ndcg')
    m2 = lgb.train(Pr, rs(tr), num_boost_round=1500, valid_sets=[rs(va)], callbacks=ES())
    T2 = fitT(va, m2.predict(va[feats])); p2 = sm(te, m2.predict(te[feats]), T2)
    print(f'\n{tag}: trees A {mA.best_iteration_} B1 {m1.best_iteration_} B2 {m2.best_iteration}')
    out = {}
    out['A'] = metr(te, pA, f'{tag} A rating route'); out['B1'] = metr(te, p1, f'{tag} B1 direct win'); out['B2'] = metr(te, p2, f'{tag} B2 direct ranking')
    metr(te, (p1 + p2) / 2, f'{tag} B1+B2 average')
    return te, out


teA, oA = run(A_d, 'ATW page data')
teP, oP = run(P_d, 'plain results data')
print(f'\nrandom baseline (covered runners only) winner LL {oA["A"][1]:.4f}')
pr = pd.to_numeric(teA.priceStarting, errors='coerce'); ok = pr.notna().groupby(teA.race_id).transform('all')
if ok.any():
    sub = teA[ok]; mk = (1 / pr[ok]) / (1 / pr[ok]).groupby(sub.race_id).transform('sum')
    print(f'\ncovered-runner races with every price known: {sub.race_id.nunique():,} (reference only)')
    metr(sub, mk, 'closing price among covered runners')
