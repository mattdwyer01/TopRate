"""First-starter rating test (10 Nov 2026). Live rule (projection/run.py, formula.json 'debut'): race level (mean Proj of the race's 3+-run runners) + a + b x (ln price - field
mean ln price). Question: do non-price facts (trials and jump-outs, sire / dam-sire / dam offspring level, the trainer's and jockey's record with first starters, age, sex,
race type) improve it, with or without the price? Complete fields from the results files on the page ATW scale (research/conv_history.py per row), a debut = the horse's first
run in the results files (2016 on). Level stand-in = mean formula figure of the race's runners with 3+ earlier runs (needs 3). Fit before 2025-10, early stop 2025-10..12,
test 2026 (to --conv-to). Also a winner test on the 2026 races that hold a first starter (others rated by their formula figure, the same for every variant).
Run: PYTHONPATH=.:projection:research PROJECTION_RATINGS=toprate python research/debut_model_test.py"""
import glob, json, sys, time
import numpy as np, pandas as pd, lightgbm as lgb
sys.path.insert(0, 'projection'); sys.path.insert(0, 'research')
import ctx as C, conv_history as CH, features as FT, rates as RT

T0 = time.time(); log = lambda *x: print(f'[{(time.time() - T0) / 60:5.1f}m]', *x, flush=True)
CONV_TO = sys.argv[1] if len(sys.argv) > 1 else '2026-10-08'
FRAC = float(sys.argv[2]) if len(sys.argv) > 2 else 1.0
CUT, ES = pd.Timestamp('2026-01-01'), pd.Timestamp('2025-10-01')
FT.runner_page_runs()
conv = CH.build(2020, CONV_TO, FRAC)
sp = conv[['horse_id', 'date', 'priceStarting']].copy()
FT._TR_CACHE['rows'] = conv
D = C.training_frame(True)
D = D.merge(sp, on=['horse_id', 'date'], how='left', suffixes=('', '_sp')) if 'priceStarting' not in D.columns else D
log('frame', len(D))
# true debuts: first non-trial run of the horse in any results file
parts = []
for f in sorted(glob.glob('race_results_20[12]*.csv.gz')):
    if '_rc' in f:
        continue
    parts.append(pd.read_csv(f, usecols=lambda c: c in ('horse_id', 'date', 'isBarrierTrial', 'is_jumpout', 'horse_age', 'horse_sex', 'sire_id', 'dam_id', 'sire_of_dam'), low_memory=False))
S = pd.concat(parts, ignore_index=True)
S['horse_id'] = pd.to_numeric(S.horse_id, errors='coerce'); S = S.dropna(subset=['horse_id']); S['date'] = pd.to_datetime(S.date)
R = S[(S.isBarrierTrial.astype(str) != 'True') & (S.is_jumpout.astype(str) != 'True')]
first = R.groupby('horse_id').date.min()
season = lambda d: d.dt.year - (d.dt.month < 8).astype(int)
S['foal'] = season(S.date) - pd.to_numeric(S.horse_age, errors='coerce')
S['sex'] = S.horse_sex.astype(str).str.upper().str[:1].map({'G': 0, 'R': 0, 'M': 1, 'F': 1, 'C': 2, 'H': 2})
H = S.sort_values('date').groupby('horse_id').agg(foal=('foal', 'median'), sex=('sex', 'last'), sire=('sire_id', 'last'), dam=('dam_id', 'last'), dsire=('sire_of_dam', 'last'))
H['dsire'] = H.dsire.astype(str).str.upper().str.strip().where(H.dsire.notna()); H['dsire'] = H.dsire.astype('category').cat.codes.astype(float).where(H.dsire.notna())
h = H.reindex(D.horse_id.values)
D['age'] = (season(D.date) - h.foal.values).astype(float); D['age'] = D.age.where(D.age.between(1, 15))
D['sex_c'], D['sire'], D['dam'], D['dsire'] = h.sex.values, h.sire.values, h.dam.values, h.dsire.values
D['debut'] = (D.date.values == first.reindex(D.horse_id.values).values) & (D.n == 0)
D['rk'] = C._race_key(D)
D['month'] = D.date.dt.month.astype(float)
D['dband'] = pd.cut(D.distance, [0, 1200, 1600, 2000, 9999], labels=False).astype(float)
D['wet'] = (D.going_n >= 5).astype(float)
exp = D.n >= 3
g = D.f.where(exp).groupby(D.rk)
D['level'], D['n_exp'], D['lvl_sd'] = g.transform('mean'), g.transform('count'), g.transform('std')
D['n_deb'] = D.debut.astype(float).groupby(D.rk).transform('sum')
D['deb_share'] = D.n_deb / D.groupby('rk').horse_id.transform('size')
D['lsp'] = np.log(pd.to_numeric(D.priceStarting, errors='coerce').where(lambda s: s > 1))
D['relp'] = D.lsp - D.lsp.groupby(D.rk).transform('mean')
MU = float(D.wpr.mean()); D['wdev'] = D.wpr - MU
D['jkc'] = pd.factorize(D.jockey.map(RT.nk))[0].astype(float); D.loc[D.jkc < 0, 'jkc'] = np.nan
D['trn'] = pd.factorize(D.trainer.astype(str))[0].astype(float); D.loc[D.trainer.isna(), 'trn'] = np.nan
SRC = D[D.wpr.notna()]


def asof(keys, tgt, val, mask=None, K=20):
    s = SRC if mask is None else SRC[mask]
    s = s.dropna(subset=keys + [val])
    gg = s.groupby(keys + ['date'])[val].agg(['sum', 'count']).reset_index().sort_values('date')
    gg['S'] = gg.groupby(keys)['sum'].cumsum(); gg['C'] = gg.groupby(keys)['count'].cumsum()
    t = tgt[keys + ['date']].copy(); t['_i'] = np.arange(len(t)); t = t.dropna(subset=keys)
    for k in keys:
        t[k] = t[k].astype(float); gg[k] = gg[k].astype(float)
    m = pd.merge_asof(t.sort_values('date'), gg[keys + ['date', 'S', 'C']], on='date', by=keys, allow_exact_matches=False)
    Sv, Cv = np.zeros(len(tgt)), np.zeros(len(tgt))
    Sv[m._i.values] = m.S.fillna(0).values; Cv[m._i.values] = m.C.fillna(0).values
    return Sv / (Cv + K), Cv


B = D[D.debut & D.wpr.notna() & (D.n_exp >= 3) & (D.date >= '2021-01-01')].copy()
log('debut runs with a level', len(B), 'price known', round(float(B.relp.notna().mean()), 3))
deb = SRC.debut
B['sire_lvl'], B['sire_n'] = asof(['sire'], B, 'wdev', K=30)
B['sire_deb_lvl'], B['sire_deb_n'] = asof(['sire'], B, 'wdev', deb, K=20)
B['sire_db_lvl'], _ = asof(['sire', 'dband'], B, 'wdev', K=30)
B['dsire_lvl'], _ = asof(['dsire'], B, 'wdev', K=30)
B['dam_lvl'], B['dam_n'] = asof(['dam'], B, 'wdev', K=5)
B['trn_deb_lvl'], B['trn_deb_n'] = asof(['trn'], B, 'wdev', deb, K=15)
B['trn_lvl'], _ = asof(['trn'], B, 'wdev', K=50)
B['jk_deb_lvl'], B['jk_deb_n'] = asof(['jkc'], B, 'wdev', deb, K=15)
B['jk_lvl'], _ = asof(['jkc'], B, 'wdev', K=50)
for k, cols in (('sire', ['sire_lvl', 'sire_deb_lvl', 'sire_db_lvl']), ('dsire', ['dsire_lvl']), ('dam', ['dam_lvl']), ('trn', ['trn_deb_lvl', 'trn_lvl']), ('jkc', ['jk_deb_lvl', 'jk_lvl'])):
    B.loc[B[k].isna(), cols] = np.nan
classes = sorted(B.cls.dropna().unique().tolist()); B['cls_c'] = pd.Categorical(B.cls, categories=classes)
B['y'] = B.wpr - B.level
RACE = ['level', 'lvl_sd', 'n_exp', 'deb_share', 'field_size', 'distance', 'going_n', 'grade', 'barr_f', 'weightCarried', 'cls_c', 'month', 'age', 'sex_c']
CONN = ['jw', 'jw90', 'tw', 'tw90', 'trn_deb_lvl', 'trn_deb_n', 'trn_lvl', 'jk_deb_lvl', 'jk_deb_n', 'jk_lvl']
PED = ['sire_lvl', 'sire_n', 'sire_deb_lvl', 'sire_deb_n', 'sire_db_lvl', 'dsire_lvl', 'dam_lvl', 'dam_n']
SETS = {'race': RACE, 'race+trials': RACE + C.TRIAL_FEATS, 'race+conn': RACE + CONN, 'race+ped': RACE + PED, 'all no price': RACE + C.TRIAL_FEATS + CONN + PED}
SETS['all + price'] = SETS['all no price'] + ['relp', 'lsp']
SETS['race + price'] = RACE + ['relp', 'lsp']
tr, va, te = B[B.date < ES], B[(B.date >= ES) & (B.date < CUT)], B[B.date >= CUT].copy()
log('train', len(tr), 'valid', len(va), 'test', len(te), 'test with price', int(te.relp.notna().sum()))
res = {}
rm = lambda e: float(np.sqrt(np.nanmean(e ** 2)))
t2 = pd.concat([tr, va]); ok = t2.relp.notna()
b, a0 = np.polyfit(t2.relp[ok], t2.y[ok], 1)
te['p_live'] = a0 + b * te.relp
te['p_const'] = t2.y.mean()
print(f'live form refit: a {a0:+.2f} b {b:+.2f}')
LIVE = json.load(open('projection/models_tr/formula.json'))['debut']
te['p_livecoef'] = LIVE['a'] + LIVE['b'] * te.relp        # the coefficients in use (others in the race sit on their formula figure here, on Proj live: about 1 point higher)
for a_try in (-1, -2, -3, -4, -5, -6, -7, -8):
    te[f'p_a{a_try}'] = a_try + b * te.relp
for b_try in (-4, -5, -7, -8):
    te[f'p_b{b_try}'] = a0 + b_try * te.relp
import statsmodels.api as sm
qm = sm.QuantReg(t2.y[ok], sm.add_constant(t2.relp[ok])).fit(q=0.5)
print('median regression: a', round(float(qm.params.iloc[0]), 2), 'b', round(float(qm.params.iloc[1]), 2), '| experienced runners: median of rating minus formula', round(float((D.wpr - D.f)[exp & (D.date < CUT)].median()), 2), 'mean', round(float((D.wpr - D.f)[exp & (D.date < CUT)].mean()), 2))
te['p_median'] = float(qm.params.iloc[0]) + float(qm.params.iloc[1]) * te.relp
for obj in ('huber', 'l2'):
    for nm, Fs in SETS.items():
        if nm not in ('all no price', 'all + price'):
            continue
        P = dict(n_estimators=4000, learning_rate=0.03, num_leaves=15, min_child_samples=60, subsample=0.8, subsample_freq=1, colsample_bytree=0.8, reg_lambda=5, verbose=-1)
        P.update(dict(objective='huber', alpha=6.0) if obj == 'huber' else dict(objective='regression'))
        m = lgb.LGBMRegressor(**P).fit(tr[Fs], tr.y, eval_set=[(va[Fs], va.y)], callbacks=[lgb.early_stopping(150, verbose=False)])
        te[f'p_{obj}_{nm}'] = m.predict(te[Fs])
        imp = pd.Series(m.booster_.feature_importance('gain'), index=Fs); imp = (imp / imp.sum()).sort_values(ascending=False).head(8).round(3).to_dict()
        print(obj, nm, 'trees', m.best_iteration_, 'top', imp, flush=True)
pc = [c for c in te.columns if c.startswith('p_')]
pr = te.relp.notna()
print('\nfirst starters, 2026 (rating minus race level; RMSE / MAE / median abs / bias), all and those with a price')
for c in pc:
    e, e2 = (te.y - te[c]), (te.y - te[c])[pr]
    res[c] = dict(n=int(e.notna().sum()), rmse=round(rm(e), 3), mae=round(float(e.abs().mean()), 3), med=round(float(e.abs().median()), 3), bias=round(float(e.mean()), 2),
                  rmse_priced=round(rm(e2), 3), mae_priced=round(float(e2.abs().mean()), 3))
    print(f'{c:28s}', res[c], flush=True)
# winner test: 2026 races with a first starter; everyone else on the formula figure
W = D[(D.date >= CUT) & D.rk.isin(te.rk)].copy()
for c in pc:
    W[c] = W.f
    W.loc[te.index.intersection(W.index), c] = (te.level + te[c]).reindex(te.index.intersection(W.index))
W = W[W.positionFinish.notna()]
W = W[W.groupby('rk').positionFinish.transform(lambda s: (s == 1).sum()) == 1]
print('\nwinner test: races', W.rk.nunique())
half = (W.date >= W.date.median()).astype(int)
base = None
for c in pc:
    X = W[W[c].notna().groupby(W.rk).transform('all')]
    def ll(df, bt):
        z = bt * (df[c] - df.groupby('rk')[c].transform('max')); return (z - np.log(np.exp(z).groupby(df.rk).transform('sum')))[df.positionFinish == 1]
    out = []
    for hh in (0, 1):
        bs = np.arange(0.04, 0.4, 0.01); bb = bs[np.argmax([ll(X[half.reindex(X.index) != hh], x).mean() for x in bs])]; out.append(ll(X[half.reindex(X.index) == hh], bb))
    s = pd.concat(out); s.index = X.loc[s.index, 'rk']
    dw = X[X.debut]; won = float((dw.positionFinish == 1).mean())
    if c == 'p_live':
        base = s
    res[c].update(win_ll=round(float(s.mean()), 4), races=int(len(s)))
    if base is not None:
        dd = (s - base.reindex(s.index)).dropna(); res[c].update(win_ll_gain=round(float(dd.mean()), 4), se=round(float(dd.std() / np.sqrt(len(dd))), 4))
    print(f'{c:28s}', {k: res[c].get(k) for k in ('races', 'win_ll', 'win_ll_gain', 'se')}, flush=True)
json.dump(res, open('research/debut_model_test.json', 'w'), indent=1)
log('done')
