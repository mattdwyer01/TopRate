"""Spd the way Proj is built (22 Oct 2026). Today's Spd = EWM (half-life 4 runs) of a horse's time-based speed figures (lengths vs par), shrunk for few runs, plus days-since-run and
weight-change terms. Proj = a formula (weights by earlier-run count, fitted) + a LightGBM correction from context + the relevance features (each earlier run judged against
today's race). This script builds the same three layers on the speed figures: formula, formula + context, formula + context + relevance, and scores them against today's Spd.
Target = the run's own figure. Speed figures come from the results files (2019 on) and the runner-page store for later days; par and same-day variant as in speed_rating.py.
Fit: runs 2023-07 to 2025-06, early stop 2025-07..12, test 2026 (results files to 8 Oct). Two scores: error predicting the figure (RMSE, within-race RMSE) and the winner test
over complete races (conditional logit of the winner on the within-race z-score, cross-fitted on date halves, top pick and winner log-lik).
Run: PYTHONPATH=. python research/spd_formula_ctx.py"""
import json, os, sys, warnings
warnings.filterwarnings('ignore')
import lightgbm as lgb, numpy as np, pandas as pd
from scipy.optimize import minimize
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'projection'))
import speed_rating as sr
import ctx as C

K = C.K
sr.USE = sr.USE + ['jockey', 'barrier']
d = sr.figures(sr.load_results(2019))
rp = pd.DataFrame(dict(key=d.horse.astype(str).str.lower().str.strip().values, date=pd.to_datetime(d.date).values, wpr=d.sp.values, track=d.track.values, distance=pd.to_numeric(d.distance, errors='coerce').values,
                       going=d.going.values, weightCarried=pd.to_numeric(d.weightCarried, errors='coerce').values, barrier=pd.to_numeric(d.barrier, errors='coerce').values,
                       field_size=pd.to_numeric(d.field_size, errors='coerce').values, race_class=d.race_class.values, trackGrading=d.trackGrading.values, jockey=d.jockey.values,
                       positionFinish=pd.to_numeric(d.positionFinish, errors='coerce').values, marginFinish=pd.to_numeric(d.marginFinish, errors='coerce').values, race_id=d.race_id.values))
rp = rp.dropna(subset=['key', 'date', 'wpr']).sort_values(['key', 'date']).drop_duplicates(['key', 'date'], keep='last').reset_index(drop=True)
rp['horse_id'] = pd.factorize(rp.key)[0].astype(float)
rp['going_n'] = C.going_num(rp.going)
rp['grade'] = pd.to_numeric(rp.trackGrading, errors='coerce')
rp['cls'] = C.class_code(rp.race_class)
rp['vn'] = C.venue_key(rp.track)
rp['jockey'] = rp.jockey.astype(object).where(rp.jockey.notna(), None)
g = rp.groupby('horse_id')
for k in range(1, K + 1):
    rp[f'r{k}'] = g.wpr.shift(k)
rp['n'] = g.cumcount().astype(float)
rp['d_last'] = (rp.date - g.date.shift(1)).dt.days.astype(float)
rp['l_dist'], rp['l_going'], rp['l_wt'], rp['l_mgn'] = g.distance.shift(1), g.going_n.shift(1), g.weightCarried.shift(1), g.marginFinish.shift(1)
rp['l_posf'] = (rp.positionFinish / rp.field_size).groupby(rp.horse_id).shift(1)
print(f"{len(rp):,} speed figures, {rp.horse_id.nunique():,} horses, {rp.date.min().date()} to {rp.date.max().date()}")

TR_FROM, ES_FROM, CUT = pd.Timestamp('2023-07-01'), pd.Timestamp('2025-07-01'), pd.Timestamp('2026-01-01')
# formula: weights by earlier-run count, fitted on runs before ES_FROM (as projection/fit_formula.py)
trn = rp[rp.date < ES_FROM]
co = {}
for nn in range(1, K + 1):
    a = trn[trn.n.clip(upper=K) == nn]; c = [f'r{k}' for k in range(1, nn + 1)]; a = a.dropna(subset=c)
    co[nn] = np.linalg.lstsq(np.c_[np.ones(len(a)), a[c].values], a.wpr.values, rcond=None)[0]
print('formula weights, 8+ runs:', np.round(co[K], 3))
rp['f'] = C.formula_pred(rp, co)
rp = C.context_columns(rp)
rp['resid'] = rp.wpr - rp.f
rp = C.add_jockey(rp, C.jockey_table(rp))
classes = sorted(rp.cls.dropna().unique().tolist()); rp['cls_c'] = C._cls(rp.cls, classes)

# today's Spd as computed now, as of before each run (EWM hl 4 of earlier figures, shrink, days and weight terms)
ew = rp.groupby('horse_id').wpr.transform(lambda s: s.shift(1).ewm(halflife=sr.HALFLIFE, min_periods=1).mean())
nfig = rp.n
mu = float(ew[nfig >= 6].mean())
kshr = np.select([nfig == 1, nfig == 2, nfig.between(3, 5)], [sr.SHRINK[1], sr.SHRINK[2], sr.SHRINK[3]], default=1.0)
adj = json.loads(sr.ADJUST.read_text()); aa = adj['adj_lengths']
days = rp.d_last.clip(lower=0, upper=400)
spd_now = (mu + kshr * (ew - mu)) + aa['ldays'] * (np.log1p(days) - adj['ldays_center']) + (aa['wchg'] * (rp.weightCarried - rp.l_wt).clip(-adj['wchg_clip'], adj['wchg_clip'])).fillna(0.0)
rp['spd_now'] = np.where(rp.n >= 1, spd_now, np.nan)

fit_rows = (rp.date >= TR_FROM) & (rp.date < CUT) & rp.f.notna()
need = rp[fit_rows | ((rp.date >= CUT) & rp.f.notna())]
print(f"computing relevance features for {len(need):,} rows (about {len(need) * 1.6 / 60000:.0f} min)...")
rel = C.rel_features(need, rp)
need = pd.concat([need, rel], axis=1)
F0, F1 = C.FEATS, C.FEATS + C.REL_FEATS
tr = need[(need.date >= TR_FROM) & (need.date < ES_FROM)]; va = need[(need.date >= ES_FROM) & (need.date < CUT)]; te = need[need.date >= CUT].copy()
P = dict(learning_rate=0.03, num_leaves=63, min_child_samples=200, subsample=0.8, subsample_freq=1, colsample_bytree=0.8, reg_lambda=5, verbose=-1, n_jobs=4)
def fitm(feats):
    m = lgb.LGBMRegressor(n_estimators=4000, **P).fit(tr[feats], tr.resid, eval_set=[(va[feats], va.resid)], callbacks=[lgb.early_stopping(100, verbose=False)])
    return m
m0, m1 = fitm(F0), fitm(F1)
print('trees: context', m0.best_iteration_, 'relevance', m1.best_iteration_, '| train', len(tr), 'valid', len(va), 'test', len(te))
te['p_formula'] = te.f; te['p_ctx'] = te.f + m0.predict(te[F0]); te['p_rel'] = te.f + m1.predict(te[F1])
# today's Spd mapped onto the figure scale by a line fitted on the same training rows
okk = tr.spd_now.notna()
ab = np.polyfit(tr.spd_now[okk], tr.wpr[okk], 1); te['p_now'] = np.polyval(ab, te.spd_now)
r = lambda x: float(np.sqrt(np.nanmean(x ** 2)))
te['race'] = te.race_id
big = te.groupby('race').wpr.transform('size') >= 5
def within(e):
    t = te.assign(_e=e); return r((t._e - t.groupby('race')._e.transform('mean'))[big])
print(f"\n{'score':22s} {'RMSE':>7s} {'within-race':>12s}   (target = the run's own figure, lengths vs par; sd of the figure {te.wpr.std():.2f})")
for lab, c in (('today Spd (line fit)', 'p_now'), ('formula', 'p_formula'), ('formula + context', 'p_ctx'), ('formula + ctx + relevance', 'p_rel')):
    e = te.wpr - te[c]; print(f"{lab:22s} {r(e):7.3f} {within(e):12.3f}")
for lab, s in (('1-2 earlier runs', te.n <= 2), ('3-5', (te.n >= 3) & (te.n <= 5)), ('6-8', (te.n >= 6) & (te.n <= 8)), ('9+', te.n >= 9)):
    print(f"   {lab:18s} n={int(s.sum()):6d} " + '  '.join(f"{nm} {r((te.wpr - te[c])[s]):.3f}" for nm, c in (('now', 'p_now'), ('formula', 'p_formula'), ('ctx', 'p_ctx'), ('rel', 'p_rel'))))

# winner test: complete races (every runner has every score), one winner, 5+ runners
te['won'] = (te.positionFinish == 1).astype(int)
cols = ['p_now', 'p_formula', 'p_ctx', 'p_rel']
ok = te[cols].notna().all(axis=1)
te['okr'] = ok.groupby(te.race).transform('all'); w = te.groupby('race').won.transform('sum'); sz = te.groupby('race').won.transform('size')
D = te[te.okr & (w == 1) & (sz >= 5)].copy(); D['rid'] = D.race.astype('category').cat.codes
for c in cols: D['z_' + c] = (D[c] - D.groupby('rid')[c].transform('mean')) / D.groupby('rid')[c].transform('std').replace(0, np.nan)
D = D.dropna(subset=['z_' + c for c in cols])
print(f"\nwinner test: {D.rid.nunique():,} complete 2026 races, {len(D):,} runners")
def ll(df, col, b):
    s = b * df[col].values; mx = pd.Series(s).groupby(df.rid.values).transform('max').values; e = np.exp(s - mx)
    return (s - (np.log(pd.Series(e).groupby(df.rid.values).transform('sum').values) + mx))[df.won.values == 1]
fit = lambda df, col: minimize(lambda b: -ll(df, col, b[0]).mean(), [0.3], method='L-BFGS-B').x[0]
dates = sorted(D.date.unique()); half = dates[len(dates) // 2]; A, B = D[D.date < half], D[D.date >= half]
res = {}
for c in cols:
    l = np.concatenate([ll(B, 'z_' + c, fit(A, 'z_' + c)), ll(A, 'z_' + c, fit(B, 'z_' + c))])
    top = D.loc[D.groupby('rid')['z_' + c].idxmax()].won.mean()
    res[c] = (l, top)
base = res['p_now'][0]
for lab, c in (('today Spd', 'p_now'), ('formula', 'p_formula'), ('formula + context', 'p_ctx'), ('formula + ctx + relevance', 'p_rel')):
    l, top = res[c]; dd = l - base
    print(f"{lab:26s} winner LL {l.mean():8.4f}  top pick {100*top:5.1f}%   gain vs today {dd.mean():+.4f} (se {dd.std()/np.sqrt(len(dd)):.4f})")
te.to_pickle(os.environ.get('SPD_OUT', 'spd_te.pkl'))
