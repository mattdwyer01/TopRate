"""Can the independent part of Spd be built into Proj? (22 Oct 2026). Speed block (ctx.SPD_FEATS): the horse's earlier time-based speed figures (lengths vs par, the same figures Spd averages)
on their own, as an EWM, against the horse's ratings in the same runs (speed-implied minus rating), added to the relevance model's inputs for horses with 3+ earlier runs. Runner-page ATW
ratings are still the only RATING inputs and the target (owner rule); speed figures come from finish times and margins. Fit before 2026-01-01 (early stop 2025-10..12).
Part 1: held-out error predicting the rating (2026) and the partial-field winner test (store races). Part 2: the 322-race dashboard sample (formula coverage 80%+) out of sample: does
Proj with speed inside make Spd's separate slot in the blend redundant? Run: ROBUST_FRAME=<cache> PYTHONPATH=. python research/proj_speed_into_proj.py"""
import glob, gzip, json, os, sys, warnings
from datetime import date
warnings.filterwarnings('ignore')
import lightgbm as lgb, numpy as np, pandas as pd
from scipy.optimize import minimize
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'projection'))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import ctx as C
import speed_rating as sr

rp = pd.read_pickle(os.environ['ROBUST_FRAME'])
if 'horse' not in rp.columns:
    nm = []
    for f in sorted(glob.glob('data/tr_form/*.json.gz')):
        for r in json.load(gzip.open(f, 'rt')).get('runs', {}).values():
            nm.append((r['horse_id'], r['date'], r.get('horse')))
    nm = pd.DataFrame(nm, columns=['horse_id', 'date', 'horse']); nm['horse_id'] = pd.to_numeric(nm.horse_id, errors='coerce'); nm['date'] = pd.to_datetime(nm.date)
    rp = rp.merge(nm.drop_duplicates(['horse_id', 'date'], keep='last'), on=['horse_id', 'date'], how='left')
rp = C.add_speed(rp)
print(f"speed figure found for {100*rp.sp.notna().mean():.1f}% of page runs", flush=True)
rp = pd.concat([rp, C.speed_features(rp, rp)], axis=1)
pg = rp[rp.f.notna() & (rp.n >= C.REL_MIN_RUNS)].copy(); classes = sorted(rp.cls.dropna().unique().tolist()); pg['cls_c'] = C._cls(pg.cls, classes)
cut, es = pd.Timestamp('2026-01-01'), pd.Timestamp('2025-10-01')
F1 = C.FEATS + C.REL_FEATS; F2 = F1 + C.SPD_FEATS
tr, va, te = pg[pg.date < es], pg[(pg.date >= es) & (pg.date < cut)], pg[pg.date >= cut].copy()
P = dict(learning_rate=0.03, num_leaves=31, min_child_samples=100, subsample=0.8, subsample_freq=1, colsample_bytree=0.8, reg_lambda=5, verbose=-1, n_jobs=4)
fit = lambda feats: lgb.LGBMRegressor(n_estimators=4000, **P).fit(tr[feats], tr.resid, eval_set=[(va[feats], va.resid)], callbacks=[lgb.early_stopping(100, verbose=False)])
m1, m2 = fit(F1), fit(F2)
te['mu_rel'] = te.f + m1.predict(te[F1]); te['mu_spd'] = te.f + m2.predict(te[F2])
for c in ('rel', 'spd'): te['e_' + c] = te.wpr - te['mu_' + c]
r = lambda x: float(np.sqrt((x ** 2).mean()))
print(f"\nPart 1. held-out 2026, {len(te):,} runs with 3+ earlier runs (trees: relevance {m1.best_iteration_}, + speed {m2.best_iteration_})")
d_ = te.e_rel ** 2 - te.e_spd ** 2
print(f"  RMSE relevance {r(te.e_rel):.4f}, relevance + speed block {r(te.e_spd):.4f} ({100*(1-r(te.e_spd)/r(te.e_rel)):.2f}% lower); paired gain {d_.mean():+.3f} pts^2/run (se {d_.std()/np.sqrt(len(d_)):.3f})")
te['hasspd'] = te.n_sp.fillna(0) >= 1
for lab, s in (('speed figures on file', te.hasspd), ('no speed figure history', ~te.hasspd)):
    print(f"   {lab:26s} n={int(s.sum()):6d}  relevance {r(te.e_rel[s]):.3f}  + speed {r(te.e_spd[s]):.3f}")
imp = pd.Series(m2.booster_.feature_importance('gain'), index=F2); imp = imp / imp.sum()
print('  gain share of the speed block:', round(float(imp[C.SPD_FEATS].sum()), 3), '| top speed inputs:', {k: round(float(v), 3) for k, v in imp[C.SPD_FEATS].sort_values(ascending=False).head(5).items()})
te['race'] = te.date.astype(str) + '|' + te.track.astype(str) + '|' + te.distance.astype(str) + '|' + te.field_size.astype(str) + '|' + te.race_class.astype(str)
te['won'] = (te.positionFinish == 1).astype(int); te['nr'] = te.groupby('race').won.transform('size'); te['nw'] = te.groupby('race').won.transform('sum')
d = te[(te.nr >= 3) & (te.nw == 1)].copy(); d['rid'] = d.race.astype('category').cat.codes
def ll1(df, col, b):
    s = b * df[col].values; mx = pd.Series(s).groupby(df.rid.values).transform('max').values; e = np.exp(s - mx)
    return (s - (np.log(pd.Series(e).groupby(df.rid.values).transform('sum').values) + mx))[df.won.values == 1]
fb = lambda df, c: minimize(lambda b: -ll1(df, c, b[0]).mean(), [0.15], method='L-BFGS-B').x[0]
dates = sorted(d.date.unique()); half = dates[len(dates) // 2]; A, B = d[d.date < half], d[d.date >= half]
o = {c: np.concatenate([ll1(B, 'mu_' + c, fb(A, 'mu_' + c)), ll1(A, 'mu_' + c, fb(B, 'mu_' + c))]) for c in ('rel', 'spd')}
dd = o['spd'] - o['rel']; print(f"  winner test on {d.rid.nunique():,} store races: relevance {o['rel'].mean():.4f}, + speed {o['spd'].mean():.4f}, gain {dd.mean():+.4f} (se {dd.std()/np.sqrt(len(dd)):.4f})", flush=True)

print("\nPart 2. dashboard races, out of sample")
pg0 = rp[rp.f.notna()].copy(); pg0['cls_c'] = C._cls(pg0.cls, classes)
tr0, va0 = pg0[pg0.date < es], pg0[(pg0.date >= es) & (pg0.date < cut)]
mp = lgb.LGBMRegressor(n_estimators=4000, **P).fit(tr0[C.FEATS], tr0.resid, eval_set=[(va0[C.FEATS], va0.resid)], callbacks=[lgb.early_stopping(100, verbose=False)])
meta1, meta2 = dict(classes=classes, rel_feats=F1), dict(classes=classes, rel_feats=F2)
KEY = ['date', 'venue', 'race', 'horse']
cols = KEY + ['horse_id', 'wpr_nett', 'scratched', 'won', 'field_source', 'spd_fig', 'weight_carried', 'barrier', 'jockey', 'distance', 'going', 'race_class', 'track_grading']
rd = lambda p: pd.read_csv(p, low_memory=False, usecols=lambda c: c in cols)
leg = pd.concat([rd('archive/toprate/toprate_runners_archive.csv.gz'), rd('archive/toprate/toprate_runners.csv')], ignore_index=True)
cur = pd.concat([rd('runners_archive.csv.gz'), rd('runners.csv')], ignore_index=True)
for x in (leg, cur):
    x['date'] = x['date'].astype(str).str[:10]; x['race'] = x['race'].astype(str)
dd_ = leg.drop_duplicates(KEY, keep='last').set_index(KEY).combine_first(cur.drop_duplicates(KEY, keep='last').set_index(KEY)).reset_index()
dd_ = dd_[(dd_.date >= '2026-04-26') & (dd_.date <= '2026-10-17')]
dd_ = dd_[(dd_.scratched.fillna(0) != 1) & ~dd_.field_source.astype(str).str.contains('not in toprate', na=False)].reset_index(drop=True)
dd_['spd_fig'] = sr.compute(dd_, today=date(2026, 8, 1)).where(lambda s: s.notna(), pd.to_numeric(dd_.spd_fig, errors='coerce'))
dd_['rk'] = dd_.venue.astype(str) + '|' + dd_.date + '|' + dd_.race
g = dd_.groupby('rk'); okr = (g.won.transform('sum') == 1) & g.won.transform(lambda s: s.notna().all()) & (g.won.transform('size') >= 5)
dd_ = dd_[okr].copy(); dd_['won'] = dd_.won.astype(int)
T = pd.DataFrame(dict(horse_id=pd.to_numeric(dd_.horse_id, errors='coerce').values, date=pd.to_datetime(dd_.date).values, jockey=dd_.jockey.values, venue=dd_.venue.values, distance=dd_.distance.values,
                      going=dd_.going.values, weightCarried=dd_.weight_carried.values, barrier=dd_.barrier.values, field_size=g.won.transform('size')[dd_.index].values, race_class=dd_.race_class.values, trackGrading=dd_.track_grading.values))
k = T.horse_id.notna().values; T = T[k].reset_index(drop=True); dd_ = dd_[k].reset_index(drop=True)
f2, c1 = C.predict(T, meta=meta1, booster=mp.booster_, rp=rp, rel_booster=m1.booster_)
_, c2 = C.predict(T, meta=meta2, booster=mp.booster_, rp=rp, rel_booster=m2.booster_)
dd_['p_rel'], dd_['p_spd'] = f2 + c1, f2 + c2
dd_['nett'] = pd.to_numeric(dd_.wpr_nett, errors='coerce'); dd_['spd'] = pd.to_numeric(dd_.spd_fig, errors='coerce')
cov = dd_.groupby('rk').p_rel.transform(lambda s: s.notna().mean()); D = dd_[cov >= 0.8].copy(); D['rid'] = D.rk.astype('category').cat.codes
for c in ('p_rel', 'p_spd', 'nett', 'spd'):
    gm = D.groupby('rid')[c]; D['z_' + c] = ((D[c] - gm.transform('mean')) / gm.transform('std').replace(0, np.nan)).fillna(0.0)
def ll(df, X, w):
    s = X @ w; mx = pd.Series(s).groupby(df.rid.values).transform('max').values; e = np.exp(s - mx)
    return (s - (np.log(pd.Series(e).groupby(df.rid.values).transform('sum').values) + mx))[df.won.values == 1]
def fitw(df, cs):
    X = df[['z_' + c for c in cs]].values; return minimize(lambda w: -ll(df, X, w).mean(), np.full(len(cs), .2), method='L-BFGS-B').x
dts = sorted(D.date.unique()); hf = dts[len(dts) // 2]; A2, B2 = D[D.date < hf], D[D.date >= hf]
def run(cs):
    out, tops = [], []
    for a, b in ((A2, B2), (B2, A2)):
        w = fitw(a, cs); X = b[['z_' + c for c in cs]].values; out.append(ll(b, X, w)); t = b.assign(s=X @ w); tops.append(t.loc[t.groupby('rid').s.idxmax()].won.values)
    return np.concatenate(out), np.concatenate(tops)
rows = {'Proj (relevance) alone': run(['p_rel']), 'Proj + speed block alone': run(['p_spd']), 'Proj + Nett': run(['p_rel', 'nett']), 'Proj + Nett + Spd (the blend)': run(['p_rel', 'nett', 'spd']),
        'Proj+speed + Nett': run(['p_spd', 'nett']), 'Proj+speed + Nett + Spd': run(['p_spd', 'nett', 'spd'])}
base = rows['Proj + Nett + Spd (the blend)'][0]
print(f"  {D.rid.nunique()} races ({len(D)} runners)\n  {'score':32s} {'winner LL':>9s} {'top pick':>9s} {'vs the blend':>20s}")
for kk, (l, t) in rows.items():
    x = l - base; print(f"  {kk:32s} {l.mean():9.4f} {100*t.mean():8.1f}% {x.mean():+10.4f} (se {x.std()/np.sqrt(len(x)):.4f})")
for cs in (['p_rel', 'nett', 'spd'], ['p_spd', 'nett', 'spd']):
    w = fitw(D, cs); print('  full-sample fitted shares', cs, np.round(w / w.sum(), 2))
