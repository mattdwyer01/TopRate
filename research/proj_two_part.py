"""Two-part Proj test (22 Oct 2026): a 'runs to form' rating (conditional median) plus the chance of a bad run (more than 12 below the formula), against today's Proj
(the mean). Runner-page ATW ratings only. Models are fit on runs before 2026-01-01 and scored on 2026 runs. Winner test inside each race as the runner-page store holds it
(a race = date, track, distance, field size, class; about 4 runners per race, the store holds only some of a field, so the test is the winner among the store's runners
in races where the store holds the winner), weights fitted on one half of the dates and scored on the other, both ways. Same runners and races for every score, so
differences between scores are fair even though the absolute figures are not comparable with full-field tests.
New pre-race inputs (formula residuals only, no model leakage): the horse's last formula miss, mean of the last four, number of bad runs in the last four.
Run: PYTHONPATH=. python research/proj_two_part.py"""
import os, sys
import lightgbm as lgb, numpy as np, pandas as pd
from scipy.optimize import minimize
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'projection'))
import ctx as C

BAD = -12.0
rp = C.training_frame()
pg = rp[rp.f.notna()].copy().sort_values(['horse_id', 'date']).reset_index(drop=True)
g = pg.groupby('horse_id').resid
pg['p1'] = g.shift(1)
sh = [g.shift(k) for k in (1, 2, 3, 4)]
st = pd.concat(sh, axis=1)
pg['m4'] = st.mean(axis=1)
pg['bad4'] = (st < BAD).sum(axis=1).where(st.notna().any(axis=1))
classes = sorted(pg.cls.dropna().unique().tolist())
pg['cls_c'] = C._cls(pg.cls, classes)
NEW = ['p1', 'm4', 'bad4']
F0, F1 = C.FEATS, C.FEATS + NEW
cut, es = pd.Timestamp('2026-01-01'), pd.Timestamp('2025-10-01')
tr_all = pg[pg.date < cut]
tr, va = pg[pg.date < es], pg[(pg.date >= es) & (pg.date < cut)]
P = dict(learning_rate=0.03, num_leaves=31, min_child_samples=100, subsample=0.8, subsample_freq=1, colsample_bytree=0.8, reg_lambda=5, verbose=-1)
te = pg[pg.date >= cut].copy()

m0 = lgb.LGBMRegressor(n_estimators=3000, **P).fit(tr[F0], tr.resid, eval_set=[(va[F0], va.resid)], callbacks=[lgb.early_stopping(100, verbose=False)])
te['proj'] = te.f + m0.predict(te[F0])
m1 = lgb.LGBMRegressor(n_estimators=3000, **P).fit(tr[F1], tr.resid, eval_set=[(va[F1], va.resid)], callbacks=[lgb.early_stopping(100, verbose=False)])
te['proj2'] = te.f + m1.predict(te[F1])
mq = lgb.LGBMRegressor(objective='quantile', alpha=0.5, n_estimators=3000, **P).fit(tr[F1], tr.resid, eval_set=[(va[F1], va.resid)], callbacks=[lgb.early_stopping(100, verbose=False)])
te['q50'] = te.f + mq.predict(te[F1])
yb = (pg.resid < BAD).astype(int)
mb = lgb.LGBMClassifier(n_estimators=3000, **P).fit(tr[F1], yb[tr.index], eval_set=[(va[F1], yb[va.index])], callbacks=[lgb.early_stopping(100, verbose=False)])
te['pbad'] = mb.predict_proba(te[F1])[:, 1]
te['lsafe'] = np.log(1 - te.pbad)
print(f"trees mean {m0.best_iteration_} mean+new {m1.best_iteration_} median {mq.best_iteration_} risk {mb.best_iteration_}; held-out runs {len(te):,}")
for c in ('proj', 'proj2', 'q50'):
    e = te.wpr - te[c]; print(f"  {c:6s} RMSE {np.sqrt((e**2).mean()):.3f} bias {e.mean():+.2f} median miss {e.median():+.2f}")
from sklearn.metrics import roc_auc_score
print(f"  risk model AUC on held-out runs {roc_auc_score((te.resid < BAD).astype(int), te.pbad):.3f}, mean predicted {100*te.pbad.mean():.1f}% vs actual {100*(te.resid < BAD).mean():.1f}%")

te['race'] = te.date.astype(str) + '|' + te.track.astype(str) + '|' + te.distance.astype(str) + '|' + te.field_size.astype(str) + '|' + te.race_class.astype(str)
te['won'] = (te.positionFinish == 1).astype(int)
te['nr'] = te.groupby('race').won.transform('size')
te['nw'] = te.groupby('race').won.transform('sum')
d = te[(te.nr >= 3) & (te.nw == 1)].copy()
d['rid'] = d.race.astype('category').cat.codes
print(f"winner test: {d.rid.nunique():,} races, {len(d):,} runners (store runners only, winner in the store)")

def ll_parts(w, X, won, rid):
    s = X @ w; df = pd.DataFrame({'s': s, 'r': rid})
    mx = df.groupby('r').s.transform('max').values; e = np.exp(s - mx)
    lse = np.log(pd.Series(e).groupby(rid).transform('sum').values) + mx
    return (s - lse)
def fit(df, cols):
    f = lambda w: -ll_parts(w, df[cols].values, df.won.values, df.rid.values)[df.won.values == 1].mean()
    return minimize(f, np.full(len(cols), .1), method='L-BFGS-B').x
def per_race(df, cols, w):
    s = ll_parts(w, df[cols].values, df.won.values, df.rid.values)
    t = df.assign(ll=s, sc=df[cols].values @ w)
    top = t.loc[t.groupby('rid').sc.idxmax()]
    return t[t.won == 1].set_index('rid').ll, top.set_index('rid').won
dates = sorted(d.date.unique()); half = dates[len(dates) // 2]
A, B = d[d.date < half], d[d.date >= half]
sets = {'Proj (mean, today)': ['proj'], 'Proj + last-miss inputs': ['proj2'], 'Median rating': ['q50'], 'Proj + bad-run risk': ['proj', 'lsafe'],
        'Median + bad-run risk': ['q50', 'lsafe'], 'Proj + median + risk': ['proj', 'q50', 'lsafe'], 'Proj2 + risk': ['proj2', 'lsafe']}
res = {}
for lab, cols in sets.items():
    lls, tops, ws = [], [], []
    for a, b in ((A, B), (B, A)):
        w = fit(a, cols); ll, tp = per_race(b, cols, w); lls.append(ll); tops.append(tp); ws.append(w)
    res[lab] = (pd.concat(lls), pd.concat(tops), np.mean(ws, axis=0))
base = res['Proj (mean, today)']
rng = np.random.default_rng(0); idx = base[0].index.values
print(f"\n{'score':26s} {'winner LL':>10s} {'top pick':>9s} {'gain vs Proj':>13s} {'se':>7s}  weights")
for lab, (ll, tp, w) in res.items():
    df_ = (ll - base[0]).values
    print(f"{lab:26s} {ll.mean():10.4f} {100*tp.mean():8.1f}% {df_.mean():+13.4f} {df_.std()/np.sqrt(len(df_)):7.4f}  {np.round(w, 3)}")
# does risk matter more where it varies most inside the race?
te.to_pickle(os.environ.get('TP_OUT', 'tp.pkl'))
