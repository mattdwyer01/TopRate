"""Mode-seeking Proj (22 Oct 2026). The shipped relevance model minimises squared error, so it predicts the MEAN rating, which the rare bad-run tail pulls down.
This compares objectives that centre on the most likely outcome, for horses with 3+ earlier runs (ctx.REL_MIN_RUNS), runner-page ATW ratings only, fit before 2026-01-01
with early stopping on 2025-10..12, scored on the 2026 held-out runs:
  l2 (shipped) | huber alpha 8 / 4 / 2 | quantile 0.5 / 0.6 | welsch (Gaussian-kernel loss, sigma 5 / 3.5) started from the alpha 4 Huber model
Scores: share of runs whose rating lands within 2 / 3 / 5 points of Proj (the 'most likely outcome' hit rate), the peak (mode) of the residual density, median, mean, MAE,
RMSE, and the winner log-lik inside each race as the runner-page store holds it (scale cross-fitted on date halves).
Run: PYTHONPATH=. python research/proj_mode.py   (frame cached in $MODE_FRAME)"""
import os, sys, warnings
warnings.filterwarnings('ignore')
import lightgbm as lgb, numpy as np, pandas as pd
from scipy.optimize import minimize
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'projection'))
import ctx as C

CACHE = os.environ.get('MODE_FRAME', 'mode_frame.pkl')
rp = pd.read_pickle(CACHE) if os.path.exists(CACHE) else C.training_frame_rel()
if not os.path.exists(CACHE): rp.to_pickle(CACHE)
pg = rp[rp.f.notna() & (rp.n >= C.REL_MIN_RUNS)].copy()
classes = sorted(pg.cls.dropna().unique().tolist()); pg['cls_c'] = C._cls(pg.cls, classes)
cut, es = pd.Timestamp('2026-01-01'), pd.Timestamp('2025-10-01')
F = C.FEATS + C.REL_FEATS
tr, va, te = pg[pg.date < es], pg[(pg.date >= es) & (pg.date < cut)], pg[pg.date >= cut].copy()
P = dict(learning_rate=0.03, num_leaves=31, min_child_samples=100, subsample=0.8, subsample_freq=1, colsample_bytree=0.8, reg_lambda=5, verbose=-1, n_jobs=4)
print(f'train {len(tr):,} valid {len(va):,} held-out {len(te):,}', flush=True)


def fit(**kw):
    m = lgb.LGBMRegressor(n_estimators=4000, **{**P, **kw})
    m.fit(tr[F], tr.resid, eval_set=[(va[F], va.resid)], callbacks=[lgb.early_stopping(100, verbose=False)])
    return m


def welsch(sig):
    def obj(y, p):
        r = y - p
        return -r * np.exp(-r * r / (2 * sig * sig)), np.ones_like(r)
    def met(y, p):
        r = y - p
        return 'welsch', float((sig * sig * (1 - np.exp(-r * r / (2 * sig * sig)))).mean()), False
    return obj, met


def fit_welsch(sig, base):
    obj, met = welsch(sig)
    m = lgb.LGBMRegressor(n_estimators=4000, objective=obj, **P)
    m.fit(tr[F], tr.resid, init_score=base.predict(tr[F]), eval_set=[(va[F], va.resid)], eval_init_score=[base.predict(va[F])], eval_metric=met,
          callbacks=[lgb.early_stopping(100, verbose=False)])
    return m


models = {}
models['l2 (shipped)'] = (fit(), None)
for a in (8.0, 4.0, 2.0): models[f'huber {a:g}'] = (fit(objective='huber', alpha=a), None)
for q in (0.5, 0.6): models[f'quantile {q}'] = (fit(objective='quantile', alpha=q), None)
base = models['huber 4'][0]
for s in (5.0, 3.5):
    mw = fit_welsch(s, base); models[f'welsch {s:g}'] = (mw, base)
    print(f'welsch {s:g} trees {mw.best_iteration_}', flush=True)

for name, (m, b) in models.items():
    p = m.predict(te[F]) + (b.predict(te[F]) if b is not None else 0)
    te['mu_' + name] = te.f + p; te['e_' + name] = te.wpr - te['mu_' + name]


def peak(e):
    x = np.linspace(-12, 12, 481); e = e.values[np.abs(e.values) < 40]; e = e[np.random.RandomState(0).permutation(len(e))[:20000]]
    d = np.exp(-0.5 * ((x[:, None] - e[None, :]) / 1.5) ** 2).sum(1)
    return x[d.argmax()]


print(f"\n{'variant':14s} {'in2':>6s} {'in3':>6s} {'in5':>6s} {'mode':>6s} {'median':>7s} {'mean':>6s} {'MAE':>6s} {'RMSE':>6s}   (held-out runs with 3+ earlier runs)")
for name in models:
    e = te['e_' + name]
    print(f"{name:14s} {100*(e.abs()<=2).mean():5.1f}% {100*(e.abs()<=3).mean():5.1f}% {100*(e.abs()<=5).mean():5.1f}% {peak(e):+6.2f} {e.median():+7.2f} {e.mean():+6.2f} {e.abs().mean():6.3f} {np.sqrt((e**2).mean()):6.3f}")

te['race'] = te.date.astype(str) + '|' + te.track.astype(str) + '|' + te.distance.astype(str) + '|' + te.field_size.astype(str) + '|' + te.race_class.astype(str)
te['won'] = (te.positionFinish == 1).astype(int); te['nr'] = te.groupby('race').won.transform('size'); te['nw'] = te.groupby('race').won.transform('sum')
d = te[(te.nr >= 3) & (te.nw == 1)].copy(); d['rid'] = d.race.astype('category').cat.codes


def ll(df, col, b):
    s = b * df[col].values; mx = pd.Series(s).groupby(df.rid.values).transform('max').values; e = np.exp(s - mx)
    return (s - (np.log(pd.Series(e).groupby(df.rid.values).transform('sum').values) + mx))[df.won.values == 1]


fitb = lambda df, c: minimize(lambda b: -ll(df, c, b[0]).mean(), [0.15], method='L-BFGS-B').x[0]
dates = sorted(d.date.unique()); half = dates[len(dates) // 2]; A, B = d[d.date < half], d[d.date >= half]
out = {n: np.concatenate([ll(B, 'mu_' + n, fitb(A, 'mu_' + n)), ll(A, 'mu_' + n, fitb(B, 'mu_' + n))]) for n in models}
print(f"\nwinner test ({d.rid.nunique():,} store races, {len(d):,} runners): winner log-lik, gain vs shipped")
for n in models:
    dd = out[n] - out['l2 (shipped)']; print(f"  {n:14s} {out[n].mean():8.4f}  {dd.mean():+.4f} (se {dd.std()/np.sqrt(len(dd)):.4f})")
te.to_pickle(os.environ.get('MODE_OUT', 'mode_te.pkl'))
