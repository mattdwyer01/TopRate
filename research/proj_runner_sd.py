"""Does a per-runner uncertainty (size of the miss predicted from pre-race facts) improve win chances over one noise level, or noise by earlier-run count as the live Rated $
uses? (22 Oct 2026). Runner-page ATW ratings only. Mean = the live Proj (formula + context, fit before 2026-01). Spread model: LightGBM on the same pre-race inputs predicting
|formula miss|, fit on runs before 2026-01. Win chance of each runner = chance its noisy figure (normal, own spread) is the highest among the runners the store holds in that race
(a race = date, track, distance, field size, class; races where the store holds the winner, 3+ runners). Scale factors are fitted on one half of the dates and scored on the other,
both ways. Run: PYTHONPATH=. python research/proj_runner_sd.py"""
import os, sys
import lightgbm as lgb, numpy as np, pandas as pd
from scipy.stats import norm
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'projection'))
import ctx as C

rp = C.training_frame()
pg = rp[rp.f.notna()].copy().sort_values(['horse_id', 'date']).reset_index(drop=True)
classes = sorted(pg.cls.dropna().unique().tolist()); pg['cls_c'] = C._cls(pg.cls, classes)
cut, es = pd.Timestamp('2026-01-01'), pd.Timestamp('2025-10-01')
tr, va, te = pg[pg.date < es], pg[(pg.date >= es) & (pg.date < cut)], pg[pg.date >= cut].copy()
P = dict(learning_rate=0.03, num_leaves=31, min_child_samples=100, subsample=0.8, subsample_freq=1, colsample_bytree=0.8, reg_lambda=5, verbose=-1)
m0 = lgb.LGBMRegressor(n_estimators=3000, **P).fit(tr[C.FEATS], tr.resid, eval_set=[(va[C.FEATS], va.resid)], callbacks=[lgb.early_stopping(100, verbose=False)])
te['mu'] = te.f + m0.predict(te[C.FEATS])
trv = pg[pg.date < cut]
ms = lgb.LGBMRegressor(n_estimators=250, learning_rate=0.03, num_leaves=15, min_child_samples=200, subsample=.8, subsample_freq=1, colsample_bytree=.8, verbose=-1).fit(trv[C.FEATS], trv.resid.abs())
te['sd_hat'] = np.clip(ms.predict(te[C.FEATS]), 3.0, None) * 1.25      # mean |e| to sd for a normal
byn = trv.groupby(trv.n.clip(upper=8).astype(int)).resid.std()
te['sd_n'] = te.n.clip(upper=8).astype(int).map(byn)
print(f"spread model: predicted sd range {te.sd_hat.quantile(.05):.1f} to {te.sd_hat.quantile(.95):.1f}; by earlier runs sd {byn.round(1).tolist()}")
for c in ('sd_hat', 'sd_n'):
    z = (te.wpr - te.mu) / te[c]; print(f"  {c}: standardised miss sd {z.std():.3f} (1.0 = right), share beyond 2 sd {100*(z.abs()>2).mean():.1f}% (normal 4.6%), beyond 3 sd {100*(z.abs()>3).mean():.1f}% (normal 0.3%)")

te['race'] = te.date.astype(str) + '|' + te.track.astype(str) + '|' + te.distance.astype(str) + '|' + te.field_size.astype(str) + '|' + te.race_class.astype(str)
te['won'] = (te.positionFinish == 1).astype(int)
te['nr'] = te.groupby('race').won.transform('size'); te['nw'] = te.groupby('race').won.transform('sum')
d = te[(te.nr >= 3) & (te.nw == 1)].copy()
races = [(g.date.iloc[0], g.mu.values, g.sd_hat.values, g.sd_n.values, int(np.argmax(g.won.values)), g.f.values) for _, g in d.groupby('race')]
print(f"winner test: {len(races):,} races, {len(d):,} runners")
X = np.linspace(-1, 1, 1)  # placeholder
def win_prob(mu, sd):
    lo, hi = (mu - 5 * sd).min(), (mu + 5 * sd).max()
    x = np.linspace(lo, hi, 400)
    cdf = norm.cdf((x[None, :] - mu[:, None]) / sd[:, None]); pdf = norm.pdf((x[None, :] - mu[:, None]) / sd[:, None]) / sd[:, None]
    logc = np.log(np.clip(cdf, 1e-300, None)); tot = logc.sum(axis=0)
    p = (pdf * np.exp(tot[None, :] - logc)).sum(axis=1) * (x[1] - x[0])
    return p / p.sum()
def ll(rs, kind, k, floor=0.0):
    out = []
    for dt, mu, sh, sn, wi, f in rs:
        sd = {'const': np.full(len(mu), k), 'n': sn * k, 'hat': np.maximum(sh * k, floor)}[kind]
        out.append(np.log(max(win_prob(mu, sd)[wi], 1e-9)))
    return np.array(out)
dates = sorted({r[0] for r in races}); half = dates[len(dates) // 2]
A = [r for r in races if r[0] < half]; B = [r for r in races if r[0] >= half]
def best_k(rs, kind, grid):
    sc = [ll(rs, kind, k).mean() for k in grid]; return grid[int(np.argmax(sc))], max(sc)
grids = {'const': np.arange(5, 14.1, 1.0), 'n': np.arange(0.7, 1.41, 0.1), 'hat': np.arange(0.7, 1.41, 0.1)}
print(f"\n{'noise model':34s} {'winner LL':>10s} {'gain vs const':>14s} {'se':>7s}  scale (A / B)")
tot = {}
for kind, lab in (('const', 'one noise level'), ('n', 'by earlier-run count (live)'), ('hat', 'per-runner predicted spread')):
    ka, _ = best_k(A, kind, grids[kind]); kb, _ = best_k(B, kind, grids[kind])
    l = np.concatenate([ll(B, kind, ka), ll(A, kind, kb)]); tot[kind] = (l, ka, kb)
base = tot['const'][0]
for kind, lab in (('const', 'one noise level'), ('n', 'by earlier-run count (live)'), ('hat', 'per-runner predicted spread')):
    l, ka, kb = tot[kind]; dd = l - base
    print(f"{lab:34s} {l.mean():10.4f} {dd.mean():+14.4f} {dd.std()/np.sqrt(len(dd)):7.4f}  {ka:.1f} / {kb:.1f}")
# by level: where does the gain come from
l = tot['hat'][0] - base
lv = np.concatenate([[r[5].mean() for r in B], [r[5].mean() for r in A]])
q = pd.qcut(lv, 4, labels=False); print("gain (per-runner spread vs one level) by field quality quartile (low to high mean figure):", [round(float(l[q == i].mean()), 4) for i in range(4)])
