"""As-of venue feature for the context Proj (22 Oct 2026, owner: add it). ven_eff = shrunk mean formula residual of the venue's page runs in [date-WINDOW-GAP, date-GAP)
(runner-page ATW ratings only). GAP keeps the newest runs out because their page ratings may still be Preliminary live but are Final in the training history.
Fit before 2026-01 (early stop 2025-10..12), score 2026-01+, 3 seeds, race-clustered paired bootstrap. Run: PYTHONPATH=. python research/venue_feature_test.py"""
import sys, numpy as np, pandas as pd, lightgbm as lgb
sys.path.insert(0, 'projection')
import ctx as C
rp = C.training_frame()
rp['venue'] = rp.venue.astype(str).str.strip().str.lower()
rp['cls_c'] = C._cls(rp.cls, sorted(rp.cls.dropna().unique().tolist()))
pg0 = rp[rp.f.notna()].copy()
def add_ven(df, window, gap, k, name):
    v = df[df.resid.notna()].groupby(['venue', 'date']).resid.agg(['sum', 'count']).reset_index().sort_values(['venue', 'date'])
    out = []
    for ven, d in v.groupby('venue'):
        dd = d.date.values; s = d['sum'].values; c = d['count'].values
        cs, cc = np.concatenate([[0], np.cumsum(s)]), np.concatenate([[0], np.cumsum(c)])
        hi = np.searchsorted(dd, dd - np.timedelta64(gap, 'D'), side='left')              # runs strictly before date-gap
        lo = np.searchsorted(dd, dd - np.timedelta64(gap + window, 'D'), side='left')
        out.append(pd.DataFrame({'venue': ven, 'date': dd, name + '_s': cs[hi] - cs[lo], name + '_n': cc[hi] - cc[lo]}))
    o = pd.concat(out)
    df = df.merge(o, on=['venue', 'date'], how='left')
    df[name + '_n'] = df[name + '_n'].fillna(0); df[name + '_s'] = df[name + '_s'].fillna(0)
    df[name] = df[name + '_s'] / (df[name + '_n'] + k)
    return df
pg = pg0
variants = {'v180_g0_k100': (180, 0, 100), 'v180_g6_k100': (180, 6, 100), 'v365_g6_k100': (365, 6, 100), 'v180_g6_k50': (180, 6, 50), 'v180_g6_k200': (180, 6, 200)}
for nm, (w, g, k) in variants.items():
    pg = add_ven(pg, w, g, k, nm)
cut, es = pd.Timestamp('2026-01-01'), pd.Timestamp('2025-10-01')
tr, va, te = pg[pg.date < es], pg[(pg.date >= es) & (pg.date < cut)], pg[pg.date >= cut].copy()
P = dict(n_estimators=3000, learning_rate=0.03, num_leaves=31, min_child_samples=100, subsample=0.8, subsample_freq=1, colsample_bytree=0.8, reg_lambda=5, verbose=-1)
def run(feats):
    ps = []
    for s in range(3):
        m = lgb.LGBMRegressor(**P, random_state=s).fit(tr[feats], tr.resid, eval_set=[(va[feats], va.resid)], callbacks=[lgb.early_stopping(100, verbose=False)])
        ps.append(m.predict(te[feats]))
    return np.mean(ps, axis=0)
base = run(C.FEATS); e0 = (te.resid - base).values
print('baseline RMSE', round(float(np.sqrt((e0 ** 2).mean())), 4), 'n', len(te))
rid = te.venue.astype(str) + te.date.astype(str)          # cluster by venue-day
codes, uniq = pd.factorize(rid); rng = np.random.default_rng(0)
idx = rng.integers(0, len(uniq), (400, len(uniq)))
def boot(d):
    s = np.bincount(codes, weights=d); n = np.bincount(codes)
    return s[idx].sum(1) / n[idx].sum(1)
for nm in variants:
    e1 = (te.resid - run(C.FEATS + [nm])).values
    d = e0 ** 2 - e1 ** 2; b = boot(d)
    print(f"{nm:14s} RMSE {np.sqrt((e1 ** 2).mean()):.4f}  paired MSE gain {d.mean():+.3f}  95% [{np.percentile(b, 2.5):+.3f},{np.percentile(b, 97.5):+.3f}]")
