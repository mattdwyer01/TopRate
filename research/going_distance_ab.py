"""6 Nov 2026 (owner: Defiantly's correction was -1.4, mostly a big drop in distance and overseas going the parser reads as NaN). Held-out A/B on the page store (no converted history), fit before 2026-01,
early stop 2025-10..12, scored on 2026. Variants: A live (going words NaN), B going words parsed, C = B plus overseas flags (last run and share of last four runs on an un-numbered going).
Also reports the live model's miss by size of the distance change, to see whether big drops are over- or under-penalised.
Run: PYTHONPATH=.:projection PROJECTION_RATINGS=toprate python research/going_distance_ab.py"""
import sys
import lightgbm as lgb, numpy as np, pandas as pd
sys.path.insert(0, 'projection')
import ctx as C

P = dict(n_estimators=4000, learning_rate=0.03, num_leaves=31, min_child_samples=100, subsample=0.8, subsample_freq=1, colsample_bytree=0.8, reg_lambda=5, verbose=-1, objective='huber', alpha=4.0)
WORDS = {'firm': 2, 'fast': 3, 'good': 4, 'sand': 4, 'dead': 5, 'slow': 6, 'soft': 6, 'heavy': 9, 'yielding': 5}
orig = C.going_num

def parsed(s):
    out = orig(s)
    alt = pd.Series(np.asarray(s), index=getattr(s, 'index', None)).astype(str).str.lower().str.extract(r'^(firm|fast|good|sand|dead|slow|soft|heavy|yielding)\b')[0].map(WORDS)
    return out.where(out.notna(), alt.values)

def build(patch):
    C.going_num = parsed if patch else orig
    rp = C.training_frame_rel(True)
    g = rp.going.astype(str).str.lower()
    rp['os_g'] = (g.str.match(r'^(firm|fast|good|sand|dead|slow|soft|heavy|yielding)\b') & ~g.str.contains(r'\d')).astype(float)
    k = rp.groupby('horse_id').os_g
    rp['os_last'] = k.shift(1)
    rp['os_frac4'] = sum(k.shift(j).fillna(0) for j in range(1, 5)) / rp.n.clip(upper=4).replace(0, np.nan)
    return rp

r = lambda x: float(np.sqrt((x ** 2).mean()))
cut, es = pd.Timestamp('2026-01-01'), pd.Timestamp('2025-10-01')
rel = lambda d: d[d.n >= C.REL_MIN_RUNS]
res = {}
for name, patch, extra in (('A live', False, []), ('B parsed', True, []), ('C parsed+flag', True, ['os_last', 'os_frac4'])):
    rp = build(patch)
    pg = rp[rp.f.notna()].copy()
    classes = sorted(pg.cls.dropna().unique().tolist())
    pg['cls_c'] = C._cls(pg.cls, classes)
    tr, va, te = pg[pg.date < es], pg[(pg.date >= es) & (pg.date < cut)], pg[pg.date >= cut].copy()
    F0 = list(C.FEATS2) + extra
    F1 = F0 + list(C.REL_FEATS2)
    m0 = lgb.LGBMRegressor(**P).fit(tr[F0], tr.resid, eval_set=[(va[F0], va.resid)], callbacks=[lgb.early_stopping(100, verbose=False)])
    m1 = lgb.LGBMRegressor(**P).fit(rel(tr)[F1], rel(tr).resid, eval_set=[(rel(va)[F1], rel(va).resid)], callbacks=[lgb.early_stopping(100, verbose=False)])
    use = (te.n >= C.REL_MIN_RUNS).values
    c = m0.predict(te[F0]); c1 = np.full(len(te), np.nan); c1[use] = m1.predict(te.loc[use, F1])
    te['corr'] = np.where(use, c1, c); te['e'] = te.resid - te['corr']
    res[name] = te
    print(name, 'trees', m0.best_iteration_, m1.best_iteration_, flush=True)
A, B, Cc = res['A live'], res['B parsed'], res['C parsed+flag']
key = ['horse_id', 'date']
for nm, X in (('A', A), ('B', B), ('C', Cc)):
    X['k'] = X.horse_id.astype(str) + X.date.astype(str)
idx = A.k.values
Bi, Ci = B.set_index('k').loc[idx], Cc.set_index('k').loc[idx]
A = A.reset_index(drop=True)
os_run = (Ci.os_last.values == 1) | (Ci.os_frac4.values > 0)
big_drop = (A.dist_chg <= -600).values
huge_drop = (A.dist_chg <= -1000).values
print(f"\n{'group':44s} {'n':>6s} | RMSE A B C | mean miss A B C | median A B C")
for nm, m in (('all', np.ones(len(A), bool)), ('last run on un-numbered going (overseas)', Ci.os_last.values == 1), ('any of last 4 on un-numbered going', os_run),
              ('no overseas-going runs', ~os_run), ('distance drop >= 600m', big_drop), ('distance drop >= 1000m', huge_drop)):
    a, b, c = A.e.values[m], Bi.e.values[m], Ci.e.values[m]
    if m.sum() == 0: continue
    print(f"{nm:44s} {m.sum():6d} | {r(a):.3f} {r(b):.3f} {r(c):.3f} | {a.mean():+.2f} {b.mean():+.2f} {c.mean():+.2f} | {np.median(a):+.2f} {np.median(b):+.2f} {np.median(c):+.2f}")
d = A.e.values ** 2 - Bi.e.values ** 2; print('paired sq-error gain B over A', round(d.mean(), 3), 'se', round(d.std() / np.sqrt(len(d)), 3))
d = A.e.values ** 2 - Ci.e.values ** 2; print('paired sq-error gain C over A', round(d.mean(), 3), 'se', round(d.std() / np.sqrt(len(d)), 3))
print('\nLive model (A): correction and miss by distance change today minus last run')
bins = [-9999, -1000, -600, -300, -100, 100, 300, 600, 1000, 9999]
A['dc'] = pd.cut(A.dist_chg, bins)
print(A.groupby('dc', observed=True).agg(n=('e', 'size'), corr_mean=('corr', 'mean'), miss_mean=('e', 'mean'), miss_median=('e', 'median'), rmse=('e', lambda x: r(x))).round(2).to_string())
