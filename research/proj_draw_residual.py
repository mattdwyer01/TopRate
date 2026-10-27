"""Does barrier, by venue and distance, still predict the live Proj's misses? (27 Oct 2026)
Refits the plain and relevance context models exactly as projection/train_ctx.py does (fit before 2026-01, early stop 2025-10..12), scores the held-out 2026 runs, then regresses each run's miss
(actual page rating minus Proj) on barrier position, pooled and per venue x distance band. A slope of zero means the model has already absorbed the draw.
Run: PYTHONPATH=. python research/proj_draw_residual.py OUTDIR"""
import sys, os, json
import numpy as np, pandas as pd, lightgbm as lgb
sys.path.insert(0, 'projection')
import ctx as C
out = sys.argv[1]
rp = C.training_frame_rel()
pg = rp[rp.f.notna()].copy()
classes = sorted(pg.cls.dropna().unique().tolist()); pg['cls_c'] = C._cls(pg.cls, classes)
cut, es = pd.Timestamp('2026-01-01'), pd.Timestamp('2025-10-01')
tr, va, te = pg[pg.date < es], pg[(pg.date >= es) & (pg.date < cut)], pg[pg.date >= cut].copy()
params = dict(n_estimators=4000, learning_rate=0.03, num_leaves=31, min_child_samples=100, subsample=0.8, subsample_freq=1, colsample_bytree=0.8, reg_lambda=5, verbose=-1, objective='huber', alpha=4.0)
F0, F1 = C.FEATS, C.FEATS + C.REL_FEATS
def fit(feats, a, b):
    m = lgb.LGBMRegressor(**params); m.fit(a[feats], a.resid, eval_set=[(b[feats], b.resid)], callbacks=[lgb.early_stopping(100, verbose=False)]); return m
m0 = fit(F0, tr, va)
rel = lambda d: d[d.n >= C.REL_MIN_RUNS]
m1 = fit(F1, rel(tr), rel(va))
te['c0'] = m0.predict(te[F0]); use = (te.n >= C.REL_MIN_RUNS).values
te['c1'] = te.c0; te.loc[use, 'c1'] = m1.predict(te.loc[use, F1])
te['e'] = te.resid - te.c1
print(len(te), 'held-out runs, RMSE', round(float(np.sqrt((te.e ** 2).mean())), 3))
te['bf'] = te.barr_f - 0.5
te['vk'] = te.venue.astype(str)
te['band'] = pd.cut(te.distance, [0, 1100, 1300, 1650, 2000, 9999], labels=['<=1100', '1101-1300', '1301-1650', '1651-2000', '2001+']).astype(str)
te['grp'] = te.date.astype(str) + '|' + te.vk + '|' + te.distance.astype(str)
te['ed'] = te.e - te.groupby('grp').e.transform('mean')
te.to_pickle(out + '/proj_resid_te.pkl')
def slope(x, col='ed'):
    xc = x.bf - x.bf.mean(); sxx = (xc ** 2).sum()
    b = (xc * x[col]).sum() / sxx
    sc = (xc * (x[col] - b * xc)).groupby(x.grp).sum()
    return b, np.sqrt((sc ** 2).sum()) / sxx
b, se = slope(te); print(f'POOLED slope of Proj miss on barrier (rail to widest): {b:+.2f} pts (se {se:.2f})  [raw atw draw effect was about -1.5]')
for k, z in te.groupby('band'):
    b, se = slope(z); print(f'  {k:10s} {b:+.2f} (se {se:.2f}) n={len(z)}')
# per cell, with the earlier raw atw slopes for comparison
raw = pd.read_csv(out + '/draw_cells_conv.csv')[['venue', 'band', 'all']].rename(columns={'all': 'raw'})
rows = []
for (v, bd), z in te.groupby(['vk', 'band']):
    if len(z) < 250: continue
    b, se = slope(z); rows.append(dict(venue=v, band=bd, n=len(z), resid_slope=b, se=se, t=b / se))
r = pd.DataFrame(rows).merge(raw, on=['venue', 'band'], how='left')
print(f'\n{len(r)} venue x band cells with 250+ held-out runs; |t|>2: {(r.t.abs() > 2).sum()} (about {0.046 * len(r):.1f} expected by chance)')
m = r.dropna(subset=['raw'])
print(f'cells with a raw atw slope: {len(m)}; correlation of the Proj miss slope with the raw draw slope: {m.resid_slope.corr(m.raw):+.2f}; mean raw {m.raw.mean():+.2f}, mean residual slope {m.resid_slope.mean():+.2f}')
print(r.sort_values('t').head(8).round(2).to_string(index=False)); print(r.sort_values('t').tail(8).round(2).to_string(index=False))
# out of sample: shrunk cell slope from 2026-01..06 residuals applied to 2026-07+
a, b_ = te[te.date < '2026-07-01'], te[te.date >= '2026-07-01'].copy()
K = 400.0
tab = {}
for (v, bd), z in a.groupby(['vk', 'band']):
    bb, _ = slope(z); n = len(z); tab[(v, bd)] = bb * n / (n + K)
gb, _ = slope(a)
b_['adj'] = [tab.get((v, bd), 0.0) * x for v, bd, x in zip(b_.vk, b_.band, b_.bf)]
b_['adj_pool'] = gb * b_.bf
rm = lambda x: float(np.sqrt((x ** 2).mean()))
print(f'\nOUT OF SAMPLE (fit slopes on 2026-01..06 misses, apply to 2026-07+ {len(b_)} runs): RMSE now {rm(b_.e):.4f}, with pooled draw term {rm(b_.e - b_.adj_pool):.4f}, with venue x band draw term {rm(b_.e - b_.adj):.4f}')
d = (b_.e ** 2 - (b_.e - b_.adj) ** 2); print(f'paired squared-error gain per run, venue x band term: {d.mean():+.4f} (se {d.std() / np.sqrt(len(d)):.4f})')
r.to_csv(out + '/proj_resid_cells.csv', index=False)
