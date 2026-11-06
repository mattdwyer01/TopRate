"""6 Nov 2026 (owner: what if non-TAB and picnic races were left out of the training rows? would it make the Proj more consistent?). No historical TAB or meeting-type flag exists in the page store, so the
dashboard's own bush/picnic rule is the proxy: a meeting (venue and date) whose biggest race prize in the store is $20,000 or less (lib/meetings.ts BUSH_TRACK_THRESHOLD). Meetings with no prize recorded
(mostly overseas runs) are 'unknown'. Only TARGET rows are excluded from training; every horse's earlier runs, bush ones included, stay in its history inputs.
Variants: A all training rows (live), B without bush rows, C without bush or unknown rows. Fit before 2026-01 with early stopping on 2025-10..12, scored on 2026 overall and by group.
Run: PYTHONPATH=.:projection PROJECTION_RATINGS=toprate python research/tab_only_training_ab.py"""
import sys
import lightgbm as lgb, numpy as np, pandas as pd
sys.path.insert(0, 'projection')
import ctx as C

P = dict(n_estimators=4000, learning_rate=0.03, num_leaves=31, min_child_samples=100, subsample=0.8, subsample_freq=1, colsample_bytree=0.8, reg_lambda=5, verbose=-1, objective='huber', alpha=4.0)
THRESH = 20000
rp = C.training_frame_rel(True)
pg = rp[rp.f.notna()].copy()
pg['mx'] = pg.groupby(['date', 'vn']).prize.transform('max') if 'prize' in pg.columns else np.nan
pg['grp'] = np.where(pg.mx.isna(), 'unknown', np.where(pg.mx <= THRESH, 'bush', 'tab_like'))
print(pg[pg.date >= '2025-01-01'].grp.value_counts(normalize=True).round(3).to_dict(), flush=True)
classes = sorted(pg.cls.dropna().unique().tolist())
pg['cls_c'] = C._cls(pg.cls, classes)
cut, es = pd.Timestamp('2026-01-01'), pd.Timestamp('2025-10-01')
te = pg[pg.date >= cut].copy()
F0 = list(C.FEATS2); F1 = F0 + list(C.REL_FEATS2)
rel = lambda d: d[d.n >= C.REL_MIN_RUNS]
r = lambda x: float(np.sqrt((x ** 2).mean()))
use = (te.n >= C.REL_MIN_RUNS).values
for name, drop in (('A all rows', []), ('B no bush', ['bush']), ('C no bush/unknown', ['bush', 'unknown'])):
    keep = ~pg.grp.isin(drop)
    tr, va = pg[keep & (pg.date < es)], pg[keep & (pg.date >= es) & (pg.date < cut)]
    m0 = lgb.LGBMRegressor(**P).fit(tr[F0], tr.resid, eval_set=[(va[F0], va.resid)], callbacks=[lgb.early_stopping(100, verbose=False)])
    m1 = lgb.LGBMRegressor(**P).fit(rel(tr)[F1], rel(tr).resid, eval_set=[(rel(va)[F1], rel(va).resid)], callbacks=[lgb.early_stopping(100, verbose=False)])
    c = m0.predict(te[F0]); c1 = np.full(len(te), np.nan); c1[use] = m1.predict(te.loc[use, F1])
    te['e_' + name[0]] = te.resid - np.where(use, c1, c)
    print(name, 'train rows', len(tr), 'trees', m0.best_iteration_, m1.best_iteration_, flush=True)
print(f"\n{'test group':26s} {'n':>6s} | RMSE A B C | MAE A B C | mean miss A B C | within 6 (%) A B C")
for nm, m in (('all 2026', te.n > 0), ('tab_like', te.grp == 'tab_like'), ('bush', te.grp == 'bush'), ('unknown prize', te.grp == 'unknown'), ('tab_like, 3+ runs', (te.grp == 'tab_like') & use)):
    a = te[m]
    print(f"{nm:26s} {len(a):6d} | {r(a.e_A):.3f} {r(a.e_B):.3f} {r(a.e_C):.3f} | {a.e_A.abs().mean():.3f} {a.e_B.abs().mean():.3f} {a.e_C.abs().mean():.3f} | {a.e_A.mean():+.2f} {a.e_B.mean():+.2f} {a.e_C.mean():+.2f} | {100*(a.e_A.abs()<=6).mean():.1f} {100*(a.e_B.abs()<=6).mean():.1f} {100*(a.e_C.abs()<=6).mean():.1f}")
t = te[te.grp == 'tab_like']
for v in 'BC':
    d = t.e_A ** 2 - t['e_' + v] ** 2
    print(f'paired squared-error gain on tab_like, {v} over A: {d.mean():+.3f} se {d.std()/np.sqrt(len(d)):.3f}')
