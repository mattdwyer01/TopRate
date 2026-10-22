"""Do different scenarios need different projections? (22 Oct 2026). Runner-page ATW ratings only; the deployed Proj layers (formula + context, relevance model for 3+ earlier runs)
fit before 2026-01 (early stop 2025-10..12) and scored on the 2026 held-out runs. For each pre-race scenario: runs, error and bias of the global model, and the error of a SPECIALIST model
trained only on that scenario's earlier runs (same inputs, own early stopping) so the two are compared on the same held-out runs. Run: PYTHONPATH=. python research/proj_scenarios.py"""
import os, sys, warnings
warnings.filterwarnings('ignore')
import lightgbm as lgb, numpy as np, pandas as pd
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'projection'))
import ctx as C

CACHE = os.environ.get('ROBUST_FRAME', '')
rp = pd.read_pickle(CACHE) if CACHE and os.path.exists(CACHE) else C.training_frame_rel()     # the frame cached by research/proj_robust.py skips the slow relevance features
pg = rp[rp.f.notna() & (rp.n >= C.REL_MIN_RUNS)].copy()
classes = sorted(pg.cls.dropna().unique().tolist()); pg['cls_c'] = C._cls(pg.cls, classes)
cut, es = pd.Timestamp('2026-01-01'), pd.Timestamp('2025-10-01')
F1 = C.FEATS + C.REL_FEATS
tr, va, te = pg[pg.date < es], pg[(pg.date >= es) & (pg.date < cut)], pg[pg.date >= cut].copy()
P = dict(learning_rate=0.03, num_leaves=31, min_child_samples=100, subsample=0.8, subsample_freq=1, colsample_bytree=0.8, reg_lambda=5, verbose=-1, n_jobs=4)
def fit(a, b):
    return lgb.LGBMRegressor(n_estimators=4000, **P).fit(a[F1], a.resid, eval_set=[(b[F1], b.resid)], callbacks=[lgb.early_stopping(100, verbose=False)])
mg = fit(tr, va)
te['e_g'] = te.resid - mg.predict(te[F1])
r = lambda x: float(np.sqrt((x ** 2).mean()))
print(f"global model on 3+ earlier runs: {len(te):,} held-out runs, RMSE {r(te.e_g):.3f}, bias {te.e_g.mean():+.2f}\n")
def lab(df):
    wet = df.going_n >= 5
    cg = np.select([df.cls.astype(str).str.startswith('MAI'), df.cls.astype(str).str.startswith('BM'), df.cls.astype(str).str.startswith('RST'), df.cls.astype(str).str.startswith('CLS'), df.cls.astype(str) == 'OPEN'],
                   ['maiden', 'benchmark', 'restricted', 'class', 'open'], 'other')
    return {
        'spell': pd.cut(df.d_last, [-1, 28, 60, 9999], labels=['in work (28d or less)', '29-60 days', 'first up (60+ days)']),
        'distance': pd.cut(df.distance, [0, 1299, 1699, 2099, 9999], labels=['sprint (<1300)', 'mile (1300-1699)', 'middle (1700-2099)', 'staying (2100+)']),
        'going': pd.Series(np.where(df.going_n.isna(), 'unknown', np.where(wet, 'wet (5+)', 'dry (4 or less)')), index=df.index),
        'level': pd.cut(df.f, [0, 60, 70, 80, 300], labels=['under 60', '60-70', '70-80', 'over 80']),
        'class': pd.Series(cg, index=df.index),
        'earlier runs': pd.cut(df.n, [2, 5, 12, 999], labels=['3-5', '6-12', '13+']),
        'field': pd.cut(df.field_size, [0, 8, 12, 99], labels=['8 or fewer', '9-12', '13+']),
        'weight vs last': pd.cut(df.wt_chg, [-99, -2, 2, 99], labels=['down 2kg+', 'same', 'up 2kg+']),
    }
LT, LV, LE = lab(tr), lab(va), lab(te)
print(f"{'scenario':32s} {'runs':>6s} {'global':>7s} {'bias':>6s} {'specialist':>11s} {'gain':>7s}")
rows = []
for fam in LE:
    for v in [x for x in LE[fam].dropna().unique()]:
        s = (LE[fam] == v).values
        if s.sum() < 500: continue
        a, b = tr[(LT[fam] == v).values], va[(LV[fam] == v).values]
        if len(a) < 3000 or len(b) < 500:
            print(f"{fam + ': ' + str(v):32s} {int(s.sum()):6d} {r(te.e_g[s]):7.3f} {te.e_g[s].mean():+6.2f}   (too few training runs for a specialist)"); continue
        m = fit(a, b); e = te[s].resid - m.predict(te[s][F1])
        d = te.e_g[s] ** 2 - e ** 2
        print(f"{fam + ': ' + str(v):32s} {int(s.sum()):6d} {r(te.e_g[s]):7.3f} {te.e_g[s].mean():+6.2f} {r(e):11.3f} {100*(1-r(e)/r(te.e_g[s])):6.2f}%  (se {d.std()/np.sqrt(len(d)):.2f} pts^2)")
