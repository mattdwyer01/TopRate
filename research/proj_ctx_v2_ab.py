"""A/B of the live context model with and without option 2 (jockey/trainer rates + field-relative block, ctx.FEATS2 / REL_FEATS2) and with page-store vs converted-history
training (27 Oct 2026). All models: formula + Huber context correction (plain for under 3 earlier runs, relevance for 3+), scored on the SAME held-out 2026 page-store runs.
Run: PYTHONPATH=.:research:projection python research/proj_ctx_v2_ab.py [--frac 0.3]"""
import argparse, json, os, sys
import numpy as np, pandas as pd, lightgbm as lgb
sys.path.insert(0, 'projection'); sys.path.insert(0, 'research')
import ctx as C, features as F, conv_history as CH

ap = argparse.ArgumentParser(); ap.add_argument('--frac', type=float, default=0.3)
a = ap.parse_args()
r = lambda x: float(np.sqrt((np.asarray(x) ** 2).mean()))
real = F.runner_page_runs().copy()
F._TR_CACHE['rows'] = CH.build(2020, '2025-12-31', a.frac)
conv = C.training_frame_rel(v2=True); conv = conv[conv.f.notna()].copy()
F._TR_CACHE['rows'] = real
allr = C.training_frame_rel(v2=True); allr = allr[allr.f.notna()].copy()
classes = json.load(open(os.path.join(C.M, 'ctx.json')))['classes']
for d in (conv, allr):
    d['cls_c'] = C._cls(d.cls, classes)
print('converted rows', len(conv), 'page rows', len(allr), 'trainer known (page)', allr.tw.notna().mean().round(3), 'jw', allr.jw.notna().mean().round(3), flush=True)
te = allr[allr.date >= '2026-01-01'].copy()
page_tr = allr[allr.date < '2026-01-01']
es = pd.Timestamp('2025-10-01')
params = dict(n_estimators=4000, learning_rate=0.03, num_leaves=31, min_child_samples=100, subsample=0.8, subsample_freq=1, colsample_bytree=0.8, reg_lambda=5, verbose=-1, objective='huber', alpha=4.0)
SETS = {'old': (C.FEATS, C.FEATS + C.REL_FEATS), 'v2': (C.FEATS2, C.FEATS2 + C.REL_FEATS2)}
rel = lambda d: d[d.n >= C.REL_MIN_RUNS]
use = (te.n >= C.REL_MIN_RUNS).values


def fit(feats, t, v):
    m = lgb.LGBMRegressor(**params); m.fit(t[feats], t.resid, eval_set=[(v[feats], v.resid)], callbacks=[lgb.early_stopping(100, verbose=False)]); return m


def run(train, tag, setname):
    F0, F1 = SETS[setname]
    tr, va = train[train.date < es], train[(train.date >= es) & (train.date < '2026-01-01')]
    m0, m1 = fit(F0, tr, va), fit(F1, rel(tr), rel(va))
    c = m0.predict(te[F0]); c1 = m1.predict(te[F1]); c = np.where(use, c1, c)
    print(f'{tag} {setname}: trees {m0.best_iteration_}/{m1.best_iteration_}', flush=True)
    return te.resid - c, te.f + c


both = pd.concat([conv, page_tr])
res, prj = {'formula': te.resid}, {}
for tag, train in (('page', page_tr), ('conv+page', both)):
    for sn in ('old', 'v2'):
        res[f'{tag} {sn}'], prj[f'{tag} {sn}'] = run(train, tag, sn)
wr = te.groupby(['date', 'vn', 'distance', 'field_size', 'cls'], dropna=False).ngroup()
for k, e in res.items():
    e = pd.Series(np.asarray(e), index=te.index)
    wi = e - e.groupby(wr).transform('mean')
    print(f'{k:20s} RMSE {r(e):.3f} MAE {e.abs().mean():.3f} within-race {r(wi):.3f} 3+runs {r(e[use]):.3f} under3 {r(e[~use]):.3f} bias {e.mean():+.2f} within3 {100*(e.abs()<=3).mean():.1f}%')
# winner test inside stored races
d = te.assign(g=wr, **{('p_' + k): v for k, v in prj.items()}).dropna(subset=['positionFinish'])
d['win'] = (d.positionFinish == 1).astype(int)
kk = d.groupby('g').agg(n=('win', 'size'), w=('win', 'sum')); d = d[d.g.isin(kk[(kk.n >= 4) & (kk.w == 1)].index)]
half = d.date >= d.date.median()
betas = np.arange(0.05, 0.5, 0.025)
def pr(df, col, b):
    z = df[col] * b; z = z - z.groupby(df.g).transform('max'); e = np.exp(z); return e / e.groupby(df.g).transform('sum')
def pr_race(m):
    out = []
    for A, B in ((d[~half], d[half]), (d[half], d[~half])):
        bb = max(betas, key=lambda b: float(np.log(pr(A, m, b)[A.win == 1]).mean()))
        p = pr(B, m, bb); w = B.win == 1; out.append(np.log(p[w]).set_axis(B.g[w]))
    return pd.concat(out)
base = pr_race('p_page old')
print('races', d.g.nunique())
for m in [c for c in d.columns if c.startswith('p_')]:
    x = pr_race(m); dd = x - base
    top = d.loc[d.groupby('g')[m].idxmax()].win.mean()
    print(f'{m:18s} winner LL {x.mean():.4f}  top pick {top:.1%}  vs page old {dd.mean():+.4f} (se {dd.std()/np.sqrt(len(dd)):.4f})')

# price sharpness and gap lines (27 Oct 2026): best softmax beta fitted on all stored races, and winners inside 2 / 4 points of the top, old vs new Proj.
# Stored races hold only some runners, so runner counts are for comparison between the two, not absolute.
print('--- sharpness and lines (same races) ---')
for m in ('p_page old', 'p_conv+page v2'):
    ll = {round(b, 3): float(np.log(pr(d, m, b)[d.win == 1]).mean()) for b in betas}
    bb = max(ll, key=ll.get)
    gap = d.groupby('g')[m].transform('max') - d[m]
    out = [f'{m:16s} best beta {bb:.3f} (LL {ll[bb]:.4f}; at 0.20 {ll[min(ll, key=lambda k: abs(k - 0.2))]:.4f})']
    for k in (2, 4):
        ins = gap <= k
        out.append(f'<={k}pt: runners {ins.groupby(d.g).sum().mean():.2f}, winners {100 * ins[d.win == 1].mean():.1f}%')
    print('  '.join(out), flush=True)
