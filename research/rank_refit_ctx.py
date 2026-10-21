"""Refit of the Rank blend weights against the live Proj (formula + context correction), 22 Oct 2026. Uses the saved sample from
research/proj_context_test.py (319 races 4 Jul to 17 Oct with >= 80% formula coverage, context Proj rebuilt as of each race, Nett, Spd as then computed,
clean books, SP). Run proj_context_test.py first to make the pickle (path below), then PYTHONPATH=. python research/rank_refit_ctx.py."""
import numpy as np, pandas as pd
from scipy.optimize import minimize
import sys
P = sys.argv[1] if len(sys.argv) > 1 else "pc.pkl"
out = pd.read_pickle(P)
cols = ["z_context", "z_nett", "z_spd"]
def nll(w, X, won, rid):
    s = X @ w; m = pd.Series(s).groupby(rid).transform("max").values; e = np.exp(s - m)
    lse = np.log(pd.Series(e).groupby(rid).transform("sum").values) + m
    return -(s - lse)[won == 1].mean()
def ev(df, w):
    t = df.assign(s=df[cols].values @ w); m = t.groupby("rkid").s.transform("max"); e = np.exp(t.s - m)
    lse = np.log(e.groupby(t.rkid).transform("sum")) + m
    return (t.s - lse)[t.won == 1].mean(), t.loc[t.groupby("rkid").s.idxmax()].won.mean() * 100
def fit(df, c=cols):
    return minimize(nll, np.full(len(c), .2), args=(df[c].values, df.won.values, df.rkid.values), method="L-BFGS-B").x
print(len(out.rk.unique()), "races")
w = fit(out); print("full-sample fitted weights", np.round(w, 3), "share", np.round(w / w.sum(), 3))
dates = sorted(out.date.unique()); half = dates[len(dates) // 2]
A, B = out[out.date < half], out[out.date >= half]
for lab, ww in (("shipped .65/.25/.10", np.array([.65, .25, .10])), ("proj only", np.array([1., 0, 0])), ("fitted cross", None),
                ("0.80/.15/.05", np.array([.8, .15, .05])), ("0.50/.35/.15", np.array([.5, .35, .15])), ("0.55/.30/.15", np.array([.55, .30, .15]))):
    r = []
    for tr, te in ((A, B), (B, A)):
        r.append(ev(te, fit(tr) / fit(tr).sum() * 1.0 if ww is None else ww))
    print(f"{lab:22s} LL {np.mean([x[0] for x in r]):.4f} top1 {np.mean([x[1] for x in r]):.1f}%")
rng = np.random.default_rng(0); ids = out.rkid.unique(); sh = []
for _ in range(200):
    pick = rng.choice(ids, len(ids)); b = pd.concat([out[out.rkid == i].assign(rkid=j) for j, i in enumerate(pick)])
    ww = fit(b); sh.append(ww / ww.sum())
sh = np.array(sh); print("bootstrap share 5/50/95%:"); print(np.round(np.percentile(sh, [5, 50, 95], axis=0), 3))
