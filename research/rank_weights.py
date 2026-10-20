"""Strike rate, average winning price and ROI for each signal's top picks (19 Oct 2026). Same sample and prep as rating_measures2.py (archive + runners.csv, clean books,
single-winner races, every price known). Rank = mean of the four signal ranks (needs all four here). Run with PYTHONPATH=."""
import numpy as np
import pandas as pd
from datetime import date
import speed_rating as sr

KEY = ["date", "venue", "race", "horse"]
cols = KEY + ["wpr_nett", "wpr_avg_last3", "wprp_proj", "scratched", "won", "placed", "fixed_win_price", "starting_price_sp", "field_source", "spd_fig"]
rd = lambda p: pd.read_csv(p, low_memory=False, usecols=lambda c: c in cols)
leg = pd.concat([rd("archive/toprate/toprate_runners_archive.csv.gz"), rd("archive/toprate/toprate_runners.csv")], ignore_index=True)
cur = pd.concat([rd("runners_archive.csv.gz"), rd("runners.csv")], ignore_index=True)
for x in (leg, cur):
    x["date"] = x["date"].astype(str).str[:10]; x["race"] = x["race"].astype(str)
d = leg.drop_duplicates(KEY, keep="last").set_index(KEY).combine_first(cur.drop_duplicates(KEY, keep="last").set_index(KEY)).reset_index()
d = d[(d.date >= "2026-07-04") & (d.date <= "2026-10-17")]
d = d[(d.scratched.fillna(0) != 1) & ~d.field_source.astype(str).str.contains("not in toprate", na=False)].reset_index(drop=True)
d["spd_fig"] = sr.compute(d, today=date(2026, 8, 1)).where(lambda s: s.notna(), pd.to_numeric(d.spd_fig, errors="coerce"))
d["rk"] = d.venue.astype(str) + "|" + d.date + "|" + d.race
d["price"] = pd.to_numeric(d.starting_price_sp, errors="coerce")
d["price"] = d.price.where(d.price > 1, pd.to_numeric(d.fixed_win_price, errors="coerce"))
g = d.groupby("rk")
d = d[(g.won.transform("sum") == 1) & g.won.transform(lambda s: s.notna().all()) & g.price.transform(lambda s: s.notna().all())].copy()
d["won"] = d.won.astype(int)
d["book"] = d.groupby("rk").price.transform(lambda s: (1 / s).sum())
d = d[(d.book >= 1.05) & (d.book <= 2.0)]

SIG = {"Spd": "spd_fig", "Nett": "wpr_nett", "L3": "wpr_avg_last3", "Proj": "wprp_proj"}
from scipy.optimize import minimize
for c in SIG.values():
    d[c] = pd.to_numeric(d[c], errors="coerce")
d = d.dropna(subset=list(SIG.values()))
d = d[d.groupby("rk").won.transform("size") >= 5].copy()
names = list(SIG)
for k, c in SIG.items():
    g = d.groupby("rk")[c]
    d["z_" + k] = (d[c] - g.transform("mean")) / g.transform("std").replace(0, np.nan)
    d["r_" + k] = g.rank(ascending=False, method="min")
d = d.dropna(subset=["z_" + k for k in names]).copy()
d["rkid"] = d.rk.astype("category").cat.codes
print(len(d.rkid.unique()), "races")
def nll(w, df, cols):
    s = df[cols].values @ w
    df = df.assign(s=s)
    m = df.groupby("rkid").s.transform("max")
    e = np.exp(df.s - m)
    lse = np.log(e.groupby(df.rkid).transform("sum")) + m
    return -(df.s - lse)[df.won == 1].sum() / df[df.won == 1].shape[0]
def ll_pick(w, df, cols):
    df = df.assign(s=df[cols].values @ w)
    top = df.loc[df.groupby("rkid").s.idxmax()]
    return -nll(w, df.assign(s=0), cols) if False else None
def score(w, df, cols):
    s = df[cols].values @ w
    df = df.assign(s=s)
    top = df.loc[df.groupby("rkid").s.idxmax()]
    return -nll(w, df, cols), top.won.mean() * 100
zc = ["z_" + k for k in names]
dates = sorted(d.date.unique()); half = dates[len(dates)//2]
A, B = d[d.date < half], d[d.date >= half]
def fit(df, cols):
    r = minimize(nll, np.full(len(cols), 0.2), args=(df, cols), method="L-BFGS-B")
    return r.x
res = {}
def evalset(label, cols, fixedw=None):
    out = []
    for tr, te in ((A, B), (B, A)):
        w = fixedw if fixedw is not None else fit(tr, cols)
        out.append(score(w, te, cols))
    ll = np.mean([o[0] for o in out]); st = np.mean([o[1] for o in out])
    print(f"{label:28s} LL {ll:.4f}  top-pick {st:.1f}%", "" if fixedw is not None else "w(full)=" + str(np.round(fit(d, cols), 3)))
evalset("equal z-score (4)", zc, np.full(4, 0.5))
evalset("fitted 4", zc)
evalset("fitted no L3", ["z_Spd","z_Nett","z_Proj"])
evalset("fitted Proj+Spd", ["z_Spd","z_Proj"])
evalset("fitted Nett+Spd", ["z_Spd","z_Nett"])
for k in names: evalset("single " + k, ["z_" + k])
# rank-mean variants
for lab, ks in (("rank-mean 4", names), ("rank-mean no L3", ["Spd","Nett","Proj"]), ("rank-mean Proj+Spd", ["Spd","Proj"])):
    d["m"] = d[["r_"+k for k in ks]].mean(axis=1)
    d["m"] = d.groupby("rk").m.rank(method="min")
    t = d[d.m == 1]
    print(f"{lab:28s} #1 picks {len(t)} strike {100*t.won.sum()/d.rkid.nunique():.1f}% per race, per pick {100*t.won.mean():.1f}%")
print("corr of z signals:"); print(d[zc].corr().round(2))
