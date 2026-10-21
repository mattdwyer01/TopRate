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


from scipy.optimize import minimize, minimize_scalar
d["spd"] = 79.15 + 1.33 * pd.to_numeric(d.spd_fig, errors="coerce")
d["nett"] = pd.to_numeric(d.wpr_nett, errors="coerce")
d["proj"] = pd.to_numeric(d.wprp_proj, errors="coerce")
d["nsig"] = d[["spd", "nett", "proj"]].notna().sum(axis=1)
# races where every runner can be scored (>= 2 signals) and the winner is among them; keep races with at least one two-signal runner
d = d.groupby("rk").filter(lambda g: (g.nsig >= 2).all() and len(g) >= 5)
d["pat"] = np.where(d.proj.isna(), "NS", np.where(d.spd.isna() & d.nett.isna(), "P", np.where(d.spd.isna(), "PN", np.where(d.nett.isna(), "PS", "PNS"))))
d = d.groupby("rk").filter(lambda g: (g.pat != "PNS").any())
d["rkid"] = d.rk.astype("category").cat.codes
print(d.rkid.nunique(), "races with at least one two-signal runner;", len(d), "runners")
print(d.pat.value_counts().to_dict())
W = {"proj": 0.5, "nett": 0.3, "spd": 0.2}
def cur(row):
    num = den = 0
    for k, w in W.items():
        if pd.notna(row[k]): num += w * row[k]; den += w
    return num / den
d["cur"] = d.apply(cur, axis=1)
d["cur"] = d.cur - d.groupby("rk").cur.transform("mean")
dates = sorted(d.date.unique()); half = dates[len(dates) // 2]
def nll_scores(s, df):
    s = pd.Series(np.asarray(s), index=df.index)
    m = s.groupby(df.rkid).transform("max")
    lse = np.log(np.exp(s - m).groupby(df.rkid).transform("sum")) + m
    w = df.won == 1
    return -(s - lse)[w].mean()
# A: current weights, scalar beta
def evalA(tr, te):
    b = minimize_scalar(lambda x: nll_scores(x * tr.cur, tr), bounds=(0.001, 3), method="bounded").x
    return -nll_scores(b * te.cur, te), b
# B: pattern-specific weights + intercepts (centre each signal within race by race mean of the signal over runners that have it, so intercepts capture level only)
cols = ["proj", "nett", "spd"]
for k in cols:
    d[k + "_c"] = d[k] - d.groupby("rk")[k].transform("mean")
A, B = d[d.date < half], d[d.date >= half]
pats = ["PNS", "PN", "PS", "NS"]
def design(df):
    X = []
    for p in pats:
        m = (df.pat == p).values
        ks = {"PNS": ["proj", "nett", "spd"], "PN": ["proj", "nett"], "PS": ["proj", "spd"], "NS": ["nett", "spd"]}[p]
        for k in ks:
            X.append(np.where(m, df[k + "_c"].fillna(0).values, 0.0))
        if p != "PNS":
            X.append(m.astype(float))
    return np.column_stack(X)
names = []
for p in pats:
    ks = {"PNS": ["proj", "nett", "spd"], "PN": ["proj", "nett"], "PS": ["proj", "spd"], "NS": ["nett", "spd"]}[p]
    names += [f"{p}:{k}" for k in ks] + ([f"{p}:level"] if p != "PNS" else [])
def fitB(tr):
    X = design(tr)
    w0 = np.zeros(X.shape[1])
    f = lambda w: nll_scores(X @ w, tr) + 0.0005 * (w ** 2).sum()
    return minimize(f, w0 + 0.1, method="L-BFGS-B").x
def evalB(tr, te):
    w = fitB(tr)
    return -nll_scores(design(te) @ w, te), w
res = {}
for nm, (tr, te) in (("A->B", (A, B)), ("B->A", (B, A))):
    la, beta = evalA(tr, te); lb, w = evalB(tr, te)
    res[nm] = (la, lb, w, beta)
    print(f"{nm}: current renormalised weights LL {la:.4f}   pattern-specific fit LL {lb:.4f}   gain {lb-la:+.4f}")
wf = fitB(d)
print("\nfull-sample pattern fit (weights per point of within-race-centred signal, level = log-odds shift for a runner with that pattern):")
for n, v in zip(names, wf): print(f"  {n:12s} {v:+.3f}")
for p in ("PNS", "PN", "PS", "NS"):
    ks = [k for k in names if k.startswith(p + ":") and not k.endswith("level")]
    tot = sum(wf[names.index(k)] for k in ks)
    shares = {k.split(":")[1]: round(wf[names.index(k)] / tot, 3) for k in ks}
    print(f"  {p}: share of weight {shares}, total slope {tot:.3f}")
# diagnostic: runners with only two signals, actual win rate vs softmax-predicted under current weights
tr = d
b = minimize_scalar(lambda x: nll_scores(x * tr.cur, tr), bounds=(0.001, 3), method="bounded").x
s = b * d.cur
d["p"] = np.exp(s - s.groupby(d.rkid).transform("max")); d["p"] = d.p / d.p.groupby(d.rkid).transform("sum")
print("\ncalibration under current weights (predicted vs actual win rate):")
for pat, g in d.groupby("pat"):
    print(f"  {pat:4s} n={len(g):5d}  predicted {g.p.mean():.3%}  actual {g.won.mean():.3%}")
