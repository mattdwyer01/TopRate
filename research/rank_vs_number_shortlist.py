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


SIG = {"Spd": "spd_fig", "Nett": "wpr_nett", "Proj": "wprp_proj"}
for c in SIG.values(): d[c] = pd.to_numeric(d[c], errors="coerce")
d = d.dropna(subset=list(SIG.values()))
d = d[d.groupby("rk").won.transform("size") >= 5].copy()
for k, c in SIG.items():
    g = d.groupby("rk")[c]
    d["z_" + k] = (d[c] - g.transform("mean")) / g.transform("std").replace(0, np.nan)
d = d.dropna(subset=["z_" + k for k in SIG]).copy()
W = {"Proj": .65, "Nett": .25, "Spd": .10}
d["s"] = sum(W[k] * d["z_" + k] for k in W)
# rating points: scale by the race's Proj spread (Proj scale)
d["pstd"] = d.groupby("rk").wprp_proj.transform("std")
d["pts"] = d.s * d.pstd
d["gap"] = d.groupby("rk").pts.transform("max") - d.pts
d["gap_proj"] = d.groupby("rk").wprp_proj.transform("max") - d.wprp_proj
d["rank"] = d.groupby("rk").s.rank(ascending=False, method="first")
n = d.rk.nunique(); print(n, "races")
def row(lab, m):
    t = d[m]; w = t.won.sum()
    print(f"{lab:26s} runners/race {len(t)/n:5.2f}  winners captured {100*w/n:5.1f}%  per runner {100*w/len(t):4.1f}%  ROI {100*((t.won*t.price).sum()/len(t)-1):6.1f}%")
for k in (1,2,3,4,5): row(f"fixed top {k}", d["rank"] <= k)
print()
for g in (1,2,3,4,5,6,8): row(f"blend gap <= {g} pts", d.gap <= g)
print()
for g in (1,2,3,4,5,6,8): row(f"Proj-only gap <= {g}", d.gap_proj <= g)
# matched size: capture of fixed top-k vs gap threshold with same avg size, interpolated
import numpy as np
def cap(m): return d[m].shape[0]/n, 100*d[m].won.sum()/n
print("\nmatched shortlist size (runners/race -> winners captured):")
gs=np.arange(0.25,12,0.25); pts=[cap(d.gap<=g) for g in gs]
ptsp=[cap(d.gap_proj<=g) for g in gs]
for k in (2,3,4):
    sz,c=cap(d["rank"]<=k)
    b=np.interp(sz,[p[0] for p in pts],[p[1] for p in pts]); pj=np.interp(sz,[p[0] for p in ptsp],[p[1] for p in ptsp])
    print(f"size {sz:.2f}: fixed top-{k} {c:.1f}%  blend gap {b:.1f}%  Proj gap {pj:.1f}%")
