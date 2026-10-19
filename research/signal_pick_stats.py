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
for c in SIG.values():
    d[c] = pd.to_numeric(d[c], errors="coerce")
d = d.dropna(subset=list(SIG.values()))
d = d[d.groupby("rk").won.transform("size") >= 5].copy()
d["imp"] = (1 / d.price) / d.book
nR = d.rk.nunique()
print(f"{nR} races, {len(d)} runners, {d.date.min()} to {d.date.max()}\n")
for k, c in SIG.items():
    d["r_" + k] = d.groupby("rk")[c].rank(ascending=False, method="min")
d["r_Rank"] = d[["r_" + k for k in SIG]].mean(axis=1)
d["r_Rank"] = d.groupby("rk").r_Rank.rank(method="min")
d["r_Market"] = d.groupby("rk").price.rank(method="min")
has_pl = d.placed.notna().all()


def row(name, sel):
    s = d[sel]
    n = len(s)
    w = s[s.won == 1]
    ret = (s.won * s.price).sum() / n - 1
    ex3 = s.assign(p=s.won * s.price).sort_values("p", ascending=False).iloc[3:]
    return dict(pick=name, picks=n, winners=len(w), strike=100 * len(w) / n, implied=100 * s.imp.mean(), avg_price=s.price.mean(),
                avg_win_price=w.price.mean() if len(w) else np.nan, median_win_price=w.price.median() if len(w) else np.nan,
                place=100 * (s.placed.fillna(0) > 0).mean() if has_pl else np.nan, roi=100 * ret, roi_ex3=100 * ((ex3.won * ex3.price).sum() / len(ex3) - 1))


rows = []
for k in ["Market", "Rank", "Proj", "L3", "Nett", "Spd"]:
    for rnk in (1, 2, 3):
        rows.append(row(f"{k} #{rnk}" if k != "Market" else f"Favourite #{rnk}", d["r_" + k] == rnk) if True else None)
out = pd.DataFrame(rows)
pd.set_option("display.width", 200)
print(out.round(1).to_string(index=False))
print("\nrandom runner: strike %.1f%%, avg field %.1f" % (100 / (len(d) / nR), len(d) / nR))
print("\nagree: Market #1 also Rank #1 / Proj #1 / Spd #1 (share of races where that signal's #1 is the favourite)")
for k in ("Rank", "Proj", "L3", "Nett", "Spd"):
    a = d[(d.r_Market == 1) & (d["r_" + k] == 1)].rk.nunique()
    print(f"  {k}: {100 * a / nR:.1f}%")
