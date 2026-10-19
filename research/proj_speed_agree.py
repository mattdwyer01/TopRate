"""Proj #1 and Spd #1 agreement (19 Oct 2026). Live runners.csv 18 Sep onward, SP else last fixed price. Same runner #1 on both, #1 on one only, by price band."""
import numpy as np
import pandas as pd

cols = ["date", "venue", "race", "horse", "spd_fig", "wprp_proj", "scratched", "won", "fixed_win_price", "starting_price_sp", "field_source"]
d = pd.read_csv("runners.csv", low_memory=False, usecols=lambda c: c in cols)
d = d[(d.date >= "2026-09-18") & (d.scratched.fillna(0) != 1) & ~d.field_source.astype(str).str.contains("not in toprate", na=False)]
d["rk"] = d.venue.astype(str) + "|" + d.date + "|" + d.race.astype(str)
d["price"] = pd.to_numeric(d.starting_price_sp, errors="coerce")
d["price"] = d.price.where(d.price > 1, pd.to_numeric(d.fixed_win_price, errors="coerce"))
g = d.groupby("rk")
d = d[(g.won.transform("sum") == 1) & g.won.transform(lambda s: s.notna().all()) & g.price.transform(lambda s: s.notna().all())].copy()
d["won"] = d.won.astype(int)
d["imp"] = (1 / d.price) / d.groupby("rk").price.transform(lambda s: (1 / s).sum())
d = d[d.spd_fig.notna() & d.wprp_proj.notna()]
d = d[d.groupby("rk").spd_fig.transform("size") >= 5]
d["rp"] = d.groupby("rk").wprp_proj.rank(ascending=False, method="first")
d["rs"] = d.groupby("rk").spd_fig.rank(ascending=False, method="first")
print(f"{d.rk.nunique()} races, {len(d)} runners with both Proj and Spd")


def row(s, label):
    n = len(s)
    if n < 20:
        print(f"{label:34s} n={n}")
        return
    w, e, v = s.won.sum(), s.imp.sum(), (s.imp * (1 - s.imp)).sum()
    roi = (s.won * s.price).sum() / n - 1
    big = s[s.won == 1].sort_values("price", ascending=False)
    x3 = s.drop(big.index[:3])
    h = s.sort_values("date")
    a, b = h.iloc[: n // 2], h.iloc[n // 2:]
    r = lambda z: (z.won * z.price).sum() / max(len(z), 1) - 1
    print(f"{label:34s} n={n:4d} wins {w:3d} exp {e:5.1f} ({w / n:5.1%} vs {e / n:5.1%}) z={(w - e) / np.sqrt(v):+5.2f} avg ${s.price.mean():5.2f} ROI {roi:+6.1%} ex3 {r(x3):+6.1%} halves {r(a):+4.0%}/{r(b):+4.0%}")


both = d[(d.rp == 1) & (d.rs == 1)]
pj = d[(d.rp == 1) & (d.rs != 1)]
sp = d[(d.rs == 1) & (d.rp != 1)]
row(both, "Proj #1 AND Spd #1 (same horse)")
row(pj, "Proj #1 only (Spd has another #1)")
row(sp, "Spd #1 only (Proj has another #1)")
row(d[d.rp == 1], "Proj #1 (all)")
row(d[d.rs == 1], "Spd #1 (all)")
print("\nsame horse #1 on both, by price")
for lo, hi in ((0, 2), (2, 3), (3, 4), (4, 6), (6, 10), (10, 1000)):
    row(both[(both.price > lo) & (both.price <= hi)], f"   ${lo}-{hi}")
print("\nProj #1 and Spd top 2 / top 3")
for k in (2, 3):
    row(d[(d.rp == 1) & (d.rs <= k)], f"Proj #1 and Spd top {k}")
    row(d[(d.rs == 1) & (d.rp <= k)], f"Spd #1 and Proj top {k}")
fav = d.groupby("rk").price.min()
print("\nraces where both agree: share", f"{both.rk.nunique() / d.rk.nunique():.1%}", "| agreed #1 is the favourite in",
      f"{(fav.reindex(both.rk).values == both.price.values).mean():.1%}")
