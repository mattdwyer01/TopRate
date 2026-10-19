"""Where does a signal's win rate beat the market-implied rate? (19 Oct 2026) Live runners.csv 18 Sep onward, SP else last fixed price, implied = 1/price
normalised within the race. For Spd, Nett, Proj (rank 1, 2, 3 and top 3) and by price band: wins, expected wins, z = (wins - expected) / sd, flat ROI."""
import numpy as np
import pandas as pd

cols = ["date", "venue", "race", "horse", "spd_fig", "wpr_nett", "wprp_proj", "scratched", "won", "fixed_win_price", "starting_price_sp", "field_source"]
d = pd.read_csv("runners.csv", low_memory=False, usecols=lambda c: c in cols)
d = d[(d.date >= "2026-09-18") & (d.scratched.fillna(0) != 1) & ~d.field_source.astype(str).str.contains("not in toprate", na=False)]
d["rk"] = d.venue.astype(str) + "|" + d.date + "|" + d.race.astype(str)
d["price"] = pd.to_numeric(d.starting_price_sp, errors="coerce")
d["price"] = d.price.where(d.price > 1, pd.to_numeric(d.fixed_win_price, errors="coerce"))
g = d.groupby("rk")
d = d[(g.won.transform("sum") == 1) & g.won.transform(lambda s: s.notna().all()) & g.price.transform(lambda s: s.notna().all())].copy()
d["won"] = d.won.astype(int)
d["imp"] = (1 / d.price) / d.groupby("rk").apply(lambda x: (1 / x.price).sum()).reindex(d.rk).values
print(f"{d.rk.nunique()} races, {len(d)} runners")


def row(s, label):
    n = len(s)
    if n < 30:
        return
    w, e, v = s.won.sum(), s.imp.sum(), (s.imp * (1 - s.imp)).sum()
    roi = (s.won * s.price).sum() / n - 1
    print(f"{label:30s} n={n:5d} wins {w:4d} expected {e:6.1f} ({w / n:5.1%} vs {e / n:5.1%}) z={(w - e) / np.sqrt(v):+5.2f} ROI {roi:+6.1%}")


for nm, c in (("Spd", "spd_fig"), ("Nett", "wpr_nett"), ("Proj", "wprp_proj")):
    x = d[d[c].notna()].copy()
    x = x[x.groupby("rk")[c].transform("size") >= 5]
    x["r"] = x.groupby("rk")[c].rank(ascending=False, method="first")
    for k in (1, 2, 3):
        row(x[x.r == k], f"{nm} #{k}")
    row(x[x.r <= 3], f"{nm} top 3")
    t = x[x.r == 1]
    for lo, hi in ((0, 2.5), (2.5, 4), (4, 6), (6, 10), (10, 1000)):
        row(t[(t.price > lo) & (t.price <= hi)], f"   {nm} #1 ${lo}-{hi}")
