"""Live check of the Spd rating on races already run in runners.csv (17 Oct 2026 onward by default).

spd_fig is stored as lengths vs par (higher = faster), computed from runs BEFORE the race, so values are pre-race even for backfilled rows.
Per race: rank runners on Spd (and Nett, Proj for comparison), then win rate, strike vs the market-implied rate, and flat $1 win ROI at
the starting price (else last fixed price) for the top 1 / top 2 / top 3.
usage: python research/speed_live_check.py [from_date] [to_date]
"""
import sys
import numpy as np
import pandas as pd

lo = sys.argv[1] if len(sys.argv) > 1 else "2026-10-17"
hi = sys.argv[2] if len(sys.argv) > 2 else "2099-01-01"
cols = ["date", "venue", "race", "horse", "spd_fig", "wpr_nett", "wprp_proj", "scratched", "won", "finish_position", "fixed_win_price",
        "starting_price_sp", "field_source"]
d = pd.read_csv("runners.csv", low_memory=False, usecols=lambda c: c in cols)
d = d[(d.date >= lo) & (d.date <= hi)]
d = d[(d.scratched.fillna(0) != 1) & ~d.field_source.astype(str).str.contains("not in toprate", na=False)]
d["rk"] = d.venue.astype(str) + "|" + d.date + "|" + d.race.astype(str)
d["price"] = pd.to_numeric(d.starting_price_sp, errors="coerce")
d["price"] = d.price.where(d.price > 1, pd.to_numeric(d.fixed_win_price, errors="coerce"))
# a race counts once it has a winner recorded and every runner has an outcome
g = d.groupby("rk")
ok = g.won.transform("sum") == 1
ok &= g.won.transform(lambda s: s.notna().all())
d = d[ok].copy()
d = d[d.groupby("rk").price.transform(lambda s: s.notna().all())]
d["won"] = d.won.astype(float)
d["imp"] = 1 / d.price
d["imp"] = d.imp / d.groupby("rk").imp.transform("sum")
print(f"{d.rk.nunique()} races, {len(d)} runners, {lo} to {d.date.max()}")


def show(name, col, higher=True):
    x = d[d[col].notna()].copy()
    x = x[x.groupby("rk")[col].transform("size") >= 4]
    x["r"] = x.groupby("rk")[col].rank(ascending=not higher, method="first")
    n = x.rk.nunique()
    out = []
    for k in (1, 2, 3):
        s = x[x.r <= k]
        roi = (s.won * s.price).sum() / len(s) - 1
        out.append(f"top{k}: win {s.won.mean():.1%} (mkt {s.imp.mean():.1%}) avg ${s.price.mean():.2f} roi {roi:+.1%} n={len(s)}")
    # winner in top k share
    w = x[x.won == 1]
    print(f"{name:6s} races={n} | " + " | ".join(out) + f" | winner in top3 {(w.r <= 3).mean():.1%}")


for nm, c in (("Spd", "spd_fig"), ("Nett", "wpr_nett"), ("Proj", "wprp_proj")):
    show(nm, c)
fav = d.copy()
fav["r"] = fav.groupby("rk").price.rank(method="first")
s = fav[fav.r == 1]
print(f"Fav    win {s.won.mean():.1%} roi {(s.won * s.price).sum() / len(s) - 1:+.1%} n={len(s)}")
# Spd rank 1 or 2 that also look like value: price above the field's model-free fair (market) is not testable; show by price band
x = d[d.spd_fig.notna()].copy()
x = x[x.groupby("rk").spd_fig.transform("size") >= 4]
x["r"] = x.groupby("rk").spd_fig.rank(ascending=False, method="first")
t = x[x.r <= 2].copy()
t["band"] = pd.cut(t.price, [0, 3, 5, 8, 15, 1000])
print(t.groupby("band", observed=True).apply(lambda s: pd.Series({"n": len(s), "win": s.won.mean(), "mkt": s.imp.mean(), "roi": (s.won * s.price).sum() / len(s) - 1})).round(3).to_string())

# robustness of Spd top1 / top2: by day, and without the biggest winners
for k in (1, 2):
    s = x[x.r <= k]
    print(f"\nSpd top{k}: by day")
    print(s.groupby("date").apply(lambda z: pd.Series({"n": len(z), "win": z.won.mean(), "roi": (z.won * z.price).sum() / len(z) - 1})).round(3).to_string())
    w = s[s.won == 1].sort_values("price", ascending=False)
    for ex in (1, 3):
        z = s.drop(w.index[:ex])
        print(f"  excluding {ex} biggest winners (${', $'.join(f'{p:.1f}' for p in w.price[:ex])}): roi {(z.won * z.price).sum() / len(z) - 1:+.1%}")
