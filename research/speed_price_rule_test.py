"""Spd rank + price rule test (19 Oct 2026): back the #1 Spd rated runner when its price is over $5, and the #2 when over $10.

Sample A (large): results files 2025-07 to 8 Oct 2026 (research/late_speed_study.build(): Spd = EWM halflife 4 of the par v2 figures as of before the race, SP =
priceStarting). Ranked among runners that have a Spd rating, at least 5 rated runners, exactly one winner. Sample B (live): runners.csv spd_fig, 18 Sep onward,
SP else last fixed price (the dashboard's own numbers). Every cell is judged on flat $1 ROI, ROI without the 3 biggest winners, by half and by quarter.
usage: python research/speed_price_rule_test.py
"""
import os
import sys

import numpy as np
import pandas as pd

sys.path.insert(0, os.path.dirname(__file__))


def stats(s, label):
    n = len(s)
    if n == 0:
        print(f"{label:34s} n=0")
        return
    roi = (s.won * s.price).sum() / n - 1
    w = s[s.won == 1].sort_values("price", ascending=False)
    x3 = s.drop(w.index[:3])
    x3roi = (x3.won * x3.price).sum() / len(x3) - 1
    h = s.sort_values("date")
    a, b = h.iloc[: n // 2], h.iloc[n // 2:]
    r = lambda z: (z.won * z.price).sum() / max(len(z), 1) - 1
    q = [r(g) for _, g in h.groupby(pd.qcut(np.arange(n), 4, labels=False))]
    print(f"{label:34s} n={n:5d} win {s.won.mean():5.1%} (mkt {s.imp.mean():5.1%}) avg ${s.price.mean():5.2f} ROI {roi:+6.1%} | ex3 {x3roi:+6.1%} | halves {r(a):+5.0%}/{r(b):+5.0%} | quarters " + "/".join(f"{v:+.0%}" for v in q))


def prep(d, rating):
    d = d[d[rating].notna() & d.price.notna() & (d.price > 1)].copy()
    d["imp"] = 1 / d.price
    g = d.groupby("rk")
    d = d[(g[rating].transform("size") >= 5) & (g.won.transform("sum") == 1)].copy()
    d["imp"] = d.imp / d.groupby("rk").imp.transform("sum")
    d["r"] = d.groupby("rk")[rating].rank(ascending=False, method="first")
    return d


def report(d, title):
    print(f"\n=== {title}: {d.rk.nunique()} races, {len(d)} runners")
    t1, t2 = d[d.r == 1], d[d.r == 2]
    stats(t1, "Spd #1, any price")
    stats(t2, "Spd #2, any price")
    a = t1[t1.price > 5]
    b = t2[t2.price > 10]
    stats(a, "RULE A: Spd #1 over $5")
    stats(b, "RULE B: Spd #2 over $10")
    stats(pd.concat([a, b]), "A + B")
    print("  context (not a chosen cell): #1 by price floor, #2 by price floor")
    for f in (3, 4, 5, 6, 8):
        stats(t1[t1.price > f], f"   #1 over ${f}")
    for f in (5, 8, 10, 12, 15):
        stats(t2[t2.price > f], f"   #2 over ${f}")
    base = d[d.price > 5]
    stats(base, "all runners over $5 (baseline)")
    stats(d[d.price > 10], "all runners over $10 (baseline)")


def main():
    import late_speed_study as ls
    h = ls.build()
    h = h[h.date >= "2025-07-01"].copy()
    h["won"] = (h.positionFinish == 1).astype(int)
    h["price"] = pd.to_numeric(h.priceStarting, errors="coerce")
    h["rk"] = h.race_id
    report(prep(h, "spd"), "A: results files 2025-07 to 8 Oct 2026 (SP)")
    # live window
    cols = ["date", "venue", "race", "horse", "spd_fig", "scratched", "won", "fixed_win_price", "starting_price_sp", "field_source"]
    d = pd.read_csv("runners.csv", low_memory=False, usecols=lambda c: c in cols)
    d = d[(d.date >= "2026-09-18") & (d.scratched.fillna(0) != 1) & ~d.field_source.astype(str).str.contains("not in toprate", na=False)]
    d["rk"] = d.venue.astype(str) + "|" + d.date + "|" + d.race.astype(str)
    d["price"] = pd.to_numeric(d.starting_price_sp, errors="coerce")
    d["price"] = d.price.where(d.price > 1, pd.to_numeric(d.fixed_win_price, errors="coerce"))
    g = d.groupby("rk")
    d = d[(g.won.transform("sum") == 1) & g.won.transform(lambda s: s.notna().all())].copy()
    d["won"] = d.won.astype(int)
    report(prep(d, "spd_fig"), "B: live runners.csv 18 Sep to now (SP else last fixed)")


if __name__ == "__main__":
    main()
