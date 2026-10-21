"""Race-level selection from the market's structure: does a Spd box (or the market's own box) do better in some kinds of races, when the race is open (high
entropy, weak favourite, dear market first four)? Uses the cache written by speed_exotics_select.py (R_CACHE.csv, with market structure columns).
usage: PYTHONPATH=.:research python research/speed_exotics_open.py R_CACHE.csv
"""
import sys

import numpy as np
import pandas as pd

import speed_exotics_select as SEL

R = pd.read_csv(sys.argv[1])
P = SEL.dividend_pairs()
fit = SEL.fit_div(P)
R["ed3"] = SEL.est_div(R.h3, R.field, fit["Trifecta"])
R["ed4"] = SEL.est_div(R.h4, R.field, fit["FirstFour"])
R["train"] = R.date < "2026-02-01"
rng = np.random.default_rng(1)
POOLS = [("s5 tri", "s5_tri", "ed3", 60, "s5_itri"), ("s5 ff", "s5_ff", "ed4", 120, "s5_iff"), ("s6 ff", "s6_ff", "ed4", 360, "s6_iff"),
         ("m5 ff", "m5_ff", "ed4", 120, "m5_iff"), ("m6 ff", "m6_ff", "ed4", 360, "m6_iff")]


def stat(g, hit, ed, cost, ic):
    ret = (g[hit] * g[ed]).values
    roi = ret.sum() / (cost * len(g)) - 1
    bs = [ret[rng.integers(0, len(g), len(g))].sum() / (cost * len(g)) - 1 for _ in range(400)]
    a, b = g[g.train], g[~g.train]
    r1 = (a[hit] * a[ed]).sum() / (cost * len(a)) - 1
    r2 = (b[hit] * b[ed]).sum() / (cost * len(b)) - 1
    return f"n {len(g):5d} hit {g[hit].mean()*100:5.1f}% x{g[hit].sum()/g[ic].sum():.2f} est {roi*100:+4.0f}% [{np.percentile(bs,5)*100:+.0f},{np.percentile(bs,95)*100:+.0f}] halves {r1*100:+.0f}/{r2*100:+.0f}"


for feat, labs in (("m_ent", "entropy (1 = wide open)"), ("m_top1", "favourite win chance"), ("m_open4", "log dividend of the market's own first four (dear = open)")):
    R["q"] = pd.qcut(R[feat], 5, labels=False)
    print(f"\n== quintiles of {labs}; 0 = lowest ==")
    for name, hit, ed, cost, ic in POOLS:
        print(f"-- {name}")
        for q, g in R.groupby("q"):
            print(f"   Q{q}: {stat(g, hit, ed, cost, ic)}")
# a rule fitted on train: open races only, both fields large
R["open"] = (R.m_ent > R.m_ent.quantile(0.6)) & (R.field >= 10)
print("\n== open races (entropy above the 60th percentile, field 10+) ==")
for name, hit, ed, cost, ic in POOLS:
    print(f"{name}: {stat(R[R.open], hit, ed, cost, ic)}")
