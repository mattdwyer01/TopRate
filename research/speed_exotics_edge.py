"""Does a Spd pool beat the market at the same cost? For every race the chance the starting-price market (Harville on normalised SP) gives the exact set of
boxed combinations, against how often the box actually hit. ratio = actual hits / market-implied hits (1.0 = priced fairly, before the takeout). The
control is the market's own top-N pool (same size, same cost). A Spd pool is only interesting where its ratio beats the market pool's, and best of all in
the cases where the boxed runners are not all market-top-N (that is where the dividends are bigger).
usage: PYTHONPATH=. python research/speed_exotics_edge.py SPD_RACES.csv.gz
"""
import sys
from itertools import permutations

import numpy as np
import pandas as pd

from speed_exotics_nuggets import load

PTS = 1.33


def implied(p, pool, k):
    """Harville probability that the first k home are all in pool and the order is anything (sum over ordered k-tuples drawn from pool)."""
    tot = 0.0
    for o in permutations(pool, k):
        left, pr = 1.0, 1.0
        for i in o:
            pr *= p[i] / left
            left -= p[i]
        tot += pr
    return tot


def race(g):
    g = g.dropna(subset=["pos"])
    top = g[g.pos.between(1, 4)]
    if len(g) < 6 or sorted(top.pos.tolist()) != [1, 2, 3, 4]:
        return None
    if not (np.isfinite(g.sp).all() and (g.sp > 1).all()) or g.pts.notna().sum() < 6:
        return None
    sp = g.sp.values
    book = (1 / sp).sum()
    if not 1.05 <= book <= 2.0:
        return None
    p = (1 / sp) / book
    pos = g.pos.values
    pts = np.nan_to_num(g.pts.values, nan=-1e9)
    spd_o = list(np.argsort(-pts, kind="stable"))
    mkt_o = list(np.argsort(sp, kind="stable"))
    r = dict(date=g.date.iloc[0], field=len(g), n_rated=int(g.pts.notna().sum()), dist=g.distance.iloc[0], cls=str(g.race_class.iloc[0]),
             fav=sp.min(), gap5=(pts[spd_o[4]] - pts[spd_o[5]]), spread5=(pts[spd_o[0]] - pts[spd_o[4]]), lead=pts[spd_o[0]] - pts[spd_o[1]])
    for N in (4, 5, 6):
        for who, o in (("s", spd_o), ("m", mkt_o)):
            pool = o[:N]
            inn = pos[pool]
            r[f"{who}{N}_tri"] = int((inn <= 3).sum() == 3)
            r[f"{who}{N}_ff"] = int((inn <= 4).sum() == 4)
            r[f"{who}{N}_itri"] = implied(p, pool, 3)
            if N >= 5:
                r[f"{who}{N}_iff"] = implied(p, pool, 4)
    r["s5_out"] = len(set(spd_o[:5]) - set(mkt_o[:5]))
    r["s6_out"] = len(set(spd_o[:6]) - set(mkt_o[:6]))
    r["s5_avgsp"] = float(np.mean(sp[spd_o[:5]]))
    return r


def row(g, col, icol):
    h, i = g[col].values, g[icol].values
    z = (h.sum() - i.sum()) / np.sqrt((i * (1 - i)).sum())
    return f"{len(g):5d} hit {h.mean()*100:5.1f}% market {i.mean()*100:5.1f}% ratio {h.sum()/i.sum():.2f} z{z:+.1f}"


def main(path):
    d = load(path)
    rows = [race(g) for _, g in d.groupby("race_id", sort=False)]
    R = pd.DataFrame([x for x in rows if x])
    print(f"{len(R):,} races (clean 1-4, every runner priced, SP book 1.05-2.0, at least 6 Spd rated), {R.date.min()} to {R.date.max()}")
    print("\n== all races: Spd pool vs the market's own pool of the same size (same cost) ==")
    for N, kind in ((4, "tri"), (5, "tri"), (6, "tri"), (5, "ff"), (6, "ff")):
        ic = "itri" if kind == "tri" else "iff"
        print(f"top {N} {kind}:  Spd  {row(R, f's{N}_{kind}', f's{N}_{ic}')}\n             mkt  {row(R, f'm{N}_{kind}', f'm{N}_{ic}')}")
    R["train"] = R.date < "2026-02-01"
    R["fb"] = pd.cut(R.field, [0, 7, 9, 11, 13, 30], labels=["<=7", "8-9", "10-11", "12-13", "14+"])
    R["gap5b"] = pd.cut(R.gap5, [-1, 1, 2, 3, 5, 100], labels=["<1", "1-2", "2-3", "3-5", "5+"])
    R["favb"] = pd.cut(R.fav, [0, 2.5, 3.5, 5, 100], labels=["<2.5", "2.5-3.5", "3.5-5", "5+"])
    R["outb"] = R.s5_out.clip(upper=3)
    R["out6b"] = R.s6_out.clip(upper=3)
    R["clsg"] = R.cls.str.extract(r"^([A-Za-z]+)")[0].str.lower().fillna("?")
    R["unr"] = (R.field - R.n_rated).clip(upper=2)
    for N, kind, slices in ((5, "tri", ("fb", "gap5b", "favb", "outb", "clsg", "unr")), (5, "ff", ("fb", "gap5b", "favb", "outb", "clsg", "unr")),
                            (6, "ff", ("fb", "favb", "out6b", "clsg")), (6, "tri", ("fb", "favb", "out6b"))):
        ic = "itri" if kind == "tri" else "iff"
        print(f"\n######## top {N} {kind}: Spd actual/market-implied, TRAIN (to Jan 2026) | TEST (Feb 2026 on)  [market pool ratio on the TEST rows in brackets] ########")
        for col in slices:
            print(f"-- {col}")
            for lv, g in R.groupby(col, observed=True):
                tr, te = g[g.train], g[~g.train]
                if len(g) < 200 or len(te) < 80:
                    continue
                m = te[f"m{N}_{kind}"].sum() / te[f"m{N}_{ic}"].sum()
                print(f"   {str(lv):8s} TRAIN {row(tr, f's{N}_{kind}', f's{N}_{ic}')}  | TEST {row(te, f's{N}_{kind}', f's{N}_{ic}')} (mkt {m:.2f})")
    return R


if __name__ == "__main__":
    main(sys.argv[1])
