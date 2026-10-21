"""Which races to play for a Spd boxed trifecta / first four. Step 1: a dividend model, log(actual TAB dividend) on log(1 / Harville probability of the actual
result from the starting-price market), fitted on the real dividends (tab_dividends.csv, 2 to 21 Oct 2026) and checked split-half. Step 2: apply it to the
2025-07 to 8 Oct 2026 races to get an estimated return per race for each box (hit x modelled dividend), and search race-selection rules (single and pairs of
pre-race conditions) on 2025-07..2026-01, then check the survivors on 2026-02+ and on the real dividends. The dividend model is an approximation: a rule's
estimated ROI is a screen, the real dividend ledger is the proof.
usage: PYTHONPATH=.:research python research/speed_exotics_select.py SPD_RACES.csv.gz [R_CACHE.csv]
"""
import os
import sys
from itertools import combinations
from math import perm

import numpy as np
import pandas as pd

import speed_exotics_edge as E
from speed_exotics_nuggets import harville, load, real_boxes


def dividend_pairs():
    import runners_io
    r = runners_io.read_runners()
    r = r[(r.date.astype(str) >= "2026-10-02") & (r.scratched.fillna(0) == 0)].copy()
    r["v"] = r.venue.astype(str).str.upper()
    r["sp"] = pd.to_numeric(r.starting_price_sp, errors="coerce").fillna(pd.to_numeric(r.fixed_win_price, errors="coerce"))
    dv = pd.read_csv("tab_dividends.csv")
    dv = dv[dv["product"].isin(["Trifecta", "FirstFour"]) & (dv.status == "Paying")].drop_duplicates(["date", "venue", "race_no", "product"])
    out = []
    for (dt, ven, rn), g in r.groupby([r.date.astype(str), "v", "race"]):
        sub = dv[(dv.date == dt) & (dv.venue.str.split(" @ ").str[0] == ven) & (dv.race_no == rn)]
        if sub.empty or g.sp.isna().any() or (g.sp <= 1).any() or g.tab_number.isna().any():
            continue
        book = (1 / g.sp.values).sum()
        if not 1.05 <= book <= 2.0:
            continue
        p = (1 / g.sp.values) / book
        idx = {int(t): i for i, t in enumerate(g.tab_number.values)}
        for _, row in sub.iterrows():
            sel = [int(x) for x in str(row.selections).split("/")]
            if any(s not in idx for s in sel):
                continue
            h = harville(p, [idx[s] for s in sel])
            if h and h > 0 and row.amount > 0:
                out.append(dict(date=dt, field=len(g), product=row["product"], lh=np.log(1 / h), ld=np.log(row.amount)))
    return pd.DataFrame(out)


def fit_div(P):
    """{product: (a, b, resid_sd)} with log div = a + b * log(1/h)."""
    res = {}
    for prod, g in P.groupby("product"):
        A = np.c_[np.ones(len(g)), g.lh, np.log(g.field)]
        coef, *_ = np.linalg.lstsq(A, g.ld, rcond=None)
        sd = np.std(g.ld - A @ coef)
        res[prod] = (coef[0], coef[1], sd, len(g), coef[2])
    return res


def split_half(P):
    days = sorted(P.date.unique())
    first, second = P[P.date.isin(days[: len(days) // 2])], P[P.date.isin(days[len(days) // 2:])]
    for prod in ("Trifecta", "FirstFour"):
        a, b, sd, _, c = fit_div(first[first["product"] == prod])[prod]
        g = second[second["product"] == prod]
        pred = a + b * g.lh + c * np.log(g.field)
        ss = ((g.ld - pred) ** 2).sum()
        base = ((g.ld - g.ld.mean()) ** 2).sum()
        print(f"  {prod}: fit on first half a={a:.2f} b={b:.2f}, second half out-of-sample R2 {1 - ss / base:.2f}, mean est/actual dividend "
              f"{np.exp(pred + sd ** 2 / 2).mean() / np.exp(g.ld).mean():.2f}")


def est_div(h, field, model):
    a, b, sd, _, c = model
    return np.exp(a + b * np.log(1 / h) + c * np.log(field) + sd ** 2 / 2)


def main(path, cache=None):
    P = dividend_pairs()
    fit = fit_div(P)
    print("dividend model (log div = a + b log(1/h) + c log(field)):", {k: tuple(round(x, 2) for x in v) for k, v in fit.items()})
    split_half(P)
    if cache and os.path.exists(cache):
        R = pd.read_csv(cache)
    else:
        d = load(path)
        R = pd.DataFrame([x for x in (E.race(g) for _, g in d.groupby("race_id", sort=False)) if x])
        if cache:
            R.to_csv(cache, index=False)
    R["train"] = R.date < "2026-02-01"
    R["ed3"] = est_div(R.h3, R.field, fit["Trifecta"])
    R["ed4"] = est_div(R.h4, R.field, fit["FirstFour"])
    R["unr"] = (R.field - R.n_rated).clip(upper=3)
    R["fb"] = pd.cut(R.field, [0, 7, 9, 11, 13, 30], labels=["<=7", "8-9", "10-11", "12-13", "14+"]).astype(str)
    R["gap5b"] = pd.cut(R.gap5, [-1, 2, 5, 100], labels=["<2", "2-5", "5+"]).astype(str)
    R["spreadb"] = pd.cut(R.spread5, [-1, 4, 8, 1000], labels=["<4", "4-8", "8+"]).astype(str)
    R["favb"] = pd.cut(R.fav, [0, 2.5, 3.5, 100], labels=["<2.5", "2.5-3.5", "3.5+"]).astype(str)
    R["leadb"] = pd.cut(R.lead, [-1, 1, 3, 1000], labels=["<1", "1-3", "3+"]).astype(str)
    R["out6"] = R.s6_out.clip(upper=3).astype(str)
    R["out5"] = R.s5_out.clip(upper=3).astype(str)
    R["distb"] = pd.cut(R.dist, [0, 1300, 1700, 9999], labels=["sprint", "mile", "staying"]).astype(str)
    R["clsg"] = R.cls.str.extract(r"^([A-Za-z]+)")[0].str.lower().fillna("?").replace({"rst": "restricted", "r": "restricted"}).astype(str)
    R["unr"] = R.unr.astype(str)
    feats = ["unr", "fb", "gap5b", "spreadb", "favb", "leadb", "out5", "out6", "distb", "clsg"]
    pools = {"s5 tri": ("s5_tri", "ed3", 60), "s6 tri": ("s6_tri", "ed3", 120), "s5 ff": ("s5_ff", "ed4", 120), "s6 ff": ("s6_ff", "ed4", 360)}

    def roi(g, hit, ed, cost):
        if len(g) == 0:
            return np.nan, 0
        return (g[hit] * g[ed]).sum() / (cost * len(g)) - 1, len(g)

    print("\nall races, estimated ROI (train | test):")
    for name, (hit, ed, cost) in pools.items():
        print(f"  {name}: {roi(R[R.train], hit, ed, cost)[0]*100:+.0f}% | {roi(R[~R.train], hit, ed, cost)[0]*100:+.0f}%")

    rules = [((f,), {f: v}) for f in feats for v in R[f].unique()]
    rules += [((f1, f2), {f1: v1, f2: v2}) for f1, f2 in combinations(feats, 2) for v1 in R[f1].unique() for v2 in R[f2].unique()]
    print(f"\nrule search: {len(rules)} rules x {len(pools)} boxes on the train period (min 250 races), keep est ROI > +15% (train), then the test period")
    keep = []
    tried = 0
    for _, cond in rules:
        m = np.ones(len(R), bool)
        for f, v in cond.items():
            m &= (R[f] == v).values
        g = R[m]
        gt = g[g.train]
        if len(gt) < 250:
            continue
        for name, (hit, ed, cost) in pools.items():
            tried += 1
            rt, nt = roi(gt, hit, ed, cost)
            if rt > 0.15:
                rs, ns = roi(g[~g.train], hit, ed, cost)
                if ns >= 120:
                    keep.append((name, cond, nt, rt, ns, rs, g[g.train][hit].mean(), g[~g.train][hit].mean()))
    print(f"{tried} rule x box tests, {len(keep)} cleared +15% on train")
    keep.sort(key=lambda x: -x[5])
    pos = [k for k in keep if k[5] > 0]
    print(f"{len(pos)} of those are still positive on the test period; top 25 by test ROI:")
    for name, cond, nt, rt, ns, rs, ht, hs in keep[:25]:
        print(f"  {name:7s} {str(cond):55s} train n={nt:5d} est {rt*100:+5.0f}% hit {ht*100:4.1f}% | test n={ns:5d} est {rs*100:+5.0f}% hit {hs*100:4.1f}%")
    avg_test = np.mean([k[5] for k in keep]) if keep else float("nan")
    print(f"mean test ROI of train winners {avg_test*100:+.0f}% (a rule found by looking should drop back toward the all-race figure)")
    return R, keep


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2] if len(sys.argv) > 2 else None)
