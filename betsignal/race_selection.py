"""Race selection test (14 Oct 2026, read-only research script).

Question (user): "I look for value in races and don't bet where it is too difficult. We won't find a model that is profitable in every race."
So: are there kinds of races, knowable before the jump, where the model reads the race better than the market does, and does that give value bets?

Model: walk-forward race-level conditional logit (fitted on years before the test year), on clean-book races only (SP book 1.05 to 1.5):
  p_cal  calibrated market only (one slope on log price)
  p_mod  calibrated market + rating form + sire (the only source that added anything in betsignal/newinfo.py)
Race edge  delta = log p_mod(winner) - log p_cal(winner): how much better the model called the winner than the calibrated market.
Segments are pre-race descriptors only (field size, class, distance, wet/dry, readable share of field, first starter, favourite price).

Part A: delta and the EV > 1.05 bets by segment, 2021 to 2026 pooled (descriptive; slicing finds false positives, read with care).
Part B (the honest test): for each test year, pick the segments whose delta had t >= 2 using ONLY earlier years, then measure the picked
segments in the test year. Part C: the same with a stricter rule (two or more segments must agree).

  python betsignal/newinfo.py --build   (needs /tmp/tune_cache/feat.pkl from own_ratings/tune.py --prep and newinfo.pkl)
  python betsignal/race_selection.py
"""
import os
import sys

import numpy as np
import pandas as pd

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from betsignal.newinfo import BASE_COLS, CACHE, GROUPS, design, fit, race_ll

TEST_YEARS = (2021, 2022, 2023, 2024, 2025, 2026)
MODEL_COLS = BASE_COLS + GROUPS["sire"]
MIN_RACES, T_MIN = 1500, 2.0


def load():
    A = pd.read_pickle(f"{CACHE}/newinfo.pkl")
    F = pd.read_pickle(f"{CACHE}/feat.pkl")[["race_id", "horse_id", "field_size", "distance", "going_n", "race_class"]]
    A = A.merge(F, on=["race_id", "horse_id"], how="left")
    book = (1 / A.sp).groupby(A.race_id).transform("sum")
    A = A[(book >= 1.05) & (book <= 1.5)]
    return A.sort_values("race_id", kind="mergesort").reset_index(drop=True)


def walk_forward(A):
    out = []
    for ty in TEST_YEARS:
        tr, te = A[A.year <= ty - 1], A[A.year == ty].copy()
        seg = lambda t: np.flatnonzero(np.r_[True, t.race_id.values[1:] != t.race_id.values[:-1]])
        for name, cols in (("p_cal", []), ("p_mod", MODEL_COLS)):
            Xtr, ms = design(tr, cols)
            Xte, _ = design(te, cols, ms)
            b = fit(Xtr, seg(tr), tr.win.values)
            _, p = race_ll(Xte, seg(te), te.win.values, b)
            te[name] = p
        out.append(te)
    P = pd.concat(out)
    P["ev"] = P.p_mod * P.sp
    P["ret"] = np.where(P.win == 1, P.sp, 0.0)
    return P


def cls_group(c):
    c = str(c)
    if c.startswith("MAI"):
        return "Maiden"
    if c.startswith("OPEN"):
        return "Open"
    if c.startswith("BM"):
        try:
            return "BM<=64" if int(c[2:]) <= 64 else "BM65+"
        except ValueError:
            return "Other"
    if c.startswith("CLS"):
        return "Class"
    if c.startswith("RST"):
        return "Restricted"
    return "Other"


def race_table(P):
    g = P.groupby("race_id")
    R = g.agg(year=("year", "first"), n=("win", "size"), field=("field_size", "first"), dist=("distance", "first"), going=("going_n", "first"),
              klass=("race_class", "first"), readable=("nruns", lambda s: (s >= 3).mean()), first=("nruns", lambda s: (s == 0).any()),
              fav=("sp", "min"))
    w = P[P.win == 1].set_index("race_id")
    R["delta"] = np.log(w.p_mod) - np.log(w.p_cal)
    R["fieldb"] = pd.cut(R.field, [0, 7, 10, 13, 99], labels=["5-7", "8-10", "11-13", "14+"])
    R["classb"] = R.klass.map(cls_group)
    R["distb"] = pd.cut(R.dist, [0, 1199, 1399, 1799, 9999], labels=["<1200", "1200-1399", "1400-1799", "1800+"])
    R["wetb"] = np.where(R.going >= 5, "wet (5+)", "dry")
    R["readb"] = pd.cut(R.readable, [-0.01, 0.7, 0.9, 1.01], labels=["<70% readable", "70-90%", "90%+ readable"])
    R["firstb"] = np.where(R["first"], "has first starter", "no first starter")
    R["favb"] = pd.cut(R.fav, [0, 2.5, 4, 6, 999], labels=["fav <$2.50", "$2.50-4", "$4-6", "fav $6+"])
    return R


DIMS = ["fieldb", "classb", "distb", "wetb", "readb", "firstb", "favb"]


def roi(bets):
    if not len(bets):
        return (0, np.nan, np.nan)
    ex10 = bets.drop(bets[bets.win == 1].nlargest(10, "sp").index) if len(bets) > 20 else bets
    return (len(bets), (bets.ret.mean() - 1) * 100, (ex10.ret.mean() - 1) * 100)


def t_stat(d):
    return d.mean() / (d.std() / np.sqrt(len(d))) if len(d) > 30 else np.nan


def main():
    A = load()
    print(f"clean-book runners {len(A):,}, races {A.race_id.nunique():,}", flush=True)
    P = walk_forward(A)
    R = race_table(P)
    P = P.join(R[DIMS + ["delta"]], on="race_id")
    print(f"\nWalk-forward test races {len(R):,} ({TEST_YEARS[0]}-{TEST_YEARS[-1]}). Overall delta {R.delta.mean()*1e4:+.1f} (1e-4 nats a race), t {t_stat(R.delta):.1f}")
    n, r, x = roi(P[P.ev > 1.05])
    print(f"All races, EV > 1.05 bets: n={n} ROI {r:+.1f}% ex10 {x:+.1f}%   |  EV > 1.00: n,roi,ex10 = {roi(P[P.ev > 1.0])}")

    print("\n=== Part A: segments (2021-2026 pooled, descriptive) ===")
    print(f"{'segment':28} {'races':>7} {'delta(1e-4)':>11} {'t':>5} | {'bets EV>1.05':>12} {'ROI':>7} {'ex10':>7}")
    for d in DIMS:
        for b, sub in R.groupby(d, observed=True):
            bets = P[(P[d] == b) & (P.ev > 1.05)]
            n, r, x = roi(bets)
            print(f"{d + ': ' + str(b):28} {len(sub):7} {sub.delta.mean()*1e4:11.1f} {t_stat(sub.delta):5.1f} | {n:12} {r:+7.1f} {x:+7.1f}")

    print("\n=== Part B: pick segments on EARLIER years (delta t >= %.0f, >= %d races), measure on the test year ===" % (T_MIN, MIN_RACES))
    rows = []
    for d in DIMS:
        picked_races, picked_bets, per_year = [], [], []
        for ty in TEST_YEARS[2:]:
            past, now = R[R.year < ty], R[R.year == ty]
            keep = [b for b, s in past.groupby(d, observed=True) if len(s) >= MIN_RACES and t_stat(s.delta) >= T_MIN]
            sel = now[now[d].isin(keep)]
            picked_races.append(sel)
            bets = P[(P.year == ty) & P.race_id.isin(sel.index) & (P.ev > 1.05)]
            picked_bets.append(bets)
            per_year.append((ty, [str(k) for k in keep], len(sel), sel.delta.mean() * 1e4 if len(sel) else np.nan, len(bets), roi(bets)[1]))
        allr, allb = pd.concat(picked_races), pd.concat(picked_bets)
        n, r, x = roi(allb)
        rows.append((d, len(allr), allr.delta.mean() * 1e4 if len(allr) else np.nan, t_stat(allr.delta) if len(allr) else np.nan, n, r, x))
        print(f"\n{d}")
        for ty, keep, nr, dl, nb, rr in per_year:
            print(f"   {ty}: picked {keep or 'nothing'}  races {nr}  delta {dl:+.1f}  bets {nb}  ROI {rr:+.1f}%")
    print(f"\n{'dimension':10} {'races':>7} {'delta':>7} {'t':>5} | {'bets':>6} {'ROI':>7} {'ex10':>7}   (test years 2023-2026 only, segments chosen on earlier years)")
    for d, nr, dl, t, n, r, x in rows:
        print(f"{d:10} {nr:7} {dl:+7.1f} {t:5.1f} | {n:6} {r:+7.1f} {x:+7.1f}")
    base = R[R.year >= 2023]
    nb, rb, xb = roi(P[(P.year >= 2023) & (P.ev > 1.05)])
    print(f"{'ALL races':10} {len(base):7} {base.delta.mean()*1e4:+7.1f} {t_stat(base.delta):5.1f} | {nb:6} {rb:+7.1f} {xb:+7.1f}")

    print("\n=== Part C: race must sit in a past-significant segment on 2+ dimensions ===")
    sels = []
    for ty in TEST_YEARS[2:]:
        past, now = R[R.year < ty], R[R.year == ty]
        score = pd.Series(0, index=now.index)
        for d in DIMS:
            keep = [b for b, s in past.groupby(d, observed=True) if len(s) >= MIN_RACES and t_stat(s.delta) >= T_MIN]
            score += now[d].isin(keep).astype(int)
        sels.append(now[score >= 2])
    sel = pd.concat(sels)
    bets = P[P.race_id.isin(sel.index) & (P.ev > 1.05)]
    n, r, x = roi(bets)
    print(f"races {len(sel)} (of {len(base)})  delta {sel.delta.mean()*1e4 if len(sel) else float('nan'):+.1f}  bets {n}  ROI {r:+.1f}%  ex10 {x:+.1f}%")


if __name__ == "__main__":
    main()
