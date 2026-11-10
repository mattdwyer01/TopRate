"""Do the ratings beat the Betfair starting price (BSP) after commission?

Run with PYTHONPATH=. python research/betfair_bsp_test.py
Reads data/betfair_bsp/win_*.csv.gz (betfair_bsp.py), the results files and runners.csv (+ archive).
Join: Melbourne race date + normalised horse name. BSP profit on a $1 win bet = (BSP - 1) x (1 - commission).

Part A  results files (long window): books, flat ROI at SP and BSP by price band, favourite, L3 #1 (mean of the
        last 3 ratings before the race), conditional logit of the rating on top of the BSP.
Part B  runners.csv window (logged Proj, Nett, Spd): #1 picks, within 2 of the top, rated-price overlays, at BSP.
Part C  the Volume rules log at BSP.
"""
import glob
import os
import re
import sys
import warnings

import numpy as np
import pandas as pd

warnings.filterwarnings("ignore")
COMM = float(os.environ.get("BSP_COMM", "0.08"))
COMMS = (0.06, 0.08, 0.10)


def norm(s):
    return re.sub(r"[^a-z]", "", str(s).lower())


def load_bsp():
    fs = sorted(glob.glob("data/betfair_bsp/win_*.csv.gz"))
    b = pd.concat([pd.read_csv(f).rename(columns=lambda c: c.strip().lower()) for f in fs], ignore_index=True)   # older files use upper-case headers
    b = b.drop_duplicates(["event_id", "selection_id"])
    t = pd.to_datetime(b.event_dt, format="%d-%m-%Y %H:%M", errors="coerce").dt.tz_localize("UTC")
    b["date"] = t.dt.tz_convert("Australia/Melbourne").dt.strftime("%Y-%m-%d")
    b["hn"] = b.selection_name.str.replace(r"^\s*\d+\.\s*", "", regex=True).map(norm)
    for c in ("bsp", "ppwap", "morningwap", "pptradedvol", "win_lose"):
        b[c] = pd.to_numeric(b[c], errors="coerce")
    b = b[b.bsp > 1.0]
    b["bf_book"] = b.groupby("event_id").bsp.transform(lambda x: (1 / x).sum())
    b["bf_n"] = b.groupby("event_id").bsp.transform("size")
    b["bf_vol"] = b.groupby("event_id").pptradedvol.transform("sum")
    return b[["event_id", "date", "hn", "menu_hint", "event_name", "bsp", "ppwap", "morningwap", "pptradedvol",
              "win_lose", "bf_book", "bf_n", "bf_vol"]]


def roi_line(label, d, price="bsp", comm=None, stake=None):
    """flat $1 (or given stakes) ROI; commission applies to Betfair prices only"""
    if len(d) == 0:
        return "%-44s n=0" % label
    c = COMM if comm is None else comm
    st = np.ones(len(d)) if stake is None else d[stake].values
    p = d[price].values
    w = d.won.values.astype(float)
    net = (p - 1) * ((1 - c) if price != "sp" else 1.0)
    pnl = st * (w * net - (1 - w))
    roi = pnl.sum() / st.sum()
    # halves by date, and without the 3 / 10 best winning bets
    dd = d.date.values
    mid = np.sort(dd)[len(dd) // 2]
    h1 = pnl[dd < mid].sum() / max(st[dd < mid].sum(), 1e-9)
    h2 = pnl[dd >= mid].sum() / max(st[dd >= mid].sum(), 1e-9)
    o = np.sort(pnl)[::-1]
    ex3 = (pnl.sum() - o[:3].sum()) / st.sum()
    ex10 = (pnl.sum() - o[:10].sum()) / st.sum()
    return "%-44s n=%6d win %5.1f%% avg $%6.2f ROI %+6.1f%%  halves %+6.1f/%+6.1f  ex3 %+6.1f ex10 %+6.1f" % (
        label, len(d), 100 * w.mean(), p.mean(), 100 * roi, 100 * h1, 100 * h2, 100 * ex3, 100 * ex10)


def both(label, d):
    print(roi_line(label + " @SP", d, "sp"))
    print(roi_line(label + " @BSP net %d%%" % round(100 * COMM), d, "bsp"))


def clogit_gain(d, col, race="rid"):
    """winner log-lik per race: BSP alone vs BSP + rating z-score, weights cross-fitted on date halves"""
    from scipy.optimize import minimize
    d = d[d[col].notna()].copy()
    d["lp"] = -np.log(d.bsp)
    d["z"] = d.groupby(race)[col].transform(lambda x: (x - x.mean()) / (x.std(ddof=0) + 1e-9))
    g = d.groupby(race)
    ok = (g.won.transform("sum") == 1) & (g.won.transform("size") >= 5)
    d = d[ok]
    rid = pd.factorize(d[race])[0]
    n = rid.max() + 1
    dates = d.groupby(rid).date.first().values
    half = dates < np.sort(dates)[n // 2]

    def ll(w, X, mask=None):
        s = X @ w
        m = np.full(n, -np.inf)
        np.maximum.at(m, rid, s)
        e = np.exp(s - m[rid])
        den = np.bincount(rid, e, n)
        per = np.bincount(rid, d.won.values * (s - m[rid]), n) - np.log(den)
        return per if mask is None else -per[mask].mean()

    out = {}
    for name, cols in (("bsp", ["lp"]), ("bsp+rating", ["lp", "z"])):
        X = d[cols].values
        per = np.zeros(n)
        for fit, score in ((half, ~half), (~half, half)):
            w = minimize(ll, np.r_[1.0, np.zeros(len(cols) - 1)], args=(X, fit), method="BFGS").x
            per[score] = ll(w, X)[score]
            out[name + "_w"] = w
        out[name] = per
    diff = out["bsp+rating"] - out["bsp"]
    print("  %s: %d races, BSP alone %.4f, + rating %.4f, gain %+.4f (se %.4f), weights %s" % (
        col, n, out["bsp"].mean(), out["bsp+rating"].mean(), diff.mean(), diff.std() / np.sqrt(n),
        np.round(out["bsp+rating_w"], 3)))


def part_a(b):
    print("\n=== Part A: results files joined to BSP ===")
    fs = [f for f in sorted(glob.glob("race_results_20*.csv.gz")) if re.search(r"20(2[3-6])", f)]
    use = ["race_id", "date", "horse_id", "horse", "track", "wpr", "priceStarting", "positionFinish", "isBarrierTrial",
           "race_class"]
    r = pd.concat([pd.read_csv(f, usecols=lambda c: c in use + ["is_jumpout"], low_memory=False) for f in fs])
    r = r[(r.isBarrierTrial != True) & (r.get("is_jumpout") != True)]  # noqa: E712
    r = r[~r.race_class.astype(str).str.contains("Hurdle|Steeple", case=False)]
    r = r.drop_duplicates(["race_id", "horse_id"]).sort_values(["horse_id", "date"])
    r["wpr"] = pd.to_numeric(r.wpr, errors="coerce")
    g = r.groupby("horse_id").wpr
    r["l3"] = (g.shift(1) + g.shift(2) + g.shift(3)) / 3
    r["sp"] = pd.to_numeric(r.priceStarting, errors="coerce")
    r["won"] = (pd.to_numeric(r.positionFinish, errors="coerce") == 1).astype(int)
    r = r[r.date >= b.date.min()]
    r["hn"] = r.horse.map(norm)
    m = r.merge(b, on=["date", "hn"], how="left")
    print("results runners %d, with BSP %d (%.1f%%), dates %s to %s" % (
        len(m), m.bsp.notna().sum(), 100 * m.bsp.notna().mean(), m.date.min(), m.date.max()))
    m["rid"] = m.race_id
    g = m.groupby("rid")
    m["n"] = g.won.transform("size")
    m["nb"] = g.bsp.transform("count")
    m["sp_book"] = g.sp.transform(lambda x: (1 / x).sum())
    m["nw"] = g.won.transform("sum")
    full = m[(m.nb == m.n) & (m.nw == 1) & (m.n >= 5) & m.sp.notna() & m.sp_book.between(1.05, 2.0)].copy()
    full["bbook"] = full.groupby("rid").bsp.transform(lambda x: (1 / x).sum())
    full = full[full.bbook.between(0.95, 1.15)]
    nr = full.rid.nunique()
    per = full.groupby("rid").agg(sp_book=("sp_book", "first"), bbook=("bbook", "first"), vol=("bf_vol", "first"))
    print("complete races (every runner has SP and BSP, clean books): %d" % nr)
    print("median book: SP %.3f, BSP %.3f; median pre-play matched volume $%.0f (10%% under $%.0f)" % (
        per.sp_book.median(), per.bbook.median(), per.vol.median(), per.vol.quantile(0.1)))
    agree = (full.won == full.win_lose).mean()
    print("Betfair win flag agrees with the results file for %.2f%% of runners" % (100 * agree))

    print("\nAll runners by BSP band (flat $1):")
    bands = [(1, 2), (2, 3), (3, 5), (5, 8), (8, 15), (15, 30), (30, 1001)]
    for lo, hi in bands:
        d = full[(full.bsp >= lo) & (full.bsp < hi)]
        print(roi_line("  BSP $%g-%g @SP" % (lo, hi), d, "sp"))
        print(roi_line("  BSP $%g-%g @BSP net" % (lo, hi), d, "bsp"))
    both("All runners", full)
    full["fav"] = full.bsp == full.groupby("rid").bsp.transform("min")
    both("Favourite (shortest BSP)", full[full.fav])

    L = full[full.groupby("rid").l3.transform(lambda x: x.notna().mean()) >= 0.8].copy()
    L["rk"] = L.groupby("rid").l3.rank(ascending=False, method="min")
    L["gap"] = L.groupby("rid").l3.transform("max") - L.l3
    print("\nL3 (mean of last 3 ratings before the race), races with 80%%+ of the field rated: %d" % L.rid.nunique())
    top = L[L.rk == 1]
    both("L3 #1", top)
    for c in COMMS:
        print(roi_line("L3 #1 @BSP commission %d%%" % round(100 * c), top, "bsp", comm=c))
    for lo, hi in ((1, 3), (3, 6), (6, 12), (12, 1001)):
        d = top[(top.bsp >= lo) & (top.bsp < hi)]
        print(roi_line("  L3 #1, BSP $%g-%g @BSP net" % (lo, hi), d, "bsp"))
    both("L3 #1 and favourite", top[top.fav])
    both("L3 #1, not favourite", top[~top.fav])
    both("L3 within 2 of top", L[L.gap <= 2])
    print("\nRating on top of the BSP (winner log-lik per race):")
    clogit_gain(L, "l3")
    return full


def part_b(b):
    print("\n=== Part B: runners.csv window (logged Proj, Nett, Spd) joined to BSP ===")
    import runners_io
    df = runners_io.read_runners()
    df = df[(df.scratched != 1) & df.date.notna()].copy()
    for c in ("wprp_proj", "wpr_nett", "spd_fig", "starting_price_sp", "fixed_win_price", "won", "finish_position"):
        df[c] = pd.to_numeric(df[c], errors="coerce")
    df["sp"] = df.starting_price_sp.fillna(df.fixed_win_price)
    df["wonk"] = df.won.where(df.won.notna(), (df.finish_position == 1).astype(float).where(df.finish_position.notna()))
    df["hn"] = df.horse.map(norm)
    df = df[df.date >= b.date.min()]
    df["rid"] = df.date + "|" + df.venue.astype(str) + "|" + df.race.astype(str)
    m = df.merge(b, on=["date", "hn"], how="left")
    g = m.groupby("rid")
    m["n"] = g.hn.transform("size")
    m["nb"] = g.bsp.transform("count")
    m["won"] = m.win_lose                      # Betfair's own result, so unresulted rows in runners.csv do not matter
    m["nw"] = g.win_lose.transform("sum")
    full = m[(m.nb >= 0.9 * m.n) & (m.nw == 1) & (m.nb >= 5) & m.bsp.notna()].copy()
    full["bbook"] = full.groupby("rid").bsp.transform(lambda x: (1 / x).sum())
    full = full[full.bbook.between(0.9, 1.15)]
    full["sp"] = full.sp.fillna(full.bsp)
    full["fav"] = full.bsp == full.groupby("rid").bsp.transform("min")
    print("races with BSP for 90%%+ of our field: %d (%s to %s), runners %d" % (
        full.rid.nunique(), full.date.min(), full.date.max(), len(full)))
    for col, name in (("wprp_proj", "Proj"), ("wpr_nett", "Nett"), ("spd_fig", "Spd")):
        R = full[full.groupby("rid")[col].transform(lambda x: x.notna().mean()) >= 0.8].copy()
        if R.rid.nunique() < 50:
            print("%s: too few races" % name)
            continue
        R["rk"] = R.groupby("rid")[col].rank(ascending=False, method="min")
        R["gap"] = R.groupby("rid")[col].transform("max") - R[col]
        top = R[R.rk == 1]
        print("\n%s, %d races" % (name, R.rid.nunique()))
        both("%s #1" % name, top)
        both("%s #1 and favourite" % name, top[top.fav])
        both("%s #1, not favourite" % name, top[~top.fav])
        for lo, hi in ((1, 3), (3, 6), (6, 12), (12, 1001)):
            print(roi_line("  %s #1, BSP $%g-%g @BSP net" % (name, lo, hi), top[(top.bsp >= lo) & (top.bsp < hi)], "bsp"))
        if col == "wprp_proj":
            both("Proj within 2 of top", R[R.gap <= 2])
            both("Proj within 4 of top", R[R.gap <= 4])
            # rated price: softmax of Proj at 0.20 per point over the rated runners
            e = np.exp(0.20 * (R[col] - R.groupby("rid")[col].transform("max")))
            R["p"] = e / e.groupby(R.rid).transform("sum")
            R["ev"] = R.p * (1 + (R.bsp - 1) * (1 - COMM))
            for th in (1.0, 1.1, 1.25, 1.5):
                print(roi_line("  rated-price overlay EV>%.2f @BSP net" % th, R[R.ev > th], "bsp"))
                print(roi_line("    and within 4 of top", R[(R.ev > th) & (R.gap <= 4)], "bsp"))
            # does the price move toward our picks? pre-play average vs BSP
            t2 = top[top.ppwap > 1]
            print("  Proj #1: mean ln(pre-play average / BSP) %+.4f (se %.4f); >0 means the pick shortened into the jump" % (
                np.log(t2.ppwap / t2.bsp).mean(), np.log(t2.ppwap / t2.bsp).std() / np.sqrt(len(t2))))
            t3 = t2.assign(bsp=t2.ppwap)
            print(roi_line("  Proj #1 at the pre-play average price, net", t3, "bsp"))
        print("  rating on top of the BSP:")
        clogit_gain(R, col)
    return full


def part_c(b):
    if not os.path.exists("volume_bets_log.csv"):
        return
    print("\n=== Part C: Volume rules log at BSP ===")
    v = pd.read_csv("volume_bets_log.csv")
    v = v[(v.void != 1) & v.won.notna()].copy()
    v["hn"] = v.horse.map(norm)
    m = v.merge(b, on=["date", "hn"], how="left")
    print("settled bets %d, with BSP %d" % (len(m), m.bsp.notna().sum()))
    m = m[m.bsp.notna()].copy()
    m["sp"] = m.price_logged
    for rule in ("v1", "v2", "v3"):
        d = m[m[rule] == 1].copy()
        if len(d) < 10:
            continue
        d["st"] = d["stake_" + rule]
        print(roi_line("%s at the fixed price logged" % rule, d, "sp", stake="st"))
        print(roi_line("%s @BSP net %d%%" % (rule, round(100 * COMM)), d, "bsp", stake="st"))
        print("   mean fixed price logged $%.2f, mean BSP $%.2f, BSP higher for %.0f%% of bets" % (
            d.sp.mean(), d.bsp.mean(), 100 * (d.bsp > d.sp).mean()))


if __name__ == "__main__":
    b = load_bsp()
    print("BSP rows %d, events %d, dates %s to %s" % (len(b), b.event_id.nunique(), b.date.min(), b.date.max()))
    parts = sys.argv[1:] or ["a", "b", "c"]
    if "a" in parts:
        part_a(b)
    if "b" in parts:
        part_b(b)
    if "c" in parts:
        part_c(b)
