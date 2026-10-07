"""Read-only analysis: horses inside the 2/4/6 gap lines that are overlays (or minor underlays) AND have a
positive speed map (demeaned suitability > 0 / >= 0.5 / >= 1.0), staked to RETURN a fixed number of units
(stake = R / price, so a win returns R units and a loss costs R / price).

Population: projection log (proj, adj = suitability, src oof = back-filled / live), joined to results in
toprate_runners (+ archive). Plain model rating (no ATW offset: history has none). Fair price = softmax, beta 0.20.
Price = starting_price_sp, else fixed_win_price.
"""
import sys
import numpy as np
import pandas as pd

sys.path.insert(0, ".")
import runners_io

BETA = 0.20
d = runners_io.read_runners()
d["run_id"] = d["run_id"].astype("int64")
res = d[["run_id", "won", "resulted", "scratched", "starting_price_sp", "fixed_win_price", "finish_position"]].copy()
log = pd.read_csv("wpr_projection_log.csv.gz")
log = log.sort_values("made").drop_duplicates("run_id", keep="last")
m = log.merge(res, on="run_id", how="left")
m["price"] = pd.to_numeric(m["starting_price_sp"], errors="coerce")
fp = pd.to_numeric(m["fixed_win_price"], errors="coerce")
m["price"] = m["price"].where(m["price"] > 1, fp)
m = m[(m["scratched"].fillna(0) != 1) & m["proj"].notna()].copy()

# races fully resulted (a winner known)
win_races = m.groupby("race_id")["won"].apply(lambda s: (s == 1).any())
m = m[m["race_id"].isin(win_races[win_races].index)].copy()
m["won"] = (m["won"] == 1).astype(int)

rows = []
for rid, g in m.groupby("race_id"):
    g = g.copy()
    top = g["proj"].max()
    g["gap"] = top - g["proj"]
    e = np.exp(BETA * (g["proj"] - top))
    g["fair"] = len(g) and (e.sum() / e)
    s = g["adj"]
    g["sm"] = s - s.mean() if s.notna().any() else np.nan
    g.loc[s.isna(), "sm"] = np.nan
    rows.append(g)
a = pd.concat(rows)
a = a[a["price"].notna()].copy()
a["ratio"] = a["price"] / a["fair"]
a["date"] = pd.to_datetime(a["date"])
print(f"runners {len(a)}, races {a.race_id.nunique()}, dates {a.date.nunique()} ({a.date.min().date()} to {a.date.max().date()})")
print(f"with suitability (main model): {a.sm.notna().mean():.1%}")
print("src mix:", a.drop_duplicates('race_id').src.value_counts().to_dict())


def tier_return(gap, scheme):
    if scheme == "flat4":
        return 4.0
    if scheme == "tier432":
        return 4.0 if gap <= 2 else 3.0 if gap <= 4 else 2.0
    raise ValueError


def run(sel, scheme):
    if sel.empty:
        return None
    R = np.array([tier_return(g, scheme) for g in sel["gap"]])
    stake = R / sel["price"].values
    ret = R * sel["won"].values
    prof = ret - stake
    return dict(n=len(sel), wins=int(sel["won"].sum()), win=sel["won"].mean() * 100,
                turn=stake.sum(), roi=prof.sum() / stake.sum() * 100, prof=prof.sum(),
                avgp=sel["price"].mean()), R, stake, prof


def fmt(r):
    if r is None:
        return "n=0"
    s = r[0]
    return f"n={s['n']:5d} w={s['wins']:4d} win%={s['win']:5.1f} avg$={s['avgp']:5.2f} turn={s['turn']:7.1f}u profit={s['prof']:+7.1f}u ROI={s['roi']:+6.1f}%"


def robust(sel, scheme):
    r = run(sel, scheme)
    if r is None or r[0]["n"] < 30:
        return ""
    mid = sel["date"].sort_values().iloc[len(sel) // 2]
    h1, h2 = run(sel[sel["date"] < mid], scheme), run(sel[sel["date"] >= mid], scheme)
    w = sel[sel["won"] == 1].sort_values("price", ascending=False).head(3).index
    ex = run(sel.drop(w), scheme)
    f = lambda x: f"{x[0]['roi']:+.1f}" if x else "na"
    return f"halves {f(h1)}/{f(h2)} ex3big {f(ex)}"


LINES = [2, 4, 6]
PRICE = [("overlay>=1.00", 1.00), ("minor underlay>=0.90", 0.90), ("underlay>=0.85", 0.85), ("any price", 0.0)]
SM = [("no map filter", -99), ("sm>0", 1e-9), ("sm>=0.5", 0.5), ("sm>=1.0", 1.0)]

for scheme, title in [("flat4", "RETURN 4 UNITS on every selection"),
                      ("tier432", "TIERED return: gap<=2 -> 4u, 2-4 -> 3u, 4-6 -> 2u")]:
    print("\n" + "=" * 100 + f"\n{title}\n" + "=" * 100)
    for pname, pthr in PRICE:
        print(f"\n--- price rule: {pname}")
        for smname, sthr in SM:
            for L in LINES:
                if scheme == "tier432" and L != 6:
                    continue
                sel = a[(a["gap"] <= L) & (a["ratio"] >= pthr)]
                if sthr > -99:
                    sel = sel[sel["sm"].notna() & (sel["sm"] >= sthr)]
                r = run(sel, scheme)
                print(f"  {smname:14s} inside {L}: {fmt(r)}  {robust(sel, scheme)}")

# band view (flat4, unconditional by tier, so the bands can be compared directly)
print("\n" + "=" * 100 + "\nBAND VIEW (return 4u each), overlay-or-minor-underlay >=0.90\n" + "=" * 100)
for smname, sthr in SM:
    for lo, hi in [(-1, 2), (2, 4), (4, 6)]:
        sel = a[(a["gap"] > lo) & (a["gap"] <= hi) & (a["ratio"] >= 0.90)]
        if sthr > -99:
            sel = sel[sel["sm"].notna() & (sel["sm"] >= sthr)]
        print(f"  {smname:14s} gap ({max(lo,0)}, {hi}]: {fmt(run(sel, 'flat4'))}  {robust(sel, 'flat4')}")
