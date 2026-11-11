"""Runners within n Proj points of the top rated whose Betfair price is above or close to the rated price (10 Nov 2026).

Rated price = 1 / softmax chance of the logged Proj at 0.20 a point (the dashboard's Rated $ before its noise simulation and sharpening).
ratio = Betfair starting price / rated price: 1.0 = the Betfair price equals the rated price, above 1 = an overlay.
Commission 10% NSW, 8% elsewhere, flat $1 a bet.
Part A: the real logged Proj (runners.csv and archive, races where 90%+ of the field has a Proj and a Betfair price).
Part B: three years with a stand-in rating (least squares on last run, last-3, last-8, best of 8, fitted on 2023; needs /tmp/value_model2_frame.pkl),
        cells ranked on 2024 and scored on 2025 and 2026.
  PYTHONPATH=. python research/betfair_gap_price_test.py
"""
import os
import sys
import warnings

import numpy as np
import pandas as pd

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from betfair_bsp_test import load_bsp, norm, nsw_flag, COMM_NSW, COMM_OTHER  # noqa: E402
import runners_io  # noqa: E402

warnings.filterwarnings("ignore")
BETA = 0.20
GAPS = [0, 1, 2, 3, 4, 6]
RATIOS = [("any price", 0, 99), ("under 0.7 (well under rated)", 0, 0.7), ("0.7 to 0.9", 0.7, 0.9), ("0.9 to 1.1 (close)", 0.9, 1.1), ("0.9+ (above or close)", 0.9, 99),
          ("1.0+ (overlay)", 1.0, 99), ("1.1 to 1.5", 1.1, 1.5), ("1.2+", 1.2, 99), ("1.5+", 1.5, 99), ("0.9 to 1.5", 0.9, 1.5)]


def prep(F, col):
    g = F.groupby("rid")
    F["gap"] = g[col].transform("max") - F[col]
    e = np.exp(BETA * -F.gap)
    F["pr"] = e / e.groupby(F.rid).transform("sum")
    F["ratio"] = F.bsp * F.pr
    F["pnl"] = F.won * (F.bsp - 1) * (1 - F.comm) - (1 - F.won)
    return F


def line(x):
    if len(x) < 30:
        return "n=%5d" % len(x)
    d = np.sort(x.date.values)
    mid = d[len(d) // 2]
    o = np.sort(x.pnl.values)[::-1]
    return "n=%6d win %5.1f%% (Betfair %5.1f%%, rated %5.1f%%) avg $%5.2f ROI %+6.1f%% halves %+6.1f/%+6.1f ex10 %+6.1f%%" % (
        len(x), 100 * x.won.mean(), 100 * x.pm.mean(), 100 * x.pr.mean(), x.bsp.mean(), 100 * x.pnl.mean(), 100 * x.pnl[x.date < mid].mean(),
        100 * x.pnl[x.date >= mid].mean(), 100 * (x.pnl.sum() - o[:10].sum()) / len(x))


def grid(F, cap=None):
    X = F if cap is None else F[F.bsp < cap]
    for n in GAPS:
        print("-- %s" % ("top rated only" if n == 0 else "within %d points of the top" % n))
        for lab, a, c in RATIOS:
            print("   %-30s %s" % (lab, line(X[(X.gap <= n) & (X.ratio >= a) & (X.ratio < c)])))


def boot(x, label):
    days = x.groupby("date").pnl.agg(["sum", "size"])
    rng = np.random.default_rng(1)
    idx = rng.integers(0, len(days), (2000, len(days)))
    bs = days["sum"].values[idx].sum(1) / days["size"].values[idx].sum(1)
    print("   %s: 90%% range by day %+.1f%% to %+.1f%%, chance above zero %.0f%%" % (label, 100 * np.quantile(bs, 0.05), 100 * np.quantile(bs, 0.95), 100 * (bs > 0).mean()))


# ---------------- Part A: the logged Proj ----------------
b = load_bsp()
df = runners_io.read_runners()
df = df[(df.scratched != 1) & df.date.notna()].copy()
df["proj"] = pd.to_numeric(df.wprp_proj, errors="coerce")
df["hn"] = df.horse.map(norm)
df["rid"] = df.date + "|" + df.venue.astype(str) + "|" + df.race.astype(str)
m = df.merge(b.drop_duplicates(["date", "hn"]), on=["date", "hn"], how="left")
g = m.groupby("rid")
m["n"], m["nb"], m["np_"] = g.hn.transform("size"), g.bsp.transform("count"), g.proj.transform("count")
m["won"] = m.win_lose
m["nw"] = g.win_lose.transform("sum")
F = m[(m.nb >= 0.9 * m.n) & (m.np_ >= 0.9 * m.n) & (m.nw == 1) & (m.nb >= 5) & m.bsp.notna() & m.proj.notna()].copy()
F["bbook"] = F.groupby("rid").bsp.transform(lambda x: (1 / x).sum())
F = F[F.bbook.between(0.9, 1.15)]
F["pm"] = (1 / F.bsp) / F.bbook
F["comm"] = np.where(nsw_flag(F.venue), COMM_NSW, COMM_OTHER)
F = prep(F, "proj")
print("===== Part A: logged Proj, %d races, %d runners, %s to %s =====" % (F.rid.nunique(), len(F), F.date.min(), F.date.max()))
grid(F)
print("\n===== Part A again, Betfair price under $20 only =====")
grid(F, 20)
for n, a, c in ((2, 0.9, 99), (4, 0.9, 99), (2, 0.9, 1.5), (4, 0.9, 1.5), (4, 1.0, 99)):
    boot(F[(F.gap <= n) & (F.ratio >= a) & (F.ratio < c)], "within %d, ratio %.1f to %s" % (n, a, "any" if c > 50 else c))
print("\nby month, within 4 and ratio 0.9+:")
x = F[(F.gap <= 4) & (F.ratio >= 0.9)]
print(x.groupby(x.date.str[:7]).pnl.agg(["size", "mean"]).round(3).T.to_string())
print("by Betfair price, within 4 and ratio 0.9+:")
print(x.groupby(pd.cut(x.bsp, [1, 3, 6, 10, 20, 50, 1e4])).apply(lambda z: pd.Series({"n": len(z), "win %": 100 * z.won.mean(), "Betfair %": 100 * z.pm.mean(), "ROI %": 100 * z.pnl.mean()})).round(1).to_string())

# ---------------- Part B: stand-in rating, three years ----------------
fp = os.environ.get("VM2_CACHE", "/tmp/value_model2_frame.pkl")
if os.path.exists(fp):
    d = pd.read_pickle(fp)
    d = d[d.ds >= "2023-01-01"].copy()
    cols = ["w1", "m3", "m8", "max8"]
    d = d[d.groupby("race_id").m3.transform(lambda x: x.notna().all())]          # every runner has form
    d = d[d[cols + ["wpr"]].notna().all(axis=1) | True]
    fit = d[(d.ds < "2024-01-01") & d.wpr.notna() & d[cols].notna().all(axis=1)]
    A = np.c_[np.ones(len(fit)), fit[cols].values]
    co = np.linalg.lstsq(A, fit.wpr.values, rcond=None)[0]
    d = d[d[cols].notna().all(axis=1)]
    d = d[d.groupby("race_id").horse_id.transform("size") == d.nr]
    d["si"] = co[0] + d[cols].values @ co[1:]
    d["rid"], d["date"] = d.race_id, d.ds
    d = prep(d, "si")
    d["yr"] = d.ds.str[:4]
    T = d[d.ds >= "2024-01-01"]
    print("\n\n===== Part B: stand-in rating (fitted on 2023: %s), %d races 2024 to %s, every runner with form =====" % (
        ", ".join("%s %.2f" % (c, v) for c, v in zip(cols, co[1:])), T.rid.nunique(), T.ds.max()))
    print("%-34s %-30s %s" % ("", "", " | ".join("%s: n, ROI" % y for y in ("2024", "2025", "2026"))))
    rows = []
    for n in GAPS:
        for lab, a, c in RATIOS:
            for cap in (None, 20):
                x = T[(T.gap <= n) & (T.ratio >= a) & (T.ratio < c)]
                if cap:
                    x = x[x.bsp < cap]
                s = x.groupby("yr").pnl.agg(["size", "mean"]).reindex(["2024", "2025", "2026"])
                rows.append((n, lab, cap, s))
                print("%-34s %-30s %s" % (("top rated" if n == 0 else "within %d" % n) + (", under $20" if cap else ""), lab,
                                          " | ".join("%6d %+6.1f%%" % (s["size"][y] if s["size"][y] == s["size"][y] else 0, 100 * s["mean"][y]) for y in s.index)))
    ok = [r for r in rows if r[3]["size"].min() >= 500]
    best = sorted(ok, key=lambda r: -r[3]["mean"]["2024"])[:10]
    print("\nthe 10 best cells on 2024 (500+ bets a year) averaged %+.1f%% in 2024, %+.1f%% in 2025, %+.1f%% in 2026; all %d cells %+.1f%% / %+.1f%% / %+.1f%%" % (
        100 * np.mean([r[3]["mean"]["2024"] for r in best]), 100 * np.mean([r[3]["mean"]["2025"] for r in best]), 100 * np.mean([r[3]["mean"]["2026"] for r in best]),
        len(ok), *[100 * np.mean([r[3]["mean"][y] for r in ok]) for y in ("2024", "2025", "2026")]))
