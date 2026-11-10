"""Search for simple rules that pay at the Betfair starting price after commission (10 Nov 2026).

Honest search: every rule is a plain condition known before the jump (or a pair of them), crossed with a Betfair price band, backing and laying.
Rules are RANKED on 2023-2024 only, then scored untouched on 2025 and on 2026 (to 8 Oct). The number of rules tried is printed so the count of
survivors can be compared with what chance alone would give.
Commission 10% NSW, 8% elsewhere (the frame's `comm`). Back: $1 flat. Lay: backer's stake $1 (win 1 x (1 - comm) when it loses, lose price - 1 when it wins),
ROI on the liability (price - 1).
Needs the cached frame from research/value_model2.py (/tmp/value_model2_frame.pkl; `PYTHONPATH=. python research/value_model2.py bias` rebuilds it).
  PYTHONPATH=. python research/betfair_rule_search.py
"""
import itertools
import os
import sys
import warnings

import numpy as np
import pandas as pd

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from betfair_bsp_test import load_bsp  # noqa: E402

warnings.filterwarnings("ignore")
d = pd.read_pickle(os.environ.get("VM2_CACHE", "/tmp/value_model2_frame.pkl"))
d = d[d.ds >= "2023-01-01"].reset_index(drop=True)
b = load_bsp()[["date", "hn", "ppwap", "morningwap", "pptradedvol", "bf_vol"]].drop_duplicates(["date", "hn"])
d = d.merge(b, left_on=["ds", "hn"], right_on=["date", "hn"], how="left", suffixes=("", "_bf"))
d["yr"] = d.ds.str[:4].astype(int)
d["per"] = np.where(d.yr <= 2024, 0, np.where(d.yr == 2025, 1, 2))
won = d.won.values.astype(float)
bsp = d.bsp.values
d["back"] = won * (bsp - 1) * (1 - d.comm.values) - (1 - won)
d["lay"] = (1 - won) * (1 - d.comm.values) - won * (bsp - 1)
d["liab"] = bsp - 1
d["mv_am"] = d.ppwap / d.morningwap          # under 1 = firmed from the morning to pre-play
d["mv_bsp"] = d.bsp / d.ppwap                # over 1 = drifted into the jump (only known at the jump)
d["sp_ratio"] = d.bsp / d.sp
cls = d.race_class.astype(str).str.upper()
dow = pd.to_datetime(d.ds).dt.dayofweek


def q(col, lo, hi):
    x = d[col]
    a, c = x.quantile(lo), x.quantile(hi)
    return ((x >= a) & (x <= c)).fillna(False).values


C = {
    "last-start winner": (d.l_won == 1).values, "first up": (d.firstup == 1).values, "second up": (d.secondup == 1).values,
    "backing up within 7 days": (d.backup == 1).values, "last run bad with an excuse": (d.l_bad_exc == 1).values,
    "last run bad": (d.l_bad == 1).values, "trialled since last run": (d.tr_since_run == 1).values,
    "favourite": (d.fav == 1).values, "2nd or 3rd in the market": d.pm_rank.between(2, 3).values, "4th to 6th in the market": d.pm_rank.between(4, 6).values,
    "field 5-7": (d.nr <= 7).values, "field 8-11": d.nr.between(8, 11).values, "field 12+": (d.nr >= 12).values,
    "maiden": cls.str.startswith("MAI").values, "not maiden": (~cls.str.startswith("MAI")).values,
    "wet track": (d.wet == 1).values, "dry track": (d.wet == 0).values, "NSW": d.nsw.values.astype(bool), "not NSW": ~d.nsw.values.astype(bool),
    "Saturday": (dow == 5).values, "midweek": (dow < 4).values,
    "inside third draw": (d.third == 0).values, "wide third draw": (d.third == 2).values,
    "forward style": q("style", 0, 0.25), "back style": q("style", 0.75, 1), "lone leader": (d.lone_lead == 1).values,
    "2yo or 3yo": (d.horse_age <= 3).values, "6yo+": (d.horse_age >= 6).values, "mare or filly": (d.sex >= 1).values,
    "jockey beats price (top fifth)": q("jk_ae", 0.8, 1), "jockey under price (bottom fifth)": q("jk_ae", 0, 0.2),
    "trainer beats price (top fifth)": q("tk_ae", 0.8, 1), "trainer under price (bottom fifth)": q("tk_ae", 0, 0.2),
    "sire beats price (top fifth)": q("sire_ae", 0.8, 1), "draw beats price here (top fifth)": q("draw_ae", 0.8, 1),
    "horse beats its price (top fifth)": q("h_ae", 0.8, 1), "horse under its price (bottom fifth)": q("h_ae", 0, 0.2),
    "best last-3 rating in field": (d.k_m3 >= d.k_m3.groupby(d.race_id).transform("max")).fillna(False).values,
    "rating trend up (top fifth)": q("trend", 0.8, 1), "up in distance 200m+": (d.dchg >= 200).fillna(False).values,
    "down in distance 200m+": (d.dchg <= -200).fillna(False).values, "better jockey than last time (top fifth)": q("jk_up", 0.8, 1),
    "1-2 earlier runs": d.nruns.between(1, 2).values, "20+ earlier runs": (d.nruns >= 20).values,
    # NOT usable: Betfair's MORNINGWAP column. Runners whose pre-play average sits above it win far more than the Betfair price says (ratio 1.3-1.5: 13.4% against
    # 10.3%; under 0.95: 0.8% against 11.2%), so it holds trades made after the result was known (in-play). "Morning drifters" showed +50% a year: a leak.
    "BSP 10%+ above pre-play price (at the jump)": (d.mv_bsp >= 1.10).fillna(False).values,
    "BSP 10%+ below pre-play price (at the jump)": (d.mv_bsp <= 0.90).fillna(False).values,
    "BSP 20%+ above SP (after the race)": (d.sp_ratio >= 1.2).fillna(False).values,
    "thin market (pre-play volume bottom third)": q("bf_vol", 0, 0.33), "deep market (top third)": q("bf_vol", 0.67, 1),
}
BANDS = {"any price under $30": (1, 30), "$1-3": (1, 3), "$3-6": (3, 6), "$6-10": (6, 10), "$10-20": (10, 20), "$20-50": (20, 50), "$50+": (50, 1e9)}
BM = {k: ((bsp >= a) & (bsp < c)) for k, (a, c) in BANDS.items()}
per = d.per.values
PM = [per == i for i in range(3)]
back, lay, liab, ds = d.back.values, d.lay.values, d.liab.values, d.ds.values


def stat(m, side):
    """n, ROI, t for one period mask"""
    n = int(m.sum())
    if n == 0:
        return 0, np.nan, np.nan
    if side == "back":
        x = back[m]
        return n, x.mean(), x.mean() / (x.std() / np.sqrt(n) + 1e-12)
    x, l = lay[m], liab[m]
    return n, x.sum() / l.sum(), x.mean() / (x.std() / np.sqrt(n) + 1e-12)


print("%d runners, %d races, %s to %s; periods: 2023-24 %d, 2025 %d, 2026 %d runners" % (len(d), d.race_id.nunique(), d.ds.min(), d.ds.max(), *[m.sum() for m in PM]))
print("\n===== the baseline: every runner by Betfair price band (back net of commission | lay ROI on liability) =====")
for k, m in BM.items():
    print("%-22s n=%7d win %5.1f%% (Betfair said %5.1f%%)  back before commission %+6.1f%%  back net %+6.1f%%  lay net %+6.1f%% | back net by period %s" % (
        k, m.sum(), 100 * won[m].mean(), 100 * d.pm.values[m].mean(), 100 * (won[m] * (bsp[m] - 1) - (1 - won[m])).mean(), 100 * back[m].mean(),
        100 * lay[m].sum() / liab[m].sum(), " / ".join("%+.1f%%" % (100 * back[m & p].mean()) for p in PM)))

rows = []
names = list(C)
cands = [(n,) for n in names] + list(itertools.combinations(names, 2))
for combo in cands:
    m0 = C[combo[0]] if len(combo) == 1 else (C[combo[0]] & C[combo[1]])
    if m0.sum() < 3000:
        continue
    for bk, bm in BM.items():
        if len(combo) == 2 and bk not in ("any price under $30", "$3-6", "$6-10", "$10-20"):
            continue
        m = m0 & bm
        for side in ("back", "lay"):
            if side == "lay" and bk in ("$20-50", "$50+"):
                continue
            s = [stat(m & p, side) for p in PM]
            if s[0][0] < 1500 or s[1][0] < 500 or s[2][0] < 400:
                continue
            rows.append(dict(rule=" + ".join(combo), band=bk, side=side, k=len(combo), n0=s[0][0], r0=s[0][1], t0=s[0][2], n1=s[1][0], r1=s[1][1], t1=s[1][2],
                             n2=s[2][0], r2=s[2][1], t2=s[2][2]))
R = pd.DataFrame(rows)
print("\n===== %d rules tried (%d single conditions, %d pairs; price bands; back and lay) =====" % (len(R), (R.k == 1).sum(), (R.k == 2).sum()))
for side in ("back", "lay"):
    x = R[R.side == side]
    print("%s: positive on 2023-24 %d (%.0f%%); on 2025 %d; on 2026 %d; positive in all three %d (%.1f%%); corr of ROI 2023-24 with 2025 %.2f, with 2026 %.2f" % (
        side, (x.r0 > 0).sum(), 100 * (x.r0 > 0).mean(), (x.r1 > 0).sum(), (x.r2 > 0).sum(), ((x.r0 > 0) & (x.r1 > 0) & (x.r2 > 0)).sum(),
        100 * ((x.r0 > 0) & (x.r1 > 0) & (x.r2 > 0)).mean(), x.r0.corr(x.r1), x.r0.corr(x.r2)))


def show(x, title, n=25):
    print("\n--- " + title + " ---")
    for r in x.head(n).itertuples():
        print("%-4s %-78s %-20s 2023-24 n=%6d %+6.1f%% (t %+4.1f) | 2025 n=%6d %+6.1f%% | 2026 n=%6d %+6.1f%%" % (
            r.side, r.rule[:78], r.band, r.n0, 100 * r.r0, r.t0, r.n1, 100 * r.r1, r.n2, 100 * r.r2))


for side in ("back", "lay"):
    x = R[R.side == side].sort_values("t0", ascending=False)
    show(x, "%s: the 25 best on 2023-24 (ranked there only), and what they did after" % side)
    top = x.head(50)
    print("the 50 best %s rules on 2023-24 averaged %+.1f%% there, %+.1f%% in 2025, %+.1f%% in 2026 (all %s rules: %+.1f%% / %+.1f%% / %+.1f%%)" % (
        side, 100 * top.r0.mean(), 100 * top.r1.mean(), 100 * top.r2.mean(), side, 100 * x.r0.mean(), 100 * x.r1.mean(), 100 * x.r2.mean()))
    # second stage: pick on 2023-24 AND 2025, score on 2026
    y = x[(x.t0 > 1.0) & (x.r1 > 0)].copy()
    y["t01"] = (y.r0 * y.n0 + y.r1 * y.n1) / (y.n0 + y.n1)
    print("%s rules with t over 1 on 2023-24 and positive in 2025: %d; in 2026 they average %+.1f%%, %d positive" % (side, len(y), 100 * y.r2.mean(), (y.r2 > 0).sum()))
    show(y.sort_values("t1", ascending=False), "%s: passed 2023-24 and 2025, sorted by 2025, with the untouched 2026" % side, 20)

R.to_csv(os.environ.get("RULES_OUT", "/tmp/betfair_rule_search.csv"), index=False)

# ---- detail on any rule positive in all three periods with a decent size
S = R[(R.r0 > 0) & (R.r1 > 0) & (R.r2 > 0) & (R.n0 + R.n1 + R.n2 >= 4000)].copy()
S["tot"] = (S.r0 * S.n0 + S.r1 * S.n1 + S.r2 * S.n2) / (S.n0 + S.n1 + S.n2)
print("\n===== rules positive in all three periods with 4,000+ bets: %d of %d =====" % (len(S), len(R)))
rng = np.random.default_rng(1)
for r in S.sort_values("tot", ascending=False).head(15).itertuples():
    parts = r.rule.split(" + ")
    m = C[parts[0]] & BM[r.band]
    if len(parts) == 2:
        m = m & C[parts[1]]
    x = pd.DataFrame({"ds": ds[m], "pnl": (back if r.side == "back" else lay)[m], "st": 1.0 if r.side == "back" else liab[m]})
    days = x.groupby("ds")[["pnl", "st"]].sum()
    idx = rng.integers(0, len(days), (1000, len(days)))
    bs = days.pnl.values[idx].sum(1) / days.st.values[idx].sum(1)
    o = np.sort(x.pnl.values)[::-1]
    print("%-4s %-70s %-20s n=%6d ROI %+5.1f%%  90%% range by day %+5.1f%% to %+5.1f%%  above zero %3.0f%%  without the 10 best %+5.1f%%" % (
        r.side, r.rule[:70], r.band, len(x), 100 * x.pnl.sum() / x.st.sum(), 100 * np.quantile(bs, 0.05), 100 * np.quantile(bs, 0.95), 100 * (bs > 0).mean(),
        100 * (x.pnl.sum() - (o[:10].sum() if r.side == "back" else 0)) / x.st.sum()))
