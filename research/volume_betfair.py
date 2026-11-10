"""Volume rules at Betfair starting prices, and a sweep of rule variants (10 Nov 2026).
Run with PYTHONPATH=.:research python research/volume_betfair.py
Selection uses what is known before the jump (trip map forecast, Proj, the TAB fixed price); the payout is the Betfair
starting price after commission (10% NSW, 8% elsewhere). A Betfair SP bet can carry a minimum price, so a floor on the
BSP itself is also a usable rule. Window: the days trip_map.json and data/trip_map_archive still hold (about 5 weeks),
so every figure here is a small sample and the variants are many: read the spread of results, not the best cell."""
import glob, gzip, itertools, json, os, sys, warnings
import numpy as np, pandas as pd
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import volume_rules as V
from betfair_bsp_test import load_bsp, norm, nsw_flag, COMM_NSW, COMM_OTHER
warnings.filterwarnings("ignore")

gaps, _ = V.read_gaps()
pft = V.read_pft()
for f in sorted(glob.glob("data/trip_map_archive/*.json.gz")):
    t = json.load(gzip.open(f, "rt"))
    for v in t.get("races", {}).values():
        for r in v.get("runners", []):
            if r.get("gap") is not None:
                gaps.setdefault(str(r["rid"]), float(r["gap"]))
            if r.get("pft") is not None:
                pft.setdefault(str(r["rid"]), float(r["pft"]))
df = V.read_runners()
d, rc = V.evaluate(df, gaps, "fixed", V.read_overrides(), pft)
b = load_bsp()
d["hn"] = d.horse.map(norm)
d = d.merge(b[["date", "hn", "bsp", "win_lose", "ppwap"]], on=["date", "hn"], how="left")
d["comm"] = np.where(nsw_flag(d.venue), COMM_NSW, COMM_OTHER)
d["sp_final"] = V.num(d["starting_price_sp"])
g = d.groupby("race_id")
d["nb"] = g.bsp.transform("count")
d["nw"] = g.win_lose.transform("sum")
d["fav"] = d.bsp == g.bsp.transform("min")
d["pm"] = (1 / d.bsp) / g.bsp.transform(lambda x: (1 / x).sum())
R = d[d.race_ok & (d.nb == d.n) & (d.nw == 1)].copy()          # eligible races that ran, every runner with a Betfair price
R["won"] = R.win_lose
R["going_n"] = V.num(R.going.astype(str).str.extract(r"(\d+)")[0])
print("eligible races with Betfair prices: %d, runners %d, %s to %s" % (R.race_id.nunique(), len(R), R.date.min(), R.date.max()))


def stats(x, price="bsp", per_race=True):
    """$25 a race split equally over the race's bets (per_race) or $1 a bet; Betfair pays after commission."""
    if len(x) == 0:
        return None
    st = 25.0 / x.groupby("race_id").race_id.transform("size") if per_race else pd.Series(1.0, index=x.index)
    net = (x[price] - 1) * ((1 - x.comm) if price in ("bsp", "ppwap") else 1.0)
    pnl = st * (x.won * net - (1 - x.won))
    days = pd.DataFrame({"p": pnl, "s": st, "d": x.date}).groupby("d").sum()
    rng = np.random.default_rng(7)
    bs = np.array([(lambda s_: s_.p.sum() / s_.s.sum())(days.sample(len(days), replace=True, random_state=int(rng.integers(1e9)))) for _ in range(600)])
    mid = np.sort(x.date.values)[len(x) // 2]
    h1, h2 = x.date < mid, x.date >= mid
    o = np.sort(pnl.values)[::-1]
    return dict(races=x.race_id.nunique(), bets=len(x), win=x.won.mean(), impl=x.pm.mean(), avg=x[price].mean(), roi=pnl.sum() / st.sum(),
                h1=pnl[h1].sum() / max(st[h1].sum(), 1e-9), h2=pnl[h2].sum() / max(st[h2].sum(), 1e-9), ex3=(pnl.sum() - o[:3].sum()) / st.sum(),
                ex10=(pnl.sum() - o[:10].sum()) / st.sum(), p0=(bs > 0).mean(), lo=np.quantile(bs, 0.05), hi=np.quantile(bs, 0.95))


def line(label, x, price="bsp", per_race=True):
    s = stats(x, price, per_race)
    if s is None:
        return "%-58s no bets" % label
    return "%-58s %4d races %5d bets win %5.1f%% (Betfair %5.1f%%) avg $%5.2f ROI %+6.1f%% [%+5.1f, %+5.1f] P>0 %3.0f%% halves %+6.1f/%+6.1f ex3 %+6.1f ex10 %+6.1f" % (
        label, s["races"], s["bets"], 100 * s["win"], 100 * s["impl"], s["avg"], 100 * s["roi"], 100 * s["lo"], 100 * s["hi"], 100 * s["p0"],
        100 * s["h1"], 100 * s["h2"], 100 * s["ex3"], 100 * s["ex10"])


print("\n===== the three rules as they stand =====")
for r in ("v1", "v2", "v3"):
    x = R[R[r]]
    print(line(r + " at the TAB fixed price", x.assign(sp=x.price), "price"))
    print(line(r + " at the starting price", x[x.sp_final > 1], "sp_final"))
    print(line(r + " at Betfair SP after commission", x))
    print(line(r + " at Betfair, $1 a bet", x, per_race=False))
print(line("every runner in eligible races (reference)", R, per_race=False))
print(line("favourites in eligible races (reference)", R[R.fav], per_race=False))

print("\n===== v1 by one cut at a time (Betfair after commission, $25 a race) =====")
x = R[R.v1]
for lab, m in (("Betfair price $3-6", x.bsp.between(3, 6)), ("$6-10", x.bsp.between(6, 10)), ("$10-20", x.bsp.between(10, 20)), ("$20+", x.bsp >= 20),
               ("field 5-7", x.n <= 7), ("field 8-11", x.n.between(8, 11)), ("field 12+", x.n >= 12),
               ("NSW", x.comm == COMM_NSW), ("other states", x.comm != COMM_NSW),
               ("top rated itself", x.off <= 1e-9), ("0-2 off the top", (x.off > 1e-9) & (x.off <= 2)), ("2-4 off the top", x.off > 2),
               ("forecast leader", x.rk == 1), ("forecast 2nd or 3rd", x.rk.between(2, 3)), ("further back in the first third", x.rk > 3),
               ("Betfair above the fixed price by 10%+", x.bsp >= 1.1 * x.price), ("Betfair within 10% of fixed", (x.bsp < 1.1 * x.price) & (x.bsp > 0.9 * x.price)),
               ("Betfair 10%+ below fixed (firmed)", x.bsp <= 0.9 * x.price),
               ("good or firm", x.going_n <= 4), ("soft or heavy", x.going_n >= 5),
               ("meeting lowest race prize $30k+", V.num(x.meet_min) >= 30000), ("under $30k", V.num(x.meet_min) < 30000)):
    print(line("  " + lab, x[m.fillna(False)]))

print("\n===== sweep: settle cut x points off the top x price floor x price cap x minimum field =====")
rows = []
for settle, off, floor, cap, fmin in itertools.product((0.25, 1 / 3, 0.5), (1, 2, 4, 6), (2, 3, 4, 5), (15, 30, 1001), (5, 8, 10)):
    x = R[(R.sp <= settle + 1e-9) & (R.off <= off + 1e-9) & (R.price > floor) & (R.bsp < cap) & (R.n >= fmin)]
    s = stats(x)
    if s and s["races"] >= 120:
        rows.append(dict(settle=round(settle, 2), off=off, floor=floor, cap=cap, fmin=fmin, **s))
S = pd.DataFrame(rows)
print("%d variants with 120+ races; ROI median %+.1f%%, positive %d%%, positive in both halves %d%%, positive without the 10 best bets %d%%" % (
    len(S), 100 * S.roi.median(), 100 * (S.roi > 0).mean(), 100 * ((S.h1 > 0) & (S.h2 > 0)).mean(), 100 * (S.ex10 > 0).mean()))
for k in ("settle", "off", "floor", "cap", "fmin"):
    print("  median ROI by %-6s: %s" % (k, "  ".join("%s %+.1f%%" % (v, 100 * q) for v, q in S.groupby(k).roi.median().items())))
rob = S[(S.h1 > 0) & (S.h2 > 0) & (S.ex10 > 0)].sort_values("roi", ascending=False)
pd.set_option("display.width", 250)
print("variants positive in both halves and without the 10 best bets: %d" % len(rob))
cols = ["settle", "off", "floor", "cap", "fmin", "races", "bets", "win", "impl", "avg", "roi", "lo", "hi", "p0", "h1", "h2", "ex3", "ex10"]
print(rob[cols].head(15).round(3).to_string(index=False))

# honest check of 'pick the best': choose the best variant on the first half of the days, score it on the second
days = np.sort(R.date.unique())
cut = days[len(days) // 2]
A, B = R[R.date < cut], R[R.date >= cut]
out = []
for settle, off, floor, cap, fmin in itertools.product((0.25, 1 / 3, 0.5), (1, 2, 4, 6), (2, 3, 4, 5), (15, 30, 1001), (5, 8, 10)):
    f = lambda Z: Z[(Z.sp <= settle + 1e-9) & (Z.off <= off + 1e-9) & (Z.price > floor) & (Z.bsp < cap) & (Z.n >= fmin)]
    a, bb = stats(f(A)), stats(f(B))
    if a and bb and a["races"] >= 60 and bb["races"] >= 60:
        out.append((a["roi"], bb["roi"]))
out = np.array(out)
top = out[np.argsort(-out[:, 0])[:20]]
print("\nchosen on the first half, scored on the second (days before / from %s): the 20 best first-half variants made %+.1f%% then and %+.1f%% after; all variants %+.1f%% and %+.1f%%; corr %.2f" % (
    cut, 100 * top[:, 0].mean(), 100 * top[:, 1].mean(), 100 * out[:, 0].mean(), 100 * out[:, 1].mean(), np.corrcoef(out[:, 0], out[:, 1])[0, 1]))
R.to_pickle("/tmp/volume_betfair_R.pkl")
