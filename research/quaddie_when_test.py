"""When to play a quaddie (22 Oct 2026). Every late and early quaddie window (last four races, and the four ending at race max(4, N-4)) in 1 Jul to 22 Oct 2026 where all four
legs have Rating (live 50/30/20 blend of Proj, Nett, Spd), starting prices and a result, so it needs no dividends. Pool per leg = runners within GAP Rating points of the top. In a
pari-mutuel pool the expected return of a pool is (1 - takeout) x (actual hit rate / market-implied hit rate), so the test statistic is R = hits / sum of implied hit probabilities,
where a leg's implied chance is the sum of the pool runners' normalised SP chances and the quaddie's is their product. R above 1 / (1 - takeout) means value. Takeout is calibrated from
paid quaddies in tab_dividends.csv (dividend per $1 against 1 / product of the winners' normalised SP chances). Same data prep as rank_weights.py. Run with PYTHONPATH=."""
import re, sys
from datetime import date
import numpy as np, pandas as pd
import speed_rating as sr

GAP = float(sys.argv[1]) if len(sys.argv) > 1 else 4.0
W = (0.5, 0.3, 0.2)
KEY = ["date", "venue", "race", "horse"]
cols = KEY + ["wpr_nett", "wprp_proj", "scratched", "won", "fixed_win_price", "starting_price_sp", "field_source", "spd_fig", "tab_number", "state", "prize_money", "distance", "weight_carried", "horse_id", "jockey"]
rd = lambda p: pd.read_csv(p, low_memory=False, usecols=lambda c: c in cols)
leg = pd.concat([rd("archive/toprate/toprate_runners_archive.csv.gz"), rd("archive/toprate/toprate_runners.csv")], ignore_index=True)
cur = pd.concat([rd("runners_archive.csv.gz"), rd("runners.csv")], ignore_index=True)
for x in (leg, cur):
    x["date"] = x["date"].astype(str).str[:10]; x["race"] = x["race"].astype(str)
d = leg.drop_duplicates(KEY, keep="last").set_index(KEY).combine_first(cur.drop_duplicates(KEY, keep="last").set_index(KEY)).reset_index()
d = d[(d.date >= "2026-07-01") & (d.date <= "2026-10-22")]
d = d[(d.scratched.fillna(0) != 1) & ~d.field_source.astype(str).str.contains("not in toprate", na=False)].reset_index(drop=True)
d["spd"] = sr.compute(d, today=date(2026, 8, 1)).where(lambda s: s.notna(), pd.to_numeric(d.spd_fig, errors="coerce"))
nv = lambda s: re.sub(r"\s+", " ", str(s).split("@")[-1].strip().lower())
d["v"] = d.venue.map(nv); d["rn"] = pd.to_numeric(d.race, errors="coerce"); d["tab"] = pd.to_numeric(d.tab_number, errors="coerce")
d["price"] = pd.to_numeric(d.starting_price_sp, errors="coerce")
d["price"] = d.price.where(d.price > 1, pd.to_numeric(d.fixed_win_price, errors="coerce"))
for c in ("wpr_nett", "wprp_proj", "won"): d[c] = pd.to_numeric(d[c], errors="coerce")
d["rk"] = d.date + "|" + d.v + "|" + d.rn.astype("Int64").astype(str)
g = d.groupby("rk")
ok = (g.won.transform("sum") == 1) & g.won.transform(lambda s: s.notna().all()) & g.price.transform(lambda s: s.notna().all())
book = g.price.transform(lambda s: (1 / s).sum())
ok &= (book >= 1.05) & (book <= 2.0) & (g.won.transform("size") >= 5)
nraces = d.groupby(["date", "v"]).rn.max()
d = d[ok].copy()
d["imp"] = (1 / d.price) / d.groupby("rk").price.transform(lambda s: (1 / s).sum())

def rate(f):
    z = {}
    for k, c in (("p", "wprp_proj"), ("n", "wpr_nett"), ("s", "spd")):
        v = f[c]; sd = v.std()
        z[k] = (v - v.mean()) / sd if v.notna().sum() >= 2 and sd and sd > 1e-9 else pd.Series(np.nan, index=f.index)
    n_sig = sum(z[k].notna().astype(int) for k in "pns")
    num = sum(w * z[k].fillna(0) for w, k in zip(W, "pns")); den = sum(w * z[k].notna() for w, k in zip(W, "pns"))
    score = (num / den.where(den > 0)).where(n_sig >= 2)
    psd = f.wprp_proj.std(); psd = psd if psd and psd > 0 else 1.0
    out = f.assign(rating=f.wprp_proj.mean() + score * psd)
    return out[out.rating.notna()].sort_values("rating", ascending=False).reset_index(drop=True)

races = {}
for rk, f in d.groupby("rk"):
    if f.wprp_proj.notna().sum() >= 3:
        r_ = rate(f)
        if len(r_) >= 4: races[rk] = (r_, float(f[f.won == 1].imp.iloc[0]))
print(len(races), "complete rated races")
rows = []
for (dt, v), n in nraces.items():
    if n < 4: continue
    wins = [("late", n)]
    if n >= 6: wins.append(("early", max(4, n - 4)))
    for kind, last in wins:
        keys = [f"{dt}|{v}|{k}" for k in range(int(last) - 3, int(last) + 1)]
        if not all(k in races for k in keys): continue
        gs = [races[k][0] for k in keys]; wps = [races[k][1] for k in keys]
        pools = [g_[(g_.rating.iloc[0] - g_.rating) <= GAP] for g_ in gs]
        S = [p.imp.sum() for p in pools]
        hit = all(len(g_[g_.won == 1]) and int(g_[g_.won == 1].index[0]) in set(p.index) for g_, p in zip(gs, pools))
        singles = sum(len(p) == 1 for p in pools)
        rows.append(dict(date=dt, v=v, kind=kind, combos=int(np.prod([len(p) for p in pools])), M=float(np.prod(S)), hit=int(hit), singles=singles,
                         maxleg=max(len(p) for p in pools), field=np.mean([len(g_) for g_ in gs]), favp=float(np.prod([g_.imp.max() for g_ in gs])),
                         prize=pd.to_numeric(gs[0].prize_money, errors="coerce").iloc[0], state=str(gs[0].state.iloc[0]),
                         winp=float(np.prod(wps))))
q = pd.DataFrame(rows)
print(len(q), "quaddie windows")

# takeout calibration on paid quaddies
dv = pd.read_csv("tab_dividends.csv"); dv = dv[dv["product"].isin(["Quaddie", "EarlyQuaddie"])].drop_duplicates(["date", "venue", "race_no", "product"])
dv["v"] = dv.venue.map(nv)
cal = []
for _, x in dv.iterrows():
    if not re.match(r"^\d+/\d+/\d+/\d+$", str(x.selections)): continue
    kind = "early" if x["product"] == "EarlyQuaddie" else "late"
    m_ = q[(q.date == x.date) & (q.v == x.v) & (q.kind == kind)]
    if len(m_): cal.append(x.amount * m_.winp.iloc[0])
print(f"takeout calibration: mean(dividend x product of winners' implied chances) = {np.mean(cal):.2f} over {len(cal)} paid quaddies (that is about 1 - takeout; below 1 means the pool pays less than the SP chances imply)")

def tab(df, by):
    out = []
    for k, s in df.groupby(by, observed=True):
        out.append((k, len(s), s.hit.sum(), 100 * s.hit.mean(), 100 * s.M.mean(), s.hit.sum() / s.M.sum() if s.M.sum() else np.nan, s.combos.mean()))
    print(f"{'':16s} {'n':>5s} {'hits':>5s} {'hit%':>6s} {'implied%':>9s} {'R':>6s} {'combos':>7s}")
    for k, n, h, hp, mp, R, c in out: print(f"{str(k):16s} {n:5d} {h:5d} {hp:6.1f} {mp:9.1f} {R:6.2f} {c:7.1f}")
q["all"] = "all"
print(f"\nGAP {GAP:g}"); tab(q, "all")
q["comboB"] = pd.cut(q.combos, [0, 16, 64, 256, 1024, 1e9], labels=["<=16", "17-64", "65-256", "257-1024", ">1024"])
q["fieldB"] = pd.cut(q.field, [0, 9, 11, 13, 99], labels=["<9", "9-11", "11-13", "13+"])
q["favB"] = pd.qcut(q.favp, 4, labels=["fav product low", "q2", "q3", "fav product high"])
q["MB"] = pd.qcut(q.M, 4, labels=["implied low", "q2", "q3", "implied high"])
q["prizeB"] = pd.cut(q.prize.fillna(0), [-1, 0, 30000, 80000, 1e9], labels=["no prize", "<30k", "30-80k", "80k+"])
for name, by in (("combinations", "comboB"), ("singles in the pool", "singles"), ("biggest leg pool", "maxleg"), ("average field size", "fieldB"), ("favourites' joint chance", "favB"),
                 ("market-implied hit chance of the pool", "MB"), ("meeting prize money", "prizeB"), ("late or early", "kind")):
    print(f"\nby {name}"); tab(q, by)
q.to_csv("/tmp/quaddie_when.csv", index=False)

# robustness of the small-pool rule: halves and a bootstrap of R (expected ROI = takeout factor x R - 1)
TF = float(np.mean(cal))
rng = np.random.default_rng(3)
def Rci(s, reps=2000):
    h = s.hit.values; m = s.M.values; idx = np.arange(len(s))
    rs = [h[i].sum() / m[i].sum() for i in (rng.choice(idx, len(idx)) for _ in range(reps))]
    return np.percentile(rs, [5, 95])
q = q.sort_values("date").reset_index(drop=True)
mid = q.date.iloc[len(q) // 2]
print(f"\nrule check (takeout factor {TF:.2f}, break-even R {1 / TF:.2f}); halves split at {mid}")
print(f"{'rule':22s} {'n':>5s} {'hits':>5s} {'R':>6s} {'R 5-95%':>13s} {'exp ROI':>8s} {'R 1st half':>10s} {'R 2nd half':>10s}")
for lab, s in (("combos <= 16", q[q.combos <= 16]), ("combos <= 32", q[q.combos <= 32]), ("combos <= 64", q[q.combos <= 64]), ("combos <= 128", q[q.combos <= 128]), ("combos <= 256", q[q.combos <= 256]),
               ("combos <= 500", q[q.combos <= 500]), ("combos > 500", q[q.combos > 500]), ("combos <= 64 or >=1 single", q[(q.combos <= 64) | (q.singles >= 1)]), ("all windows", q)):
    a, b = s[s.date < mid], s[s.date >= mid]
    lo, hi = Rci(s)
    R = s.hit.sum() / s.M.sum()
    print(f"{lab:22s} {len(s):5d} {s.hit.sum():5d} {R:6.2f} {lo:6.2f}-{hi:5.2f} {100 * (TF * R - 1):7.1f}% {a.hit.sum() / a.M.sum():10.2f} {b.hit.sum() / b.M.sum():10.2f}")

# direct dividend check on the paid quaddies (2 to 22 Oct only): flat $1 per combination
paid = []
for _, x in dv.iterrows():
    if not re.match(r"^\d+/\d+/\d+/\d+$", str(x.selections)): continue
    kind = "early" if x["product"] == "EarlyQuaddie" else "late"
    m_ = q[(q.date == x.date) & (q.v == x.v) & (q.kind == kind)]
    if len(m_): paid.append(dict(combos=m_.combos.iloc[0], hit=m_.hit.iloc[0], amt=x.amount))
paid = pd.DataFrame(paid)
print("\ndirect dividend ROI on paid quaddies (flat $1 per combination)")
for lab, s in (("combos <= 16", paid[paid.combos <= 16]), ("combos <= 32", paid[paid.combos <= 32]), ("combos <= 64", paid[paid.combos <= 64]), ("combos <= 128", paid[paid.combos <= 128]), ("combos <= 500", paid[paid.combos <= 500]), ("all paid", paid)):
    if len(s): print(f"{lab:16s} n {len(s):4d} hits {int(s.hit.sum()):3d} cost {s.combos.sum():8.0f} return {(s.hit * s.amt).sum():8.0f} ROI {100 * ((s.hit * s.amt).sum() / s.combos.sum() - 1):7.1f}%")
