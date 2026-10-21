"""Quaddie pools under a combination cap (22 Oct 2026). Per leg: every runner within GAP Rating points of the top Rating (the live 50/30/20 blend of Proj, Nett and Spd,
Rating = race mean Proj + score x race Proj sd), plus the top Spd runner if it is not already inside. If the pool's combinations exceed the cap, runners are dropped, largest gap
from the leg top first, never a leg's top Rating runner, until it fits. Dividends are per $1 combination from tab_dividends.csv (Quaddie and EarlyQuaddie, 2 to 22 Oct 2026).
Projection: the last live one made before the jump, else the out-of-sample back-fill (SAMPLE=all, older model scale). Run with PYTHONPATH=. python research/quaddie_cap_test.py [live|all]"""
import re, sys
import numpy as np, pandas as pd
import runners_io
from projection import projlog

SAMPLE = sys.argv[1] if len(sys.argv) > 1 else "all"
W = (0.5, 0.3, 0.2)  # Proj, Nett, Spd
GAP = 4.0
CAPS = [16, 32, 64, 128, 256, 500, None]
nv = lambda s: re.sub(r"\s+", " ", str(s).split("@")[-1].strip().lower())
cols = ["run_id", "venue", "race", "date", "start_time", "tab_number", "scratched", "field_source", "wpr_nett", "spd_fig"]
r = pd.read_csv(runners_io.live_path(), low_memory=False, usecols=cols)
r["date"] = r.date.astype(str).str[:10]; r["race"] = pd.to_numeric(r.race, errors="coerce"); r["v"] = r.venue.map(nv)
r = r[~r.field_source.astype(str).str.contains("not in toprate", na=False)]
r = r[r.scratched.fillna(0) != 1].copy()
r["run_id"] = pd.to_numeric(r.run_id, errors="coerce")
lg = projlog.load()[["run_id", "proj", "made", "src", "model"]].copy()
lg["made_t"] = pd.to_datetime(lg.made, utc=True, errors="coerce")
r["st"] = pd.to_datetime(r.start_time, utc=True, errors="coerce")
m = r.merge(lg, on="run_id", how="left")
live = m[(m.src == "live") & (m.made_t <= m.st)].sort_values("made_t").drop_duplicates("run_id", keep="last")
oos = m[m.src == "oos"].sort_values("made_t").drop_duplicates("run_id", keep="last")
r = r.merge(live[["run_id", "proj", "model"]].rename(columns={"proj": "p_live", "model": "m_live"}), on="run_id", how="left").merge(oos[["run_id", "proj"]].rename(columns={"proj": "p_oos"}), on="run_id", how="left")
r["proj"] = r.p_live if SAMPLE == "live" else r.p_live.where(r.p_live.notna(), r.p_oos)
r["tab"] = pd.to_numeric(r.tab_number, errors="coerce")
for c in ("wpr_nett", "spd_fig"): r[c] = pd.to_numeric(r[c], errors="coerce")

def rate(f):
    """Rating and Spd rank for one race's runners (needs 2 of 3 signals, as in lib/combinedRank.ts)."""
    z = {}
    for k, c in (("p", "proj"), ("n", "wpr_nett"), ("s", "spd_fig")):
        v = f[c]; sd = v.std()
        z[k] = (v - v.mean()) / sd if v.notna().sum() >= 2 and sd and sd > 1e-9 else pd.Series(np.nan, index=f.index)
    num = sum(w * z[k].fillna(0) for w, k in zip(W, "pns")); den = sum(w * z[k].notna() for w, k in zip(W, "pns"))
    ok = den > 0
    n_sig = sum(z[k].notna().astype(int) for k in "pns")
    score = (num / den).where(n_sig >= 2)
    psd = f.proj.std(); pm = f.proj.mean()
    out = f.assign(score=score, rating=pm + score * (psd if psd and psd > 0 else 1.0))
    return out[out.score.notna()].sort_values("rating", ascending=False).reset_index(drop=True)

d = pd.read_csv("tab_dividends.csv")
q = d[d["product"].isin(["Quaddie", "EarlyQuaddie"])].drop_duplicates(["date", "venue", "race_no", "product"]).copy()
q["v"] = q.venue.map(nv)
rows = []
for _, x in q.iterrows():
    if not re.match(r"^\d+/\d+/\d+/\d+$", str(x.selections)): continue
    win = [int(s) for s in x.selections.split("/")]; legs = []; ok = True
    for rn in range(int(x.race_no) - 3, int(x.race_no) + 1):
        f = r[(r.date == x.date) & (r.v == x.v) & (r.race == rn)]
        if len(f) < 4 or f.proj.notna().sum() < 3: ok = False; break
        g = rate(f)
        if len(g) < 3 or not set(g.tab.dropna().astype(int)) >= {win[len(legs)]} and False: ok = False; break
        legs.append(g)
    if ok: rows.append((x, win, legs))
print(f"sample={SAMPLE}: {len(q)} paid quaddies, {len(rows)} with all four legs rated")

def build(legs, cap, mode):
    pools = []
    for g in legs:
        top = g.rating.iloc[0]
        keep = list(g.index[(top - g.rating) <= GAP])
        if mode == "gap+spd":
            s = g.dropna(subset=["spd_fig"])
            if len(s): keep.append(s.spd_fig.idxmax())
        pools.append(sorted(set(keep)))
    if cap:
        while int(np.prod([len(p) for p in pools])) > cap:
            cand = [(g.rating.iloc[0] - g.rating[i], li, i) for li, (g, p) in enumerate(zip(legs, pools)) for i in p if i != 0 and len(p) > 1]
            if not cand: break
            _, li, i = max(cand); pools[li].remove(i)
    return pools

def run(cap, mode, rnd=None):
    cost = ret = hits = 0; hs = []
    for x, win, legs in rows:
        pools = build(legs, cap, mode)
        c = int(np.prod([len(p) for p in pools])); cost += c
        if rnd is not None:
            ok = all(w in set(g.sample(len(p), random_state=int(rnd.integers(1e9))).tab.astype(int)) for w, g, p in zip(win, legs, pools))
        else:
            ok = all(w in set(g.loc[p].tab.astype(int)) for w, g, p in zip(win, legs, pools))
        if ok: hits += 1; ret += x.amount; hs.append(x.amount)
    n = len(rows); ex = ret - (max(hs) if hs else 0)
    return n, hits, cost / n, 100 * ret / cost - 100, 100 * ex / cost - 100, (np.mean(hs) if hs else np.nan), cost

rng = np.random.default_rng(11)
for mode in ("gap", "gap+spd"):
    print(f"\n{mode}: within {GAP:g} Rating points" + (" plus the top Spd runner" if mode == "gap+spd" else ""))
    print(f"{'cap':>6s} {'n':>4s} {'hit':>4s} {'hit%':>6s} {'combos/qd':>10s} {'ROI%':>8s} {'ROI ex1':>8s} {'avg div':>8s} {'random ROI%':>12s}")
    for cap in CAPS:
        n, h, c, roi, ex, md, cost = run(cap, mode)
        rr = np.mean([run(cap, mode, rng)[3] for _ in range(40)])
        print(f"{str(cap or 'none'):>6s} {n:4d} {h:4d} {100*h/n:6.1f} {c:10.1f} {roi:8.1f} {ex:8.1f} {md:8.0f} {rr:12.1f}")
