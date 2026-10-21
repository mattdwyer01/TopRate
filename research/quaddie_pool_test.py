"""Quaddie pool test (21 Oct 2026): for each paid Quaddie / EarlyQuaddie in tab_dividends.csv (2 to 21 Oct 2026), build each leg's pool from the projection
logged before the race (runners.csv wprp_proj, wprp_made before the start) and compare pool rules on hit rate, combinations and dividend return
(dividend per $1 combination, as TAB lists it). Run with PYTHONPATH=."""
import itertools, re
import numpy as np, pandas as pd
import runners_io

from projection import projlog
r = pd.read_csv(runners_io.live_path(), low_memory=False, usecols=["run_id","venue","race","date","start_time","tab_number","scratched","field_source"])
r["date"] = r.date.astype(str).str[:10]
r["race"] = pd.to_numeric(r.race, errors="coerce")
nv = lambda s: re.sub(r"\s+", " ", str(s).split("@")[-1].strip().lower())
r["v"] = r.venue.map(nv)
r = r[~r.field_source.astype(str).str.contains("not in toprate", na=False)]
r = r[r.scratched.fillna(0) != 1].copy()
r["run_id"] = pd.to_numeric(r.run_id, errors="coerce")
lg = projlog.load()[["run_id","proj","made","src"]].copy()
lg["made_t"] = pd.to_datetime(lg.made, utc=True, errors="coerce")
r["st"] = pd.to_datetime(r.start_time, utc=True, errors="coerce")
m = r.merge(lg, on="run_id", how="left")
# sample A: the last LIVE projection made before the jump; sample B adds out-of-sample back-fill (older model scale) where no live pre-jump row exists
live = m[(m.src == "live") & (m.made_t <= m.st)].sort_values("made_t").drop_duplicates("run_id", keep="last")
oos = m[m.src == "oos"].sort_values("made_t").drop_duplicates("run_id", keep="last")
r = r.merge(live[["run_id","proj"]].rename(columns={"proj":"proj_live"}), on="run_id", how="left").merge(oos[["run_id","proj"]].rename(columns={"proj":"proj_oos"}), on="run_id", how="left")
import sys
SAMPLE = sys.argv[1] if len(sys.argv) > 1 else "live"
r["proj"] = r.proj_live if SAMPLE == "live" else r.proj_live.where(r.proj_live.notna(), r.proj_oos)
print("sample:", SAMPLE)
r["pre"] = True
d = pd.read_csv("tab_dividends.csv")
q = d[d["product"].isin(["Quaddie", "EarlyQuaddie"])].drop_duplicates(["date", "venue", "race_no", "product"]).copy()
q["v"] = q.venue.map(nv)
rows = []
for _, x in q.iterrows():
    if not re.match(r"^\d+/\d+/\d+/\d+$", str(x.selections)): continue
    win = [int(s) for s in x.selections.split("/")]
    legs = []
    ok = True
    for i, rn in enumerate(range(int(x.race_no) - 3, int(x.race_no) + 1)):
        f = r[(r.date == x.date) & (r.v == x.v) & (r.race == rn)]
        if len(f) < 4 or f.proj.notna().sum() < 3 or not f.pre[f.proj.notna()].all(): ok = False; break
        legs.append(f.dropna(subset=["proj"]).sort_values("proj", ascending=False).reset_index(drop=True))
    if not ok: continue
    rows.append((x, win, legs))
print(len(q), "paid quaddies,", len(rows), "with all four legs projected before the jump")

def pool(f, rule):
    top = f.proj.iloc[0]; gap = top - f.proj; n = len(f)
    kind, k = rule
    if kind == "top": return f.iloc[:k]
    if kind == "gap": return f[gap <= k]
    if kind == "mix":  # standout (lead of k2 over the second) -> single, else inside 4
        lead = f.proj.iloc[0] - f.proj.iloc[1]
        return f.iloc[:1] if lead >= k else f[gap <= 4]
    if kind == "mix2":  # standout -> single, tight (inside 2) -> inside 2, else inside 6
        lead = f.proj.iloc[0] - f.proj.iloc[1]
        return f.iloc[:1] if lead >= k else f[gap <= 6]
    if kind == "cap":  # inside 4 but at most k runners
        return f[gap <= 4].iloc[:k]
def run(rule):
    cost = 0; ret = 0; hits = 0; n = 0; sizes = []
    for x, win, legs in rows:
        ps = [pool(f, rule) for f in legs]
        c = int(np.prod([len(p) for p in ps])); cost += c; n += 1; sizes += [len(p) for p in ps]
        if all(w in set(p.tab_number.astype(int)) for w, p in zip(win, ps)): hits += 1; ret += x.amount
    if not n: return 0,0,np.nan,np.nan,np.nan,0
    run.last = (cost, ret, hits)
    return n, hits, cost / n, np.mean(sizes), 100 * ret / cost - 100 if cost else np.nan, ret
print(f"{'rule':24s} {'n':>4s} {'hit':>4s} {'hit%':>6s} {'combos/qd':>10s} {'runners/leg':>11s} {'ROI%':>8s}")
for rule in [("top",1),("top",2),("top",3),("top",4),("gap",2),("gap",3),("gap",4),("gap",6),("mix",4),("mix",6),("mix2",4),("mix2",6),("cap",3),("cap",4)]:
    n, h, c, s, roi, ret = run(rule)
    print(f"{str(rule):24s} {n:4d} {h:4d} {100*h/n:6.1f} {c:10.1f} {s:11.2f} {roi:8.1f}")
# dividends hit by inside-4: how big

# robustness: ROI without the largest-dividend hit, and a random-pool baseline with the same pool sizes
rng = np.random.default_rng(7)
def rnd(rule, reps=300):
    out = []
    for _ in range(reps):
        cost = 0; ret = 0
        for x, win, legs in rows:
            ps = [pool(f, rule) for f in legs]
            c = int(np.prod([len(p) for p in ps])); cost += c
            if all(w in set(f.sample(len(p), random_state=int(rng.integers(1e9))).tab_number.astype(int)) for w, p, f in zip(win, ps, legs)): ret += x.amount
        out.append(100 * ret / cost - 100)
    return np.mean(out)
print("\nrule  hits  ROI%  ROI% without the biggest hit  random same-size pools ROI%  mean dividend of hits")
for rule in [("top",2),("top",4),("gap",4),("gap",6),("mix2",4)]:
    hs = []; cost = 0
    for x, win, legs in rows:
        ps = [pool(f, rule) for f in legs]; cost += int(np.prod([len(p) for p in ps]))
        if all(w in set(p.tab_number.astype(int)) for w, p in zip(win, ps)): hs.append(x.amount)
    tot = sum(hs); ex = tot - (max(hs) if hs else 0)
    print(rule, len(hs), round(100*tot/cost-100,1), round(100*ex/cost-100,1), round(rnd(rule, 60),1), round(np.mean(hs),0) if hs else None)
