"""Spd pools for boxed trifecta / first four: how often the Spd top N (or everyone within X pts of the top Spd) holds the first 3 / first 4, what it costs,
and which pre-race conditions make it pay. Prompted by Geelong R6 21 Oct 2026 (top 5-6 on Spd ran 1-4: box trifecta $60-120 returned $382.50, box first four
$120-360 returned $8,381.90).
Part A (results files 2025-07 to 8 Oct 2026, spd from speed_exotics_build.py): capture rate against the random-pool baseline, cost per $1 unit, and an
return is NOT estimated (a Harville estimate of the dividend blew up on first-four tails and was dropped; see speed_exotics_edge.py for the market-relative test). Part B (tab_dividends.csv, 2 to 21 Oct 2026, spd_fig
from runners.csv): the real boxed returns. Slices are fitted on 2025-07..2026-01 and checked on 2026-02+ (par model is out of sample from 2026-01).
usage: PYTHONPATH=. python research/speed_exotics_nuggets.py SPD_RACES.csv.gz
"""
import sys
from itertools import permutations
from math import comb, perm

import numpy as np
import pandas as pd

PTS = 1.33        # displayed Spd points per length (speedRatingOnScale)


def load(path):
    d = pd.read_csv(path, low_memory=False)
    d["pts"] = d["spd_len"] * PTS
    d["sp"] = pd.to_numeric(d["priceStarting"], errors="coerce")
    d["pos"] = pd.to_numeric(d["positionFinish"], errors="coerce")
    return d


def harville(p, order):
    out, left = 1.0, 1.0
    for i in order:
        out *= p[i] / left
        left -= p[i]
        if left <= 1e-9:
            return np.nan
    return out


def race_rows(g, model_k=None):
    """One dict per race, or None when the finishing order is not clean."""
    g = g.dropna(subset=["pos"])
    top = g[g.pos.between(1, 4)]
    if len(g) < 6 or sorted(top.pos.tolist()) != [1, 2, 3, 4]:
        return None
    g = g.sort_values("pts", ascending=False, na_position="last").reset_index(drop=True)
    rated = g.pts.notna()
    n_rated = int(rated.sum())
    if n_rated < 5:
        return None
    pts = g.pts.values
    top_pts = pts[0]
    pos = g.pos.values
    r = dict(race=g.race_id.iloc[0], date=g.date.iloc[0], field=len(g), n_rated=n_rated, track=g.track.iloc[0], dist=g.distance.iloc[0],
             going=str(g.going.iloc[0]), cls=str(g.race_class.iloc[0]), lead=top_pts - pts[1], spread5=top_pts - pts[4])
    r["gap5"] = pts[4] - pts[5] if n_rated > 5 else np.nan       # break after the 5th
    r["gap6"] = pts[5] - pts[6] if n_rated > 6 else np.nan
    r["gap4"] = pts[3] - pts[4]
    for name, mask in (("t4", np.arange(len(g)) < 4), ("t5", np.arange(len(g)) < 5), ("t6", np.arange(len(g)) < 6),
                       ("w5", (top_pts - np.nan_to_num(pts, nan=-1e9)) <= 5.0), ("w8", (top_pts - np.nan_to_num(pts, nan=-1e9)) <= 8.0)):
        n = int(mask.sum())
        r[f"{name}_n"] = n
        r[f"{name}_tri"] = int(((pos <= 3) & mask).sum() == 3)
        r[f"{name}_ff"] = int(((pos <= 4) & mask).sum() == 4)
        r[f"{name}_in4"] = int(((pos <= 4) & mask).sum())
    sp = g.sp.values
    if np.isfinite(sp).all() and (sp > 1).all():
        p = 1 / sp
        p = p / p.sum()
        book = (1 / sp).sum()
        r["book"] = book
        o = list(np.argsort(pos)[:4])   # pos 1..4 are first (nan sorts last)
        h3, h4 = harville(p, o[:3]), harville(p, o)
        r["h3"], r["h4"] = h3, h4
        r["fav_sp"] = sp.min()
        r["pool5_avg_sp"] = np.nanmean(sp[:5])
        r["top_is_fav"] = int(sp[0] == sp.min())
    return r


def build(d):
    rows = [race_rows(g) for _, g in d.groupby("race_id", sort=False)]
    return pd.DataFrame([x for x in rows if x])


def cost(name, n, kind):
    return perm(n, 3) if kind == "tri" else perm(n, 4)


def summarise(R, pool, kind, k, label=""):
    n_col, hit_col = f"{pool}_n", f"{pool}_{kind}"
    m = R
    c = np.array([cost(pool, n, kind) for n in m[n_col]])
    h = m[hit_col].values
    rnd = np.array([(comb(n, 3) / comb(f, 3) if kind == "tri" else comb(n, 4) / comb(f, 4)) for n, f in zip(m[n_col], m.field)])
    out = dict(label=label, races=len(m), avg_n=m[n_col].mean(), cost=c.mean(), hit=h.mean(), lift=h.mean() / rnd.mean())
    return out


def fit_k(path_runners, path_div):
    """Actual dividend / Harville fair dividend, per product, from races in both files (median ratio)."""
    import runners_io
    r = runners_io.read_runners()
    r = r[(r.date.astype(str) >= "2026-10-02") & (r.scratched.fillna(0) == 0)].copy()
    r["v"] = r.venue.astype(str).str.upper()
    r["sp"] = pd.to_numeric(r.starting_price_sp, errors="coerce").fillna(pd.to_numeric(r.fixed_win_price, errors="coerce"))
    dv = pd.read_csv(path_div)
    dv = dv[dv["product"].isin(["Trifecta", "FirstFour"]) & (dv.status == "Paying")].drop_duplicates(["date", "venue", "race_no", "product"])
    ratios = {"Trifecta": [], "FirstFour": []}
    for (dt, ven, rn), g in r.groupby([r.date.astype(str), "v", "race"]):
        sub = dv[(dv.date == dt) & (dv.venue.str.split(" @ ").str[0] == ven) & (dv.race_no == rn)]
        if sub.empty or g.sp.isna().any() or (g.sp <= 1).any() or g.tab_number.isna().any():
            continue
        p = (1 / g.sp.values)
        p = p / p.sum()
        idx = {int(t): i for i, t in enumerate(g.tab_number.values)}
        for _, row in sub.iterrows():
            sel = [int(x) for x in str(row.selections).split("/")]
            if any(s not in idx for s in sel):
                continue
            hv = harville(p, [idx[s] for s in sel])
            if hv and hv > 0:
                ratios[row["product"]].append(row.amount * hv)
    k = {a: float(np.median(v)) for a, v in ratios.items() if v}
    print("actual dividend x Harville probability (1 = fair; the takeout shows as below 1):", {a: (round(x, 3), len(ratios[a])) for a, x in k.items()})
    return k


def real_boxes(path_div):
    """Real TAB dividends, 2 to 21 Oct 2026: box the top 4/5/6 on Spd (runners.csv spd_fig) and the within 5 pts pool."""
    import runners_io
    r = runners_io.read_runners()
    r = r[(r.date.astype(str) >= "2026-10-02") & (r.scratched.fillna(0) == 0)].copy()
    r["v"] = r.venue.astype(str).str.upper()
    r["spd_fig"] = pd.to_numeric(r.spd_fig, errors="coerce")
    r["pts"] = r["spd_fig"]                          # spd_fig is in lengths on the runner file
    r["pts"] = r["pts"] * PTS
    dv = pd.read_csv(path_div)
    dv = dv[dv["product"].isin(["Trifecta", "FirstFour"]) & (dv.status == "Paying")].drop_duplicates(["date", "venue", "race_no", "product"])
    res = []
    for (dt, ven, rn), g in r.groupby([r.date.astype(str), "v", "race"]):
        sub = dv[(dv.date == dt) & (dv.venue.str.split(" @ ").str[0] == ven) & (dv.race_no == rn)]
        if sub.empty:
            continue
        tri = sub[sub["product"] == "Trifecta"]
        ff = sub[sub["product"] == "FirstFour"]
        if tri.empty or ff.empty or g.pts.notna().sum() < 5 or g.tab_number.isna().any():
            continue
        g = g.sort_values("pts", ascending=False, na_position="last")
        tabs = [int(t) for t in g.tab_number]
        t3 = [int(x) for x in str(tri.iloc[0].selections).split("/")]
        f4 = [int(x) for x in str(ff.iloc[0].selections).split("/")]
        row = dict(date=dt, venue=ven, race=rn, field=len(g), n_rated=int(g.pts.notna().sum()), tri_div=float(tri.iloc[0].amount), ff_div=float(ff.iloc[0].amount))
        top = g.pts.iloc[0]
        for name, n in (("t4", 4), ("t5", 5), ("t6", 6)):
            pool = set(tabs[:n])
            row[f"{name}_n"] = n
            row[f"{name}_tri"] = int(set(t3) <= pool)
            row[f"{name}_ff"] = int(set(f4) <= pool)
        pool = {int(t) for t, p in zip(g.tab_number, g.pts) if p == p and top - p <= 5.0}
        row["w5_n"] = len(pool)
        row["w5_tri"] = int(set(t3) <= pool)
        row["w5_ff"] = int(set(f4) <= pool)
        res.append(row)
    return pd.DataFrame(res)


def main(path):
    d = load(path)
    R = build(d)
    print(f"{len(R):,} races with a clean 1-4 finish and at least 5 rated runners ({R.date.min()} to {R.date.max()}), avg field {R.field.mean():.1f}, avg rated {R.n_rated.mean():.1f}")
    kt = kf = None

    def block(R, label):
        rows = []
        for pool in ("t4", "t5", "t6", "w5", "w8"):
            for kind, kk in (("tri", kt), ("ff", kf)):
                rows.append(summarise(R, pool, kind, kk, f"{pool} {kind}"))
        t = pd.DataFrame(rows).set_index("label")
        print(f"\n== {label}: pool capture, cost ($1 unit, boxed), lift vs a random pool of the same size ==")
        print(t.round(3).to_string())

    block(R, "all races")
    # how many of the first four sit in the top 5 / 6
    for pool in ("t5", "t6"):
        print(f"\nfirst-four runners inside {pool}:", R[f"{pool}_in4"].value_counts(normalize=True).sort_index().round(3).to_dict())

    # slices: fit on train, check on test
    R["train"] = R.date < "2026-02-01"
    R["fb"] = pd.cut(R.field, [0, 7, 9, 11, 13, 30], labels=["<=7", "8-9", "10-11", "12-13", "14+"])
    R["gap5b"] = pd.cut(R.gap5, [-1, 1, 2, 3, 5, 100], labels=["<1", "1-2", "2-3", "3-5", "5+"])
    R["gap6b"] = pd.cut(R.gap6, [-1, 1, 2, 3, 5, 100], labels=["<1", "1-2", "2-3", "3-5", "5+"])
    R["spread5b"] = pd.cut(R.spread5, [-1, 3, 5, 8, 12, 1000], labels=["<3", "3-5", "5-8", "8-12", "12+"])
    R["leadb"] = pd.cut(R.lead, [-1, 1, 2, 4, 1000], labels=["<1", "1-2", "2-4", "4+"])
    R["dist_b"] = pd.cut(R.dist, [0, 1100, 1300, 1600, 2000, 9999], labels=["<=1100", "1200-1300", "1400-1600", "1700-2000", "2100+"])
    R["favb"] = pd.cut(R.fav_sp, [0, 2.5, 3.5, 5, 100], labels=["<2.5", "2.5-3.5", "3.5-5", "5+"])
    R["unr"] = (R.field - R.n_rated).clip(upper=3)
    R["clsg"] = R.cls.str.extract(r"^([A-Za-z]+)")[0].str.lower().fillna("?")
    R["going_g"] = R.going.str.extract(r"([A-Za-z]+)")[0].fillna("?")
    for pool, kind in (("t5", "tri"), ("t5", "ff"), ("t6", "ff"), ("w5", "ff")):
        kk = kt if kind == "tri" else kf
        print(f"\n######## pool {pool}, {kind}: slices, TRAIN 2025-07..2026-01 | TEST 2026-02+ (races, hit, lift, est ROI) ########")
        for col in ("fb", "gap5b", "gap6b", "spread5b", "leadb", "dist_b", "favb", "unr", "clsg", "going_g"):
            if pool == "w5" and col in ("gap5b", "gap6b", "spread5b"):
                continue
            lines = []
            for lv, g in R.groupby(col, observed=True):
                if len(g) < 150:
                    continue
                a = summarise(g[g.train], pool, kind, kk)
                b = summarise(g[~g.train], pool, kind, kk) if (~g.train).sum() >= 60 else None
                lines.append((lv, a, b))
            if not lines:
                continue
            print(f"-- {col}")
            for lv, a, b in lines:
                bt = f"{b['races']:5d} {b['hit']*100:5.1f}% x{b['lift']:.1f}" if b else "   (thin)"
                print(f"   {str(lv):10s} {a['races']:5d} {a['hit']*100:5.1f}% x{a['lift']:.1f} avg cost {a['cost']:.0f} | {bt}")

    print("\n######## REAL dividends, 2 to 21 Oct 2026 ########")
    X = real_boxes("tab_dividends.csv")
    print(f"{len(X)} races with Spd, both dividends and a full tab list")
    for pool in ("t4", "t5", "t6", "w5"):
        for kind, div in (("tri", "tri_div"), ("ff", "ff_div")):
            c = np.array([cost(pool, n, kind) for n in X[f"{pool}_n"]])
            h = X[f"{pool}_{kind}"].values
            ret = (X[div].values * h)
            roi = ret.sum() / c.sum() - 1
            ex = ret.copy()
            if h.sum() >= 3:
                ex[np.argsort(-ret)[:3]] = 0
            print(f"{pool} {kind}: races {len(X)}, hits {int(h.sum())} ({h.mean()*100:.1f}%), avg cost {c.mean():.0f}, return/cost {roi*100:+.0f}%, without the 3 biggest {(ex.sum()/c.sum()-1)*100:+.0f}%")
    return R, X


if __name__ == "__main__":
    main(sys.argv[1])
