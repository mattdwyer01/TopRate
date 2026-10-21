"""Can Proj pick winners better, and hold the winner in a tighter shortlist? (21 Oct 2026). Run with PYTHONPATH=.
Population: same as signal_pick_stats.py (archive + runners.csv, 4 Jul to 17 Oct, clean books, single winner, prices known), with races of 5+ runners.
Signals (z-scored within race, a missing value is the race mean): model Proj (logged `wprp_proj`, mixed model versions), formula Proj (recomputed as of each race
date from the runner-page store with weights fitted BEFORE the test window), Nett, Spd. Blends are fitted by race-level conditional logit, cross-fitted on date
halves (fit on one half, score the other, both ways). Also a small LightGBM ranker with context features. Metrics: winner log-lik, top pick strike rate, and the
share of winners inside a shortlist of the matched average size (2.0 and 3.4 runners a race), so a model that spreads the field differently is judged fairly."""
import json, os
import numpy as np
import pandas as pd
from datetime import date
from scipy.optimize import minimize
import speed_rating as sr
from projection import features as F

KEY = ["date", "venue", "race", "horse"]
cols = KEY + ["horse_id", "wpr_nett", "wprp_proj", "scratched", "won", "placed", "fixed_win_price", "starting_price_sp", "field_source", "spd_fig",
              "distance", "race_class", "barrier", "weight_carried"]
rd = lambda p: pd.read_csv(p, low_memory=False, usecols=lambda c: c in cols)
leg = pd.concat([rd("archive/toprate/toprate_runners_archive.csv.gz"), rd("archive/toprate/toprate_runners.csv")], ignore_index=True)
cur = pd.concat([rd("runners_archive.csv.gz"), rd("runners.csv")], ignore_index=True)
for x in (leg, cur):
    x["date"] = x["date"].astype(str).str[:10]; x["race"] = x["race"].astype(str)
d = leg.drop_duplicates(KEY, keep="last").set_index(KEY).combine_first(cur.drop_duplicates(KEY, keep="last").set_index(KEY)).reset_index()
d = d[(d.date >= "2026-07-04") & (d.date <= "2026-10-17")]
d = d[(d.scratched.fillna(0) != 1) & ~d.field_source.astype(str).str.contains("not in toprate", na=False)].reset_index(drop=True)
d["spd_fig"] = sr.compute(d, today=date(2026, 8, 1)).where(lambda s: s.notna(), pd.to_numeric(d.spd_fig, errors="coerce"))
d["rk"] = d.venue.astype(str) + "|" + d.date + "|" + d.race
d["price"] = pd.to_numeric(d.starting_price_sp, errors="coerce")
d["price"] = d.price.where(d.price > 1, pd.to_numeric(d.fixed_win_price, errors="coerce"))
g = d.groupby("rk")
d = d[(g.won.transform("sum") == 1) & g.won.transform(lambda s: s.notna().all()) & g.price.transform(lambda s: s.notna().all())].copy()
d["won"] = d.won.astype(int)
d["book"] = d.groupby("rk").price.transform(lambda s: (1 / s).sum())
d = d[(d.book >= 1.05) & (d.book <= 2.0)]
d = d[d.groupby("rk").won.transform("size") >= 5].copy()

# formula Proj with weights fitted before the test window (no leakage), as of each race date
K = 8
rp = F.runner_page_runs().sort_values(["horse_id", "date"]).reset_index(drop=True)
gg = rp.groupby("horse_id")
for k in range(1, K + 1):
    rp[f"r{k}"] = gg.wpr.shift(k)
rp["n"] = gg.cumcount()
fit_rows = rp[rp.date < "2026-07-04"]
coef = {}
for n in range(1, K + 1):
    a = fit_rows[fit_rows.n.clip(upper=K) == n]
    c = [f"r{k}" for k in range(1, n + 1)]
    coef[n] = np.linalg.lstsq(np.c_[np.ones(len(a)), a[c].values], a.wpr.values, rcond=None)[0]
byh = {h: (x.date.values, x.wpr.values) for h, x in rp.groupby("horse_id")}
hid = pd.to_numeric(d.horse_id, errors="coerce").values
dts = pd.to_datetime(d.date).values
fp = np.full(len(d), np.nan)
for i, (h, t) in enumerate(zip(hid, dts)):
    if np.isnan(h) or int(h) not in byh:
        continue
    dd, ww = byh[int(h)]
    r = ww[dd < t]
    if len(r) == 0:
        continue
    k = min(len(r), K)
    fp[i] = coef[k][0] + float(np.dot(coef[k][1:], r[::-1][:k]))
d["formula"] = fp
SIG = {"model": "wprp_proj", "formula": "formula", "nett": "wpr_nett", "spd": "spd_fig"}
for k, c in SIG.items():
    d[c] = pd.to_numeric(d[c], errors="coerce")
    gm = d.groupby("rk")[c]
    z = (d[c] - gm.transform("mean")) / gm.transform("std").replace(0, np.nan)
    d["z_" + k] = z.fillna(0.0)
    d["has_" + k] = d[c].notna()
d["rkid"] = d.rk.astype("category").cat.codes
# races where the model and the formula both exist for most of the field (so the two are comparable)
cov = d.groupby("rk")[["has_model", "has_formula"]].mean()
ok = cov[(cov.has_model >= 0.8) & (cov.has_formula >= 0.8)].index
d = d[d.rk.isin(ok)].copy()
d.to_pickle(os.environ.get("PI_CACHE","/tmp/pi_cache.pkl"))
print(f"{d.rk.nunique()} races, {len(d)} runners; coverage model {d.has_model.mean():.2f} formula {d.has_formula.mean():.2f} nett {d.has_nett.mean():.2f} spd {d.has_spd.mean():.2f}")

idx = d.groupby("rkid").indices
def nll(w, X, won, rid):
    s = X @ w
    m = pd.Series(s).groupby(rid).transform("max").values
    e = np.exp(s - m)
    lse = np.log(pd.Series(e).groupby(rid).transform("sum").values) + m
    return -(s - lse)[won == 1].mean()
def fit(df, cols):
    X = df[cols].values; return minimize(nll, np.full(len(cols), 0.2), args=(X, df.won.values, df.rkid.values), method="L-BFGS-B").x
def evalscore(df, s):
    t = df.assign(s=s)
    m = t.groupby("rkid").s.transform("max"); e = np.exp(t.s - m)
    lse = np.log(e.groupby(t.rkid).transform("sum")) + m
    ll = (t.s - lse)[t.won == 1].mean()
    top = t.loc[t.groupby("rkid").s.idxmax()]
    return ll, top.won.mean() * 100
def capture(df, s, sizes=(2.0, 3.4)):
    t = df.assign(gap=pd.Series(s, index=df.index).groupby(df.rkid).transform("max") - s)
    out = []
    for target in sizes:
        lo, hi = 0.0, 20.0
        for _ in range(40):
            mid = (lo + hi) / 2
            size = (t.gap <= mid).groupby(t.rkid).sum().mean()
            lo, hi = (mid, hi) if size < target else (lo, mid)
        w = t[t.won == 1]
        out.append(100 * (w.gap <= hi).mean())
    return out
dates = sorted(d.date.unique()); half = dates[len(dates) // 2]
A, B = d[d.date < half], d[d.date >= half]
def run(label, cols, fixedw=None):
    r = []
    for tr, te in ((A, B), (B, A)):
        w = fixedw if fixedw is not None else fit(tr, cols)
        s = te[cols].values @ w
        ll, top = evalscore(te, s); c = capture(te, pd.Series(s, index=te.index))
        r.append((ll, top, c[0], c[1]))
    m = np.mean(r, axis=0)
    w = fit(d, cols) if fixedw is None else fixedw
    print(f"{label:34s} LL {m[0]:.4f}  top1 {m[1]:.1f}%  in-2.0-runners {m[2]:.1f}%  in-3.4-runners {m[3]:.1f}%   w={np.round(w, 2)}")
print("\nsignals alone and blends (fitted weights):")
for k in SIG: run("only " + k, ["z_" + k])
run("model + formula", ["z_model", "z_formula"])
run("model + formula + nett", ["z_model", "z_formula", "z_nett"])
run("model + formula + nett + spd", ["z_model", "z_formula", "z_nett", "z_spd"])
run("formula + nett + spd (no model)", ["z_formula", "z_nett", "z_spd"])
run("model + nett + spd (no formula)", ["z_model", "z_nett", "z_spd"])
# shipped Rank-style blend for reference: Proj 0.65, Nett 0.25, Spd 0.10 with the model as Proj and with the formula as Proj
run("ref: formula .65 nett .25 spd .10", ["z_formula", "z_nett", "z_spd"], np.array([0.65, 0.25, 0.10]) * 1.0)
run("ref: model .65 nett .25 spd .10", ["z_model", "z_nett", "z_spd"], np.array([0.65, 0.25, 0.10]) * 1.0)

# small LightGBM ranker with context, cross-fitted
import lightgbm as lgb
d["dist"] = pd.to_numeric(d.distance, errors="coerce")
d["barr"] = pd.to_numeric(d.barrier, errors="coerce")
d["fsz"] = d.groupby("rk").won.transform("size")
d["wt"] = pd.to_numeric(d.weight_carried, errors="coerce")
d["wt_z"] = (d.wt - d.groupby("rk").wt.transform("mean")).fillna(0)
d["barr_f"] = (d.barr / d.fsz).fillna(0.5)
d["mkt"] = 0.0  # no market input
feats = ["z_model", "z_formula", "z_nett", "z_spd", "dist", "fsz", "barr_f", "wt_z"]
A, B = d[d.date < half], d[d.date >= half]
res = []
for tr, te in ((A, B), (B, A)):
    tr = tr.sort_values("rkid"); te = te.sort_values("rkid")
    grp = tr.groupby("rkid").size().values
    mdl = lgb.LGBMRanker(objective="lambdarank", n_estimators=150, learning_rate=0.04, num_leaves=7, min_child_samples=60, subsample=0.8, colsample_bytree=0.8, verbose=-1)
    mdl.fit(tr[feats], tr.won, group=grp)
    s = mdl.predict(te[feats]); ll, top = evalscore(te, s * 1.0); c = capture(te, pd.Series(s, index=te.index))
    res.append((top, c[0], c[1]))
m = np.mean(res, axis=0)
print(f"\n{'LightGBM ranker + context':34s} top1 {m[0]:.1f}%  in-2.0-runners {m[1]:.1f}%  in-3.4-runners {m[2]:.1f}%   (scores are not on a log scale, so no log-lik)")
