"""Strike rate, average winning price and ROI for each signal's top picks (19 Oct 2026). Same sample and prep as rating_measures2.py (archive + runners.csv, clean books,
single-winner races, every price known). Rank = mean of the four signal ranks (needs all four here). Run with PYTHONPATH=."""
import numpy as np
import pandas as pd
from datetime import date
import speed_rating as sr

KEY = ["date", "venue", "race", "horse"]
cols = KEY + ["wpr_nett", "wpr_avg_last3", "wprp_proj", "scratched", "won", "placed", "fixed_win_price", "starting_price_sp", "field_source", "spd_fig"]
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


from scipy.optimize import minimize_scalar
SIG = {"Spd": "spd_fig", "Nett": "wpr_nett", "Proj": "wprp_proj"}
for c in SIG.values():
    d[c] = pd.to_numeric(d[c], errors="coerce")
d = d.dropna(subset=list(SIG.values()))
d = d[d.groupby("rk").won.transform("size") >= 5].copy()
d["rkid"] = d.rk.astype("category").cat.codes
W = {"spd_fig": 0.20, "wpr_nett": 0.30, "wprp_proj": 0.50}
g = d.groupby("rk")
d["spd_scaled"] = 79.15 + 1.33 * d.spd_fig
for c in ("spd_fig", "wpr_nett", "wprp_proj", "spd_scaled"):
    gg = d.groupby("rk")[c]
    d["z_" + c] = (d[c] - gg.transform("mean")) / gg.transform("std").replace(0, np.nan)
d = d.dropna(subset=["z_spd_fig", "z_wpr_nett", "z_wprp_proj"]).copy()
d["s_z"] = sum(W[c] * d["z_" + c] for c in W)
d["s_raw_scaled"] = 0.2 * d.spd_scaled + 0.3 * d.wpr_nett + 0.5 * d.wprp_proj
d["s_raw_lengths"] = 0.2 * d.spd_fig + 0.3 * d.wpr_nett + 0.5 * d.wprp_proj
# centre raw scores within race (softmax is shift invariant anyway)
def nll(beta, df, col):
    s = beta * df[col]
    m = s.groupby(df.rkid).transform("max")
    lse = np.log(np.exp(s - m).groupby(df.rkid).transform("sum")) + m
    w = df.won == 1
    return -(s - lse)[w].mean()
def evaluate(label, col):
    dates = sorted(d.date.unique()); half = dates[len(dates) // 2]
    A, B = d[d.date < half], d[d.date >= half]
    lls, picks, betas = [], [], []
    for tr, te in ((A, B), (B, A)):
        b = minimize_scalar(lambda x: nll(x, tr, col), bounds=(0.001, 5), method="bounded").x
        lls.append(-nll(b, te, col)); betas.append(b)
        top = te.loc[te.groupby("rkid")[col].idxmax()]
        picks.append(top.won.mean() * 100)
    # bootstrap-free paired comparison handled below via per-race LL
    print(f"{label:34s} LL {np.mean(lls):.4f}  top-pick {np.mean(picks):.1f}%  beta {np.mean(betas):.3f}")
    return np.mean(betas)
print(d.rkid.nunique(), "races,", len(d), "runners,", d.date.min(), "to", d.date.max())
bz = evaluate("z-score blend 50/30/20", "s_z")
br = evaluate("raw blend, Spd on Nett scale", "s_raw_scaled")
bl = evaluate("raw blend, Spd in lengths (naive)", "s_raw_lengths")
for k in ("z_wprp_proj", "z_wpr_nett", "z_spd_fig"):
    evaluate("single " + k, k)
# paired per-race LL difference, z vs raw_scaled, betas fitted on full set
def per_race(col):
    b = minimize_scalar(lambda x: nll(x, d, col), bounds=(0.001, 5), method="bounded").x
    s = b * d[col]
    m = s.groupby(d.rkid).transform("max")
    lse = np.log(np.exp(s - m).groupby(d.rkid).transform("sum")) + m
    return (s - lse)[d.won == 1].groupby(d.rkid[d.won == 1]).mean()
diff = per_race("s_z") - per_race("s_raw_scaled")
print(f"paired LL z minus raw(scaled): mean {diff.mean():+.4f}  se {diff.std()/np.sqrt(len(diff)):.4f}")
tz = d.loc[d.groupby("rkid").s_z.idxmax()].set_index("rkid").index
same = (d.loc[d.groupby("rkid").s_z.idxmax()].set_index("rkid").horse == d.loc[d.groupby("rkid").s_raw_scaled.idxmax()].set_index("rkid").horse).mean()
print(f"same #1 pick z vs raw(scaled): {100*same:.1f}% of races")
print("within-race sd (mean of per-race sd): Spd scaled %.2f  Nett %.2f  Proj %.2f  Spd lengths %.2f" % tuple(d.groupby("rk")[c].std().mean() for c in ("spd_scaled", "wpr_nett", "wprp_proj", "spd_fig")))
d["s_hyb"] = d.s_z * d.groupby("rk").wprp_proj.transform("std")
evaluate("Rating as shown (z blend x Proj sd)", "s_hyb")
diff2 = per_race("s_hyb") - per_race("s_raw_scaled")
print(f"paired LL Rating-as-shown minus raw(scaled): mean {diff2.mean():+.4f}  se {diff2.std()/np.sqrt(len(diff2)):.4f}")
diff3 = per_race("s_hyb") - per_race("s_z")
print(f"paired LL Rating-as-shown minus z: mean {diff3.mean():+.4f}  se {diff3.std()/np.sqrt(len(diff3)):.4f}")
