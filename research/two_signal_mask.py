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
d["spd"] = 79.15 + 1.33 * pd.to_numeric(d.spd_fig, errors="coerce")
d["nett"] = pd.to_numeric(d.wpr_nett, errors="coerce"); d["proj"] = pd.to_numeric(d.wprp_proj, errors="coerce")
d = d.dropna(subset=["spd", "nett", "proj"])
d = d.groupby("rk").filter(lambda g: len(g) >= 5)
d["rkid"] = d.rk.astype("category").cat.codes
print(d.rkid.nunique(), "complete-case races,", len(d), "runners")
W = dict(proj=.5, nett=.3, spd=.2)
d["full"] = .5 * d.proj + .3 * d.nett + .2 * d.spd
# 1) field-level gap between signals' means, per race
g = d.groupby("rk")
gap = pd.DataFrame({"nett_minus_proj": g.nett.mean() - g.proj.mean(), "spd_minus_proj": g.spd.mean() - g.proj.mean()})
print("\nwithin-race field-mean gaps (points): mean / sd across races")
print(gap.agg(["mean", "std"]).round(2).T)
# 2) random masking: mask one signal on 8% of runners, score by renormalising, compare level and win calibration
rng = np.random.default_rng(1)
def nll(s, df):
    s = pd.Series(np.asarray(s), index=df.index); m = s.groupby(df.rkid).transform("max")
    lse = np.log(np.exp(s - m).groupby(df.rkid).transform("sum")) + m
    return -(s - lse)[df.won == 1].mean()
b = minimize_scalar(lambda x: nll(x * d.full, d), bounds=(0.001, 3), method="bounded").x
base_ll = -nll(b * d.full, d)
print(f"\nall-three baseline LL {base_ll:.4f}, beta {b:.3f}")
for miss in ("spd", "nett"):
    rows = []
    for rep in range(30):
        m = rng.random(len(d)) < 0.08
        sc = d.full.copy()
        keep = {k: w for k, w in W.items() if k != miss}
        sc[m] = sum(w * d.loc[m, k] for k, w in keep.items()) / sum(keep.values())
        ll = -nll(b * sc, d)
        p = np.exp(b * sc); p = p / p.groupby(d.rkid).transform("sum")
        rows.append((ll - base_ll, (sc[m] - d.full[m]).mean(), p[m].mean(), d.won[m].mean(), m.sum()))
    r = np.array(rows)
    print(f"missing {miss:4s}: LL change {r[:,0].mean():+.4f} (sd {r[:,0].std():.4f}); mean score shift for masked runners {r[:,1].mean():+.2f} pts (sd {r[:,1].std():.2f}); predicted win {r[:,2].mean():.2%} actual {r[:,3].mean():.2%} (avg n {r[:,4].mean():.0f})")
# 3) what shift-to-Proj-level would have done: masked runner gets signal imputed as proj + field gap
for miss in ("spd", "nett"):
    gapk = (g[miss].transform("mean") - g.proj.transform("mean"))
    rows = []
    for rep in range(30):
        m = rng.random(len(d)) < 0.08
        sc = d.full.copy()
        keep = {k: w for k, w in W.items() if k != miss}
        sc[m] = sum(w * d.loc[m, k] for k, w in keep.items()) / sum(keep.values())
        sc2 = d.full.copy()
        # impute missing signal as the average of the others plus nothing (renormalised) vs add the field's average level gap of the missing signal times its weight
        sc2[m] = sc[m] + W[miss] * (gapk[m] * 0 + (g[miss].transform("mean")[m] - (sum(w * g[k].transform("mean")[m] for k, w in keep.items()) / sum(keep.values()))))
        rows.append((-nll(b * sc, d) - base_ll, -nll(b * sc2, d) - base_ll))
    r = np.array(rows)
    print(f"missing {miss:4s}: LL change renormalised {r[:,0].mean():+.4f}  vs field-level-corrected {r[:,1].mean():+.4f}")
