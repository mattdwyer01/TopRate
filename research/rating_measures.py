"""Which measure judges a rating best? (19 Oct 2026) Live runners.csv 18 Sep onward, clean books. For Spd, Nett, L3 (mean of last 3 results/runner-page ratings is not in
runners.csv, so Proj stands in as the model rating), Proj: (1) within-race correlation with the market (log implied chance) and with each other, (2) winner log-lik alone,
(3) incremental winner log-lik over the market: market + w x z(signal), w fitted on the first half of dates, scored on the second (paired gain per race and se).
"""
import numpy as np
import pandas as pd
from scipy.optimize import minimize_scalar

cols = ["date", "venue", "race", "horse", "spd_fig", "wpr_nett", "wprp_proj", "scratched", "won", "fixed_win_price", "starting_price_sp", "field_source"]
d = pd.read_csv("runners.csv", low_memory=False, usecols=lambda c: c in cols)
d = d[(d.date >= "2026-09-18") & (d.scratched.fillna(0) != 1) & ~d.field_source.astype(str).str.contains("not in toprate", na=False)]
d["rk"] = d.venue.astype(str) + "|" + d.date + "|" + d.race.astype(str)
d["price"] = pd.to_numeric(d.starting_price_sp, errors="coerce")
d["price"] = d.price.where(d.price > 1, pd.to_numeric(d.fixed_win_price, errors="coerce"))
g = d.groupby("rk")
d = d[(g.won.transform("sum") == 1) & g.won.transform(lambda s: s.notna().all()) & g.price.transform(lambda s: s.notna().all())].copy()
d["won"] = d.won.astype(int)
d["book"] = d.groupby("rk").price.transform(lambda s: (1 / s).sum())
d = d[(d.book >= 1.05) & (d.book <= 2.0)]
d = d[d.spd_fig.notna() & d.wpr_nett.notna() & d.wprp_proj.notna()]
d = d[d.groupby("rk").spd_fig.transform("size") >= 5].copy()
d["lm"] = np.log((1 / d.price) / d.book)
sig = {"Spd": "spd_fig", "Nett": "wpr_nett", "Proj": "wprp_proj"}
for k, c in sig.items():
    gg = d.groupby("rk")[c]
    d["z_" + k] = ((d[c] - gg.transform("mean")) / gg.transform("std").replace(0, np.nan)).fillna(0)
d["zm"] = d.lm - d.groupby("rk").lm.transform("mean")
print(f"{d.rk.nunique()} races, {len(d)} runners (all three ratings present)")
print("\nwithin-race correlation (mean over races)")
names = list(sig) + ["market"]
zs = {k: d["z_" + k] for k in sig}
zs["market"] = d.zm
M = pd.DataFrame(index=names, columns=names, dtype=float)
for a in names:
    for b in names:
        M.loc[a, b] = pd.DataFrame({"a": zs[a], "b": zs[b], "rk": d.rk}).groupby("rk").apply(lambda x: x.a.corr(x.b)).mean()
print(M.round(2).to_string())

dates = sorted(d.date.unique())
cut = dates[len(dates) // 2]
d["h2"] = d.date >= cut


def race_ll(score, mask):
    s = pd.Series(score, index=d.index)[mask]
    sub = d[mask]
    mx = s.groupby(sub.rk).transform("max")
    e = np.exp(s - mx)
    lse = np.log(e.groupby(sub.rk).transform("sum")) + mx
    ll = (s - lse)[sub.won == 1]
    return ll.values


base_all = race_ll(d.zm.values, d.index == d.index)
print(f"\nmarket alone winner log-lik {base_all.mean():+.4f}")
print("\nsignal                alone LL   fitted w (1st half)   gain over market, 2nd half (se)")
m1, m2 = ~d.h2, d.h2
for k in sig:
    z = d["z_" + k].values
    alone = race_ll(z * 0.5, d.index == d.index).mean()
    f = minimize_scalar(lambda w: -race_ll(d.zm.values + w * z, m1).mean(), bounds=(0, 2), method="bounded")
    w = f.x
    diff = race_ll(d.zm.values + w * z, m2) - race_ll(d.zm.values, m2)
    print(f"{k:6s}  {alone:+9.4f}   {w:6.3f}               {diff.mean():+.4f} ({diff.std() / np.sqrt(len(diff)):.4f})")
z = d[["z_Spd", "z_Nett", "z_Proj"]].mean(axis=1).values
f = minimize_scalar(lambda w: -race_ll(d.zm.values + w * z, m1).mean(), bounds=(0, 3), method="bounded")
diff = race_ll(d.zm.values + f.x * z, m2) - race_ll(d.zm.values, m2)
print(f"mean of three  {race_ll(z * 0.5, d.index == d.index).mean():+9.4f}   {f.x:6.3f}               {diff.mean():+.4f} ({diff.std() / np.sqrt(len(diff)):.4f})")
