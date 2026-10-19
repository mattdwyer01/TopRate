"""Which signal adds most over the market? (19 Oct 2026) Longer sample: archived TopRate runner files (26 Apr to 12 Oct, Nett and TopRate's last-3 average as scraped before each race,
the logged projection) joined to runners.csv for 13 Oct onward, Spd computed with speed_rating.compute for every date. Clean books only (BOOK_MIN 1.05 to BOOK_MAX 2.0), races with a
single winner and every price known. Signals are z-scored inside the race; for each, market + w x z is fitted on one half of the dates and scored on the other (cross-fit both ways), paired
gain in winner log-lik per race with its se. Also a joint fit of all signals and drop-one tests.
"""
import numpy as np
import pandas as pd
from datetime import date
from scipy.optimize import minimize
import speed_rating as sr

KEY = ["date", "venue", "race", "horse"]
cols = KEY + ["wpr_nett", "wpr_avg_last3", "wprp_proj", "toprate_rating", "scratched", "won", "fixed_win_price", "starting_price_sp", "field_source", "spd_fig"]
rd = lambda p: pd.read_csv(p, low_memory=False, usecols=lambda c: c in cols)
leg = pd.concat([rd("archive/toprate/toprate_runners_archive.csv.gz"), rd("archive/toprate/toprate_runners.csv")], ignore_index=True)
cur = pd.concat([rd("runners_archive.csv.gz"), rd("runners.csv")], ignore_index=True)
for x in (leg, cur):
    x["date"] = x["date"].astype(str).str[:10]
    x["race"] = x["race"].astype(str)
leg = leg.drop_duplicates(KEY, keep="last").set_index(KEY)
cur = cur.drop_duplicates(KEY, keep="last").set_index(KEY)
d = leg.combine_first(cur).reset_index()
d = d[(d.date >= "2026-04-26") & (d.date <= "2026-10-17")]
d = d[(d.scratched.fillna(0) != 1) & ~d.field_source.astype(str).str.contains("not in toprate", na=False)].copy()
print("rows", len(d), "dates", d.date.min(), d.date.max())

# Spd for every runner (rating before the race)
d = d.reset_index(drop=True)
d["spd_calc"] = sr.compute(d, today=date(2026, 5, 24))
d["spd_fig"] = d.spd_calc.where(d.spd_calc.notna(), pd.to_numeric(d.spd_fig, errors="coerce"))
print("fill rates", d[["spd_fig", "wpr_nett", "wpr_avg_last3", "wprp_proj", "toprate_rating"]].notna().mean().round(3).to_dict())

d["rk"] = d.venue.astype(str) + "|" + d.date + "|" + d.race
d["price"] = pd.to_numeric(d.starting_price_sp, errors="coerce")
d["price"] = d.price.where(d.price > 1, pd.to_numeric(d.fixed_win_price, errors="coerce"))
g = d.groupby("rk")
d = d[(g.won.transform("sum") == 1) & g.won.transform(lambda s: s.notna().all()) & g.price.transform(lambda s: s.notna().all())].copy()
d["won"] = d.won.astype(int)
d["book"] = d.groupby("rk").price.transform(lambda s: (1 / s).sum())
d = d[(d.book >= 1.05) & (d.book <= 2.0)]
SIG = {"Spd": "spd_fig", "Nett": "wpr_nett", "L3": "wpr_avg_last3", "Proj": "wprp_proj", "TRrat": "toprate_rating"}
for c in SIG.values():
    d[c] = pd.to_numeric(d[c], errors="coerce")
need = [SIG[k] for k in ("Spd", "Nett", "L3", "Proj")]
d = d.dropna(subset=need)
d = d[d.groupby("rk").won.transform("size") >= 5].copy()
d["lm"] = np.log((1 / d.price) / d.book)
for k, c in SIG.items():
    gg = d.groupby("rk")[c]
    d["z_" + k] = ((d[c] - gg.transform("mean")) / gg.transform("std").replace(0, np.nan)).fillna(0)
d["zm"] = d.lm - d.groupby("rk").lm.transform("mean")
print(f"{d.rk.nunique()} complete races, {len(d)} runners, {d.date.min()} to {d.date.max()}")

names = list(SIG) + ["market"]
zs = {k: d["z_" + k] for k in SIG}
zs["market"] = d.zm
M = pd.DataFrame(index=names, columns=names, dtype=float)
sub = pd.DataFrame(zs); sub["rk"] = d.rk
for a in names:
    for b in names:
        M.loc[a, b] = sub.groupby("rk").apply(lambda x: x[a].corr(x[b])).mean()
print("\nwithin-race correlation (mean over races)")
print(M.round(2).to_string())

# race arrays for speed
d = d.sort_values(["rk"]).reset_index(drop=True)
codes, uniq = pd.factorize(d.rk)
nR = len(uniq)
won = d.won.values == 1
rdate = d.groupby("rk").date.first().reindex(uniq).values


def ll(score, rmask):
    """winner log-lik per race for races where rmask is True (indexed by race code)"""
    mx = np.full(nR, -1e9)
    np.maximum.at(mx, codes, score)
    e = np.exp(score - mx[codes])
    s = np.bincount(codes, e, nR)
    w = np.zeros(nR)
    w[codes[won]] = score[won]
    out = w - (np.log(s) + mx)
    return out[rmask]


dates = np.sort(np.unique(rdate))
cut = dates[len(dates) // 2]
h1 = rdate < cut
h2 = ~h1
zm = d.zm.values


def fit(cols_, mask):
    Z = np.column_stack([d["z_" + c].values for c in cols_])
    f = minimize(lambda w: -ll(zm + Z @ w, mask).mean(), np.zeros(len(cols_)), method="L-BFGS-B", bounds=[(0, 3)] * len(cols_))
    return f.x, Z


def crossfit(cols_):
    diffs = []
    ws = []
    for tr, te in ((h1, h2), (h2, h1)):
        w, Z = fit(cols_, tr)
        diffs.append(ll(zm + Z @ w, te) - ll(zm, te))
        ws.append(w)
    dd = np.concatenate(diffs)
    return dd.mean(), dd.std() / np.sqrt(len(dd)), np.mean(ws, axis=0)


print(f"\nmarket alone winner log-lik {ll(zm, np.ones(nR, bool)).mean():+.4f}")
print("\nsignal(s)                 alone LL   cross-fit gain over market (se)   avg weight")
for k in SIG:
    alone = ll(0.5 * d["z_" + k].values, np.ones(nR, bool)).mean()
    m, se, w = crossfit([k])
    print(f"{k:24s}  {alone:+8.4f}   {m:+.4f} ({se:.4f})                  {w.round(3)}")
for combo in (["Spd", "Nett", "L3", "Proj"], ["Nett", "L3", "Proj"], ["Spd", "L3"], ["Spd", "Nett", "L3"], ["Spd", "Proj"], ["Nett", "Proj"], ["Spd", "Nett", "L3", "Proj", "TRrat"]):
    m, se, w = crossfit(combo)
    print(f"{'+'.join(combo):24s}  {'':8s}   {m:+.4f} ({se:.4f})                  {w.round(3)}")
print("\nmarginal value of each signal inside the full four (drop-one loss of gain)")
full, _, _ = crossfit(["Spd", "Nett", "L3", "Proj"])
for k in ("Spd", "Nett", "L3", "Proj"):
    rest = [x for x in ("Spd", "Nett", "L3", "Proj") if x != k]
    m, se, _ = crossfit(rest)
    print(f"  without {k:5s}: {m:+.4f}   ({full - m:+.4f} lost)")
