"""Volume v1, v2 and v3 side by side on three years of Betfair prices, with stand-ins (11 Nov 2026).
  PYTHONPATH=.:research python research/volume_v123_history.py      (needs /tmp/value_model2_frame.pkl from research/value_model2.py)
Stand-ins, as in volume_betfair_history.py: rating = least squares on last run, last-3, last-8 and best of 8 (fitted on 2023);
settle = mean 800m position share over the last 4 runs, ranked in the field. For v3 the chance of settling in the first third is a
LightGBM classifier on style, its rank in the field, gap to the most forward runner, barrier, field size and likely leaders (fitted on 2023).
Qualifier = first third on the settle stand-in and Betfair price over $3.
  v1  qualifiers within 4 points of the top-rated runner
  v2  top-rated runner is a qualifier: qualifiers within 2; no qualifier within 1 of the top: qualifiers within 4; otherwise no bet
  v3  as v1 but 'first third' = chance of the first third 0.6 or more
$25 a race split over the bets, paid at the Betfair starting price after commission (10% NSW, 8% elsewhere)."""
import warnings
import lightgbm as lgb
import numpy as np, pandas as pd
warnings.filterwarnings("ignore")
d = pd.read_pickle("/tmp/value_model2_frame.pkl")
d["yr"] = d.ds.str[:4]
X = ["w1", "m3", "m8", "max8"]
fit = d[(d.yr == "2023") & d[X + ["wpr"]].notna().all(axis=1)]
co = np.linalg.lstsq(np.c_[np.ones(len(fit)), fit[X].values], fit.wpr.values, rcond=None)[0]
d["proj"] = co[0] + d[X].fillna(d[X].mean()).values @ co[1:]
d.loc[d.nruns < 3, "proj"] = np.nan
g = d.groupby("race_id")
d["n"] = g.race_id.transform("size")
d["ok"] = g.proj.transform(lambda s: s.notna().all()) & g["style"].transform(lambda s: s.notna().all()) & (d.n >= 5)
d["off"] = g.proj.transform("max") - d.proj
d["srk"] = g["style"].rank(method="min")
d["sp_"] = (d.srk - 1) / (d.n - 1)
PF = ["style", "sp_", "style_gap_lead", "barfrac", "n", "n_lead"]
tr = d[(d.yr == "2023") & d.ok & d.e0.notna()]
m = lgb.train(dict(objective="binary", learning_rate=0.03, num_leaves=15, min_data_in_leaf=200, bagging_fraction=0.8, bagging_freq=1, feature_fraction=0.8, verbose=-1, seed=1),
              lgb.Dataset(tr[PF], label=(tr.e0 <= 1 / 3).astype(int)), num_boost_round=300)
d["pft"] = m.predict(d[PF])
R = d[d.ok & (d.yr >= "2024")].copy()
te = R[R.e0.notna()]
print("eligible races 2024 to 8 Oct 2026: %d (%d runners)" % (R.race_id.nunique(), len(R)))
print("settle stand-in check: rank cut is right %.1f%% of the time (%d picks); chance 0.6+ is right %.1f%% (%d picks)" % (
    100 * (te[te.sp_ <= 1 / 3].e0 <= 1 / 3).mean(), (te.sp_ <= 1 / 3).sum(), 100 * (te[te.pft >= 0.6].e0 <= 1 / 3).mean(), (te.pft >= 0.6).sum()))

R["q"] = (R.sp_ <= 1 / 3 + 1e-9) & (R.bsp > 3)
R["q3"] = (R.pft >= 0.6) & (R.bsp > 3)
gr = R.groupby("race_id")
top_is_q = (R.q & (R.off <= 1e-9)).groupby(R.race_id).transform("max")
any_q1 = (R.q & (R.off <= 1)).groupby(R.race_id).transform("max")
R["v1"] = R.q & (R.off <= 4)
R["v2"] = R.q & np.where(top_is_q, R.off <= 2, np.where(~any_q1, R.off <= 4, False))
R["v3"] = R.q3 & (R.off <= 4)
R["case"] = np.where(top_is_q, "top is a bet", np.where(~any_q1, "nothing within 1", "one within 1, top not a bet"))


def stats(x, per_race=True):
    st = 25.0 / x.groupby("race_id").race_id.transform("size") if per_race else pd.Series(1.0, index=x.index)
    pnl = st * (x.won * (x.bsp - 1) * (1 - x.comm) - (1 - x.won))
    o = np.sort(pnl.values)[::-1]
    by = pd.DataFrame({"p": pnl, "s": st, "y": x.yr}).groupby("y").sum()
    days = pd.DataFrame({"p": pnl, "s": st, "d": x.ds}).groupby("d").sum()
    rng = np.random.default_rng(3)
    idx = rng.integers(0, len(days), (1000, len(days)))
    bs = days.p.values[idx].sum(1) / days.s.values[idx].sum(1)
    return dict(races=x.race_id.nunique(), bets=len(x), win=x.won.mean(), impl=x.pm.mean(), avg=x.bsp.mean(), roi=pnl.sum() / st.sum(),
                lo=np.quantile(bs, .05), hi=np.quantile(bs, .95), ex50=(pnl.sum() - o[:50].sum()) / st.sum(),
                years=" ".join("%s %+.1f%%" % (y, 100 * r.p / r.s) for y, r in by.iterrows()))


def line(lab, x, per_race=True):
    if len(x) == 0:
        return "%-58s no bets" % lab
    s = stats(x, per_race)
    return "%-58s %5d races %6d bets win %5.1f%% (Betfair %5.1f%%) avg $%5.2f ROI %+6.1f%% [%+5.1f, %+5.1f] ex50 %+6.1f | %s" % (
        lab, s["races"], s["bets"], 100 * s["win"], 100 * s["impl"], s["avg"], 100 * s["roi"], 100 * s["lo"], 100 * s["hi"], 100 * s["ex50"], s["years"])


print("\n===== the three rules, $25 a race =====")
for r in ("v1", "v2", "v3"):
    print(line(r, R[R[r]]))
print("\n===== the same, $1 a bet =====")
for r in ("v1", "v2", "v3"):
    print(line(r, R[R[r]], per_race=False))
print("\n===== where they differ ($1 a bet) =====")
print(line("v1 bets that v2 drops", R[R.v1 & ~R.v2], per_race=False))
print(line("v1 bets that v3 drops", R[R.v1 & ~R.v3], per_race=False))
print(line("v3 bets that v1 does not have", R[R.v3 & ~R.v1], per_race=False))
print(line("in all three", R[R.v1 & R.v2 & R.v3], per_race=False))
print("\n===== v1 bets by v2's three cases ($1 a bet) =====")
for c in ("top is a bet", "nothing within 1", "one within 1, top not a bet"):
    x = R[R.v1 & (R.case == c)]
    print(line(c + ": all v1 bets", x, per_race=False))
    if c == "top is a bet":
        print(line("   the top-rated runner itself", x[x.off <= 1e-9], per_race=False))
        print(line("   others within 2", x[(x.off > 1e-9) & (x.off <= 2)], per_race=False))
        print(line("   others 2 to 4 off (v2 drops)", x[x.off > 2], per_race=False))
print("\n===== v1 bets by the chance of the first third ($1 a bet) =====")
for a, b in ((0, .4), (.4, .5), (.5, .6), (.6, .7), (.7, 1.01)):
    print(line("chance %.1f to %.1f" % (a, b), R[R.v1 & (R.pft >= a) & (R.pft < b)], per_race=False))
print("\n===== v1 bets by points off the top ($1 a bet) =====")
for a, b in ((-1, 1e-9), (1e-9, 1), (1, 2), (2, 3), (3, 4.0001)):
    print(line("off %.0f to %.0f" % (max(a, 0), b), R[R.v1 & (R.off > a) & (R.off <= b)], per_race=False))
