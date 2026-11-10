"""The Volume idea on three years of Betfair prices, with stand-ins for the two forecasts (10 Nov 2026).
Run after research/value_model2.py has written its frame (/tmp/value_model2_frame.pkl):  PYTHONPATH=.:research python research/volume_betfair_history.py
The live rule needs the trip map forecast and the logged Proj, which exist for about five weeks. Here:
  rating stand-in  = least-squares fit of a run's rating on the horse's last run, last-3 mean, last-8 mean and best of 8 (fitted on 2023, applied from 2024)
  settle stand-in  = the horse's average position at the 800m (as a share of the field) over its last 4 runs, ranked in today's field
Rule: every runner has 3+ earlier runs and a style, field of 5+, runner in the first third on the settle stand-in, within N points of the top stand-in
rating, Betfair price over $3 (a Betfair SP bet can carry a minimum price). Payout: Betfair SP after commission (10% NSW, 8% elsewhere)."""
import itertools, sys, warnings
import numpy as np, pandas as pd
warnings.filterwarnings("ignore")
d = pd.read_pickle("/tmp/value_model2_frame.pkl")
d["yr"] = d.ds.str[:4]
X = ["w1", "m3", "m8", "max8"]
fit = d[(d.yr == "2023") & d[X + ["wpr"]].notna().all(axis=1)]
A = np.c_[np.ones(len(fit)), fit[X].values]
co = np.linalg.lstsq(A, fit.wpr.values, rcond=None)[0]
print("rating stand-in: %.2f + %s" % (co[0], " + ".join("%.3f x %s" % (c, n) for c, n in zip(co[1:], X))))
d["proj"] = co[0] + d[X].fillna(d[X].mean()).values @ co[1:]
d.loc[d.nruns < 3, "proj"] = np.nan
g = d.groupby("race_id")
d["n"] = g.race_id.transform("size")
d["ok"] = g.proj.transform(lambda s: s.notna().all()) & g["style"].transform(lambda s: s.notna().all()) & (d.n >= 5)
d["off"] = g.proj.transform("max") - d.proj
d["srk"] = g["style"].rank(method="min")
d["sp_"] = (d.srk - 1) / (d.n - 1)
R = d[d.ok & (d.yr >= "2024")].copy()
print("eligible races 2024 to 8 Oct 2026: %d of %d (%d runners)" % (R.race_id.nunique(), d[d.yr >= "2024"].race_id.nunique(), len(R)))


def stats(x, per_race=True):
    st = 25.0 / x.groupby("race_id").race_id.transform("size") if per_race else pd.Series(1.0, index=x.index)
    pnl = st * (x.won * (x.bsp - 1) * (1 - x.comm) - (1 - x.won))
    o = np.sort(pnl.values)[::-1]
    by = pd.DataFrame({"p": pnl, "s": st, "y": x.yr}).groupby("y").sum()
    days = pd.DataFrame({"p": pnl, "s": st, "d": x.ds}).groupby("d").sum()
    rng = np.random.default_rng(3)
    bs = np.array([(lambda s_: s_.p.sum() / s_.s.sum())(days.sample(len(days), replace=True, random_state=int(rng.integers(1e9)))) for _ in range(400)])
    return dict(races=x.race_id.nunique(), bets=len(x), win=x.won.mean(), impl=x.pm.mean(), avg=x.bsp.mean(), roi=pnl.sum() / st.sum(),
                lo=np.quantile(bs, .05), hi=np.quantile(bs, .95), p0=(bs > 0).mean(), ex10=(pnl.sum() - o[:10].sum()) / st.sum(),
                ex50=(pnl.sum() - o[:50].sum()) / st.sum(), years=" ".join("%s %+.1f%%" % (y, 100 * r.p / r.s) for y, r in by.iterrows()))


def line(lab, x, per_race=True):
    if len(x) == 0:
        return "%-52s no bets" % lab
    s = stats(x, per_race)
    return "%-52s %5d races %6d bets win %5.1f%% (Betfair %5.1f%%) avg $%5.2f ROI %+6.1f%% [%+5.1f, %+5.1f] P>0 %3.0f%% ex10 %+6.1f ex50 %+6.1f | %s" % (
        lab, s["races"], s["bets"], 100 * s["win"], 100 * s["impl"], s["avg"], 100 * s["roi"], 100 * s["lo"], 100 * s["hi"], 100 * s["p0"], 100 * s["ex10"], 100 * s["ex50"], s["years"])


q = lambda settle, off, floor=3, cap=1001, fmin=5: R[(R.sp_ <= settle + 1e-9) & (R.off <= off + 1e-9) & (R.bsp > floor) & (R.bsp < cap) & (R.n >= fmin)]
print("\n===== the rule as it stands (first third, within 4, over $3) and its parts =====")
print(line("v1 stand-in: first third, within 4, over $3", q(1 / 3, 4)))
print(line("  same, $1 a bet", q(1 / 3, 4), per_race=False))
print(line("  first third only (any rating), over $3", q(1 / 3, 99)))
print(line("  within 4 only (any settle), over $3", q(1.01, 4)))
print(line("  middle third, within 4, over $3", R[(R.sp_ > 1 / 3) & (R.sp_ <= 2 / 3) & (R.off <= 4) & (R.bsp > 3)]))
print(line("  last third, within 4, over $3", R[(R.sp_ > 2 / 3) & (R.off <= 4) & (R.bsp > 3)]))
print(line("  every runner over $3 (reference)", R[R.bsp > 3], per_race=False))
print(line("  every runner (reference)", R, per_race=False))
print("\n===== variants =====")
for settle, off in itertools.product((0.25, 1 / 3, 0.5), (1, 2, 4, 6)):
    print(line("settle %.2f, within %d, over $3" % (settle, off), q(settle, off)))
print()
for lab, x in (("field 8+", q(1 / 3, 4, fmin=8)), ("field 12+", q(1 / 3, 4, fmin=12)), ("over $3 to $30", q(1 / 3, 4, cap=30)), ("over $5", q(1 / 3, 4, floor=5)),
               ("over $10", q(1 / 3, 4, floor=10)), ("$3 to $6", q(1 / 3, 4, cap=6)), ("$6 to $10", q(1 / 3, 4, floor=6, cap=10)), ("$10 to $20", q(1 / 3, 4, floor=10, cap=20)),
               ("$20+", q(1 / 3, 4, floor=20)), ("forecast leader only", q(0, 4)), ("first quarter, within 2, field 8+, to $30", q(0.25, 2, cap=30, fmin=8)),
               ("first quarter, within 4, field 8+, to $30", q(0.25, 4, cap=30, fmin=8))):
    print(line("v1 stand-in, " + lab, x))
