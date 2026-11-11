"""Overlays (value bets) against the Betfair starting price.
Run with PYTHONPATH=. python research/betfair_overlay_test.py
A bet is an overlay when model chance x net Betfair return > threshold. Model chances tried:
  proj   softmax of the logged Proj at 0.20 a point (the dashboard's Rated $ before the noise simulation)
  nett   softmax of TopRate's Nett at 0.20 a point
  direct the finishing-position model's stored chances (data/direct_scores, 14 Oct 2026 on)
Also: overlays restricted by rank and price, sharpness refitted on the first half of the dates, and the price
moves Betfair records (morning average and pre-play average against BSP)."""
import glob, json, os, sys, warnings
import numpy as np, pandas as pd
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from betfair_bsp_test import load_bsp, roi_line, norm, COMM
import runners_io
warnings.filterwarnings("ignore")

b = load_bsp()
df = runners_io.read_runners()
df = df[(df.scratched != 1) & df.date.notna()].copy()
for c in ("wprp_proj", "wpr_nett", "tab_number", "fixed_win_price", "starting_price_sp"):
    df[c] = pd.to_numeric(df[c], errors="coerce")
df["hn"] = df.horse.map(norm)
df["rid"] = df.date + "|" + df.venue.astype(str) + "|" + df.race.astype(str)
ds = {}
for f in sorted(glob.glob("data/direct_scores/*.json")):
    for rid, v in json.load(open(f))["races"].items():
        for tab, p in v.items():
            ds[(float(rid), float(tab))] = p
df["dm"] = [ds.get((r, t)) for r, t in zip(pd.to_numeric(df.race_id, errors="coerce"), df.tab_number)]
m = df.merge(b, on=["date", "hn"], how="left")
g = m.groupby("rid")
m["n"], m["nb"] = g.hn.transform("size"), g.bsp.transform("count")
m["won"] = m.win_lose
m["nw"] = g.win_lose.transform("sum")
F = m[(m.nb >= 0.9 * m.n) & (m.nw == 1) & (m.nb >= 5) & m.bsp.notna()].copy()
F["bbook"] = F.groupby("rid").bsp.transform(lambda x: (1 / x).sum())
F = F[F.bbook.between(0.9, 1.15)]
F["pm"] = (1 / F.bsp) / F.bbook
F["net"] = 1 + (F.bsp - 1) * (1 - COMM)
F["sp"] = F.bsp
print("races %d, %s to %s, commission %.0f%%" % (F.rid.nunique(), F.date.min(), F.date.max(), 100 * COMM))


def chances(R, col, beta):
    e = np.exp(beta * (R[col] - R.groupby("rid")[col].transform("max")))
    return e / e.groupby(R.rid).transform("sum")


def calib(R, lab):
    R = R.assign(evb=pd.cut(R.ev, [0, 0.8, 0.95, 1.05, 1.2, 1.5, 2.5, 99]))
    t = R.groupby("evb").apply(lambda x: pd.Series({"n": len(x), "model %": 100 * x.p.mean(), "market %": 100 * x.pm.mean(), "actual %": 100 * x.won.mean(),
                                                    "ROI %": 100 * (x.won * x.net - 1).mean()}))
    print("  %s: by model edge (chance x net return)" % lab)
    print(t.round(1).to_string())


for col, name in (("wprp_proj", "Proj"), ("wpr_nett", "Nett")):
    R = F[F.groupby("rid")[col].transform(lambda x: x.notna().mean()) >= 0.9].copy()
    R = R[R[col].notna()]
    mid = np.sort(R.date.unique())[R.date.nunique() // 2]
    fit = R[R.date < mid]
    bs = np.linspace(0.05, 0.40, 36)
    bb = bs[int(np.argmax([np.log(chances(fit, col, x)[fit.won == 1]).mean() for x in bs]))]
    print("\n===== %s: %d races; sharpness refitted on the first half %.2f =====" % (name, R.rid.nunique(), bb))
    for beta, lab in ((0.20, "sharpness 0.20"), (bb, "refitted, second half only")):
        X = R if beta == 0.20 else R[R.date >= mid]
        X = X.assign(p=chances(X, col, beta))
        X["ev"] = X.p * X.net
        X["rk"] = X.groupby("rid")[col].rank(ascending=False, method="min")
        print("-- " + lab)
        calib(X, name)
        for th in (1.05, 1.2, 1.5):
            o = X[X.ev > th]
            print(roi_line("  overlay >%.2f, all" % th, o))
            print(roi_line("  overlay >%.2f, model top pick" % th, o[o.rk == 1]))
            print(roi_line("  overlay >%.2f, model rank 2-4" % th, o[o.rk.between(2, 4)]))
            print(roi_line("  overlay >%.2f, BSP under $6" % th, o[o.bsp < 6]))
            print(roi_line("  overlay >%.2f, BSP $6-15" % th, o[o.bsp.between(6, 15)]))
        u = X[X.ev < 0.8]
        print(roi_line("  underlay <0.80 (model says too short)", u))

D = F[F.groupby("rid").dm.transform(lambda x: x.notna().all())].copy()
if D.rid.nunique() > 100:
    D["p"] = D.dm / D.groupby("rid").dm.transform("sum")
    D["ev"] = D.p * D.net
    D["rk"] = D.groupby("rid").p.rank(ascending=False, method="min")
    print("\n===== Direct finishing-position model: %d races (%s to %s) =====" % (D.rid.nunique(), D.date.min(), D.date.max()))
    ll = lambda p: np.log(p[D.won == 1]).mean()
    print("  winner log-lik: model %.4f, Betfair price %.4f" % (ll(D.p), ll(D.pm)))
    calib(D, "direct")
    print(roi_line("  direct top pick", D[D.rk == 1]))
    for th in (1.05, 1.2, 1.5):
        o = D[D.ev > th]
        print(roi_line("  overlay >%.2f, all" % th, o))
        print(roi_line("  overlay >%.2f, model rank 1-4" % th, o[o.rk <= 4]))
        print(roi_line("  overlay >%.2f, BSP under $10" % th, o[o.bsp < 10]))

print("\n===== Price moves Betfair records (all runners) =====")
M = F[(F.morningwap > 1) & (F.ppwap > 1)].copy()
M["mv"] = np.log(M.bsp / M.morningwap)
for lo, hi, lab in ((-9, -0.25, "firmed 22%+ from the morning average"), (-0.25, -0.08, "firmed 8-22%"), (-0.08, 0.08, "steady"), (0.08, 0.25, "drifted 8-22%"), (0.25, 9, "drifted 22%+")):
    x = M[(M.mv > lo) & (M.mv <= hi)]
    print(roi_line("  " + lab + " @BSP", x))
    y = x.assign(bsp=x.morningwap)
    print(roi_line("  " + lab + " @morning average", y))
P = F[F.wprp_proj.notna()].copy()
P["rk"] = P.groupby("rid").wprp_proj.rank(ascending=False, method="min")
P = P[(P.morningwap > 1)]
t = P[P.rk == 1]
print("  Proj top pick: mean ln(BSP / morning average) %+.4f; all runners %+.4f; favourites %+.4f" % (
    np.log(t.bsp / t.morningwap).mean(), np.log(P.bsp / P.morningwap).mean(),
    np.log(P[P.bsp == P.groupby("rid").bsp.transform("min")].pipe(lambda x: x.bsp / x.morningwap)).mean()))
print(roi_line("  Proj top pick @morning average, net", t.assign(bsp=t.morningwap)))
print(roi_line("  Proj top pick that drifted 8%+ @BSP", t[np.log(t.bsp / t.morningwap) > 0.08]))
print(roi_line("  Proj top pick that firmed 8%+ @BSP", t[np.log(t.bsp / t.morningwap) < -0.08]))
