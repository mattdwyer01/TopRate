"""Context-aware Proj built ONLY on ATW figures (21 Oct 2026, owner rule: Proj never uses plain WPR). Run with PYTHONPATH=.
Data: the runner-page store (features.runner_page_runs, ratings as TopRate gives them) and nothing else for ratings. Baseline = the shipped formula (weights
refitted on runs before 2026-01-01). Candidate = baseline + a LightGBM correction learned from context (distance, going, class, grading, field size, barrier,
weight and its change, days since run, last-run margin and finish, jockey effect as of the day). Part 1: held-out rating error (train < 2026-01, early stop on
2025-10..12, test 2026-01..06 and 2026-07..10). Part 2: winner picking on the dashboard's races 4 Jul to 17 Oct (runners.csv + archive), Proj alone and inside
the Rank blend (Proj 0.65, Nett 0.25, Spd 0.10), with log-lik, top pick strike rate and winners inside a shortlist of matched size (2.0 and 3.4 runners)."""
import os
import numpy as np
import pandas as pd
import lightgbm as lgb
from datetime import date
from scipy.optimize import minimize
import speed_rating as sr
from projection import features as F

K = 8
CUT = pd.Timestamp("2026-01-01")
ES_FROM = pd.Timestamp("2025-10-01")

def going_num(s):
    s = s.astype(str)
    n = pd.to_numeric(s.str.extract(r"(\d+)")[0], errors="coerce")
    return n.where(n.notna(), np.where(s.str.contains("Synth|Dirt|Poly|Tapeta", case=False), 4, np.nan))

CLASS_MAP = {"maiden": "MAI", "open": "OPEN"}
def class_code(s):
    s = s.astype(str).str.strip()
    out = s.copy()
    low = s.str.lower()
    out = out.where(~low.eq("maiden"), "MAI").where(~low.eq("open"), "OPEN")
    m = low.str.extract(r"^class (\d)$")[0]; out = out.where(m.isna(), "CLS" + m.fillna(""))
    m = low.str.extract(r"^benchmark (\d+)$")[0]; out = out.where(m.isna(), "BM" + m.fillna(""))
    m = low.str.extract(r"^restricted (\d+)$")[0]; out = out.where(m.isna(), "RST" + m.fillna(""))
    return out

def build(rp):
    """rp: runs (page runs plus target rows with wpr NaN, is_t=1). Returns frame with lag and context features."""
    rp = rp.sort_values(["horse_id", "date", "is_t"], ascending=[True, True, False]).reset_index(drop=True)
    g = rp.groupby("horse_id")
    for k in range(1, K + 1):
        rp[f"r{k}"] = g.wpr.shift(k)
    # earlier runs only count page runs: pseudo rows have NaN wpr so shift skips nothing; make lags skip target rows by working on a page-only index
    return rp

def lags(rp):
    pg = rp[rp.is_t == 0].copy()
    pg = pg.sort_values(["horse_id", "date"])
    # for every row (page or target) find lags among page runs strictly before its date
    out = pd.DataFrame(index=rp.index, columns=[f"r{k}" for k in range(1, K + 1)] + ["n", "d_last", "l_dist", "l_going", "l_wt", "l_mgn", "l_posf", "l_fsz", "l_class"], dtype=float)
    byh = {h: x for h, x in pg.groupby("horse_id")}
    arr_r = np.full((len(rp), K), np.nan); n_ = np.zeros(len(rp)); aux = np.full((len(rp), 8), np.nan)
    hid = rp.horse_id.values; dts = rp.date.values
    for h, ix in rp.groupby("horse_id").indices.items():
        x = byh.get(h)
        if x is None:
            continue
        xd = x.date.values; xw = x.wpr.values; xdist = x.distance.values; xg = x.going_n.values; xwt = x.weightCarried.values
        xm = x.marginFinish.values; xp = (x.positionFinish / x.field_size).values; xf = x.field_size.values
        for i in ix:
            j = np.searchsorted(xd, dts[i], side="left")   # runs strictly before
            n_[i] = j
            if j == 0:
                continue
            take = xw[max(0, j - K):j][::-1]
            arr_r[i, :len(take)] = take
            aux[i] = [(dts[i] - xd[j - 1]) / np.timedelta64(1, "D"), xdist[j - 1], xg[j - 1], xwt[j - 1], xm[j - 1], xp[j - 1], xf[j - 1], 0]
    for k in range(K):
        rp[f"r{k+1}"] = arr_r[:, k]
    rp["n"] = n_
    for c, nm in enumerate(["d_last", "l_dist", "l_going", "l_wt", "l_mgn", "l_posf", "l_fsz", "_z"]):
        rp[nm] = aux[:, c]
    return rp

def prep_runs():
    rp = F.runner_page_runs().copy()
    rp["is_t"] = 0
    rp["going_n"] = going_num(rp.going)
    rp["grade"] = pd.to_numeric(rp.trackGrading, errors="coerce")
    for c in ("distance", "weightCarried", "barrier", "field_size", "marginFinish", "positionFinish"):
        rp[c] = pd.to_numeric(rp[c], errors="coerce")
    rp["cls"] = rp.race_class.astype(str)
    return rp

def formula_fit(rp):
    tr = rp[(rp.date < CUT) & (rp.is_t == 0)]
    coef = {}
    for n in range(1, K + 1):
        a = tr[tr.n.clip(upper=K) == n]
        c = [f"r{k}" for k in range(1, n + 1)]
        a = a.dropna(subset=c)
        coef[n] = np.linalg.lstsq(np.c_[np.ones(len(a)), a[c].values], a.wpr.values, rcond=None)[0]
    return coef

def formula_pred(rp, coef):
    f = np.full(len(rp), np.nan)
    kk = rp.n.clip(upper=K).values
    for n in range(1, K + 1):
        m = (kk == n)
        c = [f"r{k}" for k in range(1, n + 1)]
        X = rp.loc[m, c].values
        ok = ~np.isnan(X).any(axis=1)
        idx = np.where(m)[0][ok]
        f[idx] = coef[n][0] + X[ok] @ coef[n][1:]
    return f

def add_context(rp, f, with_resid=True):
    rp["f"] = f
    r = rp[[f"r{k}" for k in range(1, K + 1)]].values
    rp["mean3"] = np.nanmean(r[:, :3], axis=1) if True else 0
    rp["max4"] = np.nanmax(np.where(np.isnan(r[:, :4]), -1e9, r[:, :4]), axis=1)
    rp.loc[rp.max4 < -1e8, "max4"] = np.nan
    rp["std4"] = np.nanstd(r[:, :4], axis=1)
    rp["dist_chg"] = rp.distance - rp.l_dist
    rp["going_chg"] = rp.going_n - rp.l_going
    rp["wt_chg"] = rp.weightCarried - rp.l_wt
    rp["barr_f"] = rp.barrier / rp.field_size
    rp["ldays"] = np.log1p(rp.d_last)
    rp["resid"] = rp.wpr - rp.f
    # jockey effect as of the day: shrunk mean residual of the jockey's earlier page runs (strictly before the date)
    pg = rp[(rp.is_t == 0) & rp.resid.notna()].groupby(["jockey", "date"]).resid.agg(["sum", "count"]).reset_index().sort_values(["jockey", "date"])
    pg["cs"] = pg.groupby("jockey")["sum"].cumsum() - pg["sum"]
    pg["cn"] = pg.groupby("jockey")["count"].cumsum() - pg["count"]
    rp = rp.merge(pg[["jockey", "date", "cs", "cn"]], on=["jockey", "date"], how="left")
    # target rows (jockey, date not in pg): take the latest earlier cumulative
    pg2 = pg.assign(cs=pg.cs + pg["sum"], cn=pg.cn + pg["count"])
    miss = rp.cs.isna()
    if miss.any():
        t = rp.loc[miss, ["jockey", "date"]].reset_index().sort_values("date")
        base = pg2[["jockey", "date", "cs", "cn"]].rename(columns={"date": "d0"}).sort_values("d0")
        mm = pd.merge_asof(t, base, left_on="date", right_on="d0", by="jockey", direction="backward", allow_exact_matches=False)
        rp.loc[mm["index"].values, "cs"] = mm["cs"].values
        rp.loc[mm["index"].values, "cn"] = mm["cn"].values
    rp["cn"] = rp.cn.fillna(0); rp["cs"] = rp.cs.fillna(0)
    rp["jock_eff"] = rp.cs / (rp.cn + 20.0)
    rp["cls_c"] = rp.cls.astype("category")
    return rp

FEATS = ["f", "n", "mean3", "max4", "std4", "ldays", "distance", "dist_chg", "going_n", "going_chg", "grade", "field_size", "barr_f", "weightCarried", "wt_chg",
         "l_mgn", "l_posf", "jock_eff", "cn", "cls_c"]

def main():
    rp = prep_runs()
    rp = lags(rp)
    coef = formula_fit(rp)
    f = formula_pred(rp, coef)
    rp = add_context(rp, f)
    pg = rp[(rp.is_t == 0) & rp.f.notna()].copy()
    tr = pg[pg.date < ES_FROM]; va = pg[(pg.date >= ES_FROM) & (pg.date < CUT)]
    mdl = lgb.LGBMRegressor(n_estimators=3000, learning_rate=0.03, num_leaves=31, min_child_samples=100, subsample=0.8, subsample_freq=1, colsample_bytree=0.8, reg_lambda=5, verbose=-1)
    mdl.fit(tr[FEATS], tr.resid, eval_set=[(va[FEATS], va.resid)], callbacks=[lgb.early_stopping(100, verbose=False)])
    print("trees", mdl.best_iteration_, "train", len(tr), "valid", len(va))
    for name, a in (("test 2026-01..06", pg[(pg.date >= CUT) & (pg.date < "2026-07-01")]), ("test 2026-07..10", pg[pg.date >= "2026-07-01"])):
        c = mdl.predict(a[FEATS])
        print(f"\n{name}: n={len(a)}  RMSE formula {np.sqrt((a.resid**2).mean()):.3f}  formula+context {np.sqrt(((a.resid - c)**2).mean()):.3f}")
        for lab, m in (("1-2 runs", a.n <= 2), ("3-5", (a.n >= 3) & (a.n <= 5)), ("6-8", (a.n >= 6) & (a.n <= 8)), ("9+", a.n >= 9)):
            b = a[m]; cc = mdl.predict(b[FEATS])
            print(f"   {lab:9s} n={len(b):5d} formula {np.sqrt((b.resid**2).mean()):.3f}  context {np.sqrt(((b.resid - cc)**2).mean()):.3f}")
    imp = pd.Series(mdl.booster_.feature_importance("gain"), index=FEATS).sort_values(ascending=False)
    print("\nfeature gain share:", (imp / imp.sum()).round(3).head(10).to_dict())
    winner_test(rp, mdl, coef)

def winner_test(rp_all, mdl, coef):
    KEY = ["date", "venue", "race", "horse"]
    cols = KEY + ["horse_id", "wpr_nett", "scratched", "won", "fixed_win_price", "starting_price_sp", "field_source", "spd_fig", "distance", "race_class",
                  "barrier", "weight_carried", "jockey", "going", "track_grading"]
    rd = lambda p: pd.read_csv(p, low_memory=False, usecols=lambda c: c in cols)
    leg = pd.concat([rd("archive/toprate/toprate_runners_archive.csv.gz"), rd("archive/toprate/toprate_runners.csv")], ignore_index=True)
    cur = pd.concat([rd("runners_archive.csv.gz"), rd("runners.csv")], ignore_index=True)
    for x in (leg, cur):
        x["date"] = x["date"].astype(str).str[:10]; x["race"] = x["race"].astype(str)
    d = leg.drop_duplicates(KEY, keep="last").set_index(KEY).combine_first(cur.drop_duplicates(KEY, keep="last").set_index(KEY)).reset_index()
    d = d[(d.date >= "2026-04-26") & (d.date <= "2026-10-17")]
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
    d["fsz"] = d.groupby("rk").won.transform("size")
    d = d[d.fsz >= 5].copy()
    # target rows
    t = pd.DataFrame(dict(horse_id=pd.to_numeric(d.horse_id, errors="coerce"), date=pd.to_datetime(d.date), wpr=np.nan, jockey=d.jockey.astype(str),
                          distance=pd.to_numeric(d.distance, errors="coerce"), going=d.going.astype(str), weightCarried=pd.to_numeric(d.weight_carried, errors="coerce"),
                          barrier=pd.to_numeric(d.barrier, errors="coerce"), field_size=d.fsz.astype(float), cls=class_code(d.race_class),
                          trackGrading=pd.to_numeric(d.track_grading, errors="coerce"), marginFinish=np.nan, positionFinish=np.nan, track="", is_t=1))
    t["going_n"] = going_num(t.going); t["grade"] = t.trackGrading
    t["tid"] = np.arange(len(t))
    t = t.dropna(subset=["horse_id"])
    base = rp_all[rp_all.is_t == 0][["horse_id", "date", "wpr", "jockey", "distance", "going", "weightCarried", "barrier", "field_size", "cls", "trackGrading",
                                    "marginFinish", "positionFinish", "track", "is_t", "going_n", "grade"]].copy()
    base["tid"] = -1
    allr = pd.concat([base, t], ignore_index=True).sort_values(["horse_id", "date", "is_t"], ascending=[True, True, False]).reset_index(drop=True)
    allr = lags(allr)
    f = formula_pred(allr, coef)
    allr = add_context(allr, f)
    tt = allr[allr.is_t == 1].copy()
    tt = tt[tt.f.notna()]
    tt["ctx"] = tt.f + mdl.predict(tt[FEATS])
    out = d.reset_index(drop=True).copy(); out["tid"] = np.arange(len(out))
    out = out.merge(tt[["tid", "f", "ctx"]], on="tid", how="left")
    out["rkid"] = out.rk.astype("category").cat.codes
    cov = out.groupby("rk").f.apply(lambda s: s.notna().mean())
    COV = float(os.environ.get("COV", "0.8")); out = out[out.rk.isin(cov[cov >= COV].index)].copy()
    print(f"\nwinner test: {out.rk.nunique()} races, {len(out)} runners (formula coverage >= {COV:.0%} of the field)")
    for nm, c in (("formula", "f"), ("context", "ctx"), ("nett", "wpr_nett"), ("spd", "spd_fig")):
        out[c] = pd.to_numeric(out[c], errors="coerce"); gm = out.groupby("rk")[c]
        out["z_" + nm] = ((out[c] - gm.transform("mean")) / gm.transform("std").replace(0, np.nan)).fillna(0.0)
    out.to_pickle(os.environ.get("PC_OUT", "pc.pkl"))
    report(out)

def nll(w, X, won, rid):
    s = X @ w; m = pd.Series(s).groupby(rid).transform("max").values; e = np.exp(s - m)
    lse = np.log(pd.Series(e).groupby(rid).transform("sum").values) + m
    return -(s - lse)[won == 1].mean()
def evalscore(df, s):
    t = df.assign(s=s); m = t.groupby("rkid").s.transform("max"); e = np.exp(t.s - m)
    lse = np.log(e.groupby(t.rkid).transform("sum")) + m
    return (t.s - lse)[t.won == 1].mean(), t.loc[t.groupby("rkid").s.idxmax()].won.mean() * 100
def capture(df, s, sizes=(2.0, 3.4)):
    t = df.assign(gap=pd.Series(s, index=df.index).groupby(df.rkid).transform("max") - s); res = []
    for target in sizes:
        lo, hi = 0.0, 30.0
        for _ in range(40):
            mid = (lo + hi) / 2; size = (t.gap <= mid).groupby(t.rkid).sum().mean(); lo, hi = (mid, hi) if size < target else (lo, mid)
        res.append(100 * (t[t.won == 1].gap <= hi).mean())
    return res
def report(out):
    dates = sorted(out.date.unique()); half = dates[len(dates) // 2]
    A, B = out[out.date < half], out[out.date >= half]
    def run(label, cols, fixed=None):
        r = []
        for tr, te in ((A, B), (B, A)):
            w = fixed if fixed is not None else minimize(nll, np.full(len(cols), .2), args=(tr[cols].values, tr.won.values, tr.rkid.values), method="L-BFGS-B").x
            s = te[cols].values @ w; ll, top = evalscore(te, s); c = capture(te, pd.Series(s, index=te.index)); r.append((ll, top, c[0], c[1]))
        m = np.mean(r, axis=0)
        print(f"{label:36s} LL {m[0]:.4f}  top1 {m[1]:.1f}%  in-2.0 {m[2]:.1f}%  in-3.4 {m[3]:.1f}%")
    for nm in ("formula", "context", "nett", "spd"): run("only " + nm, ["z_" + nm])
    run("rank blend, formula as Proj", ["z_formula", "z_nett", "z_spd"], np.array([.65, .25, .10]))
    run("rank blend, context as Proj", ["z_context", "z_nett", "z_spd"], np.array([.65, .25, .10]))
    run("fitted: formula + nett + spd", ["z_formula", "z_nett", "z_spd"])
    run("fitted: context + nett + spd", ["z_context", "z_nett", "z_spd"])

if __name__ == "__main__":
    main()
