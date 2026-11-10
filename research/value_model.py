"""Value model, first build (10 Nov 2026): learn where the Betfair starting price (BSP) is wrong.

The model starts from the Betfair chance of each runner (1 / BSP, normalised over the race) and learns only a
correction to it (LightGBM with a per-race softmax loss, the Betfair log chance as a fixed offset). An input the
price already covers earns nothing. Output per runner: model chance, and "value points" = 5 x ln(model chance /
Betfair chance), i.e. the disagreement in rating points on the Proj scale (5 points per ln chance, sharpness 0.20).

Inputs are things a market may misweigh, all known before the race and built from the results files:
form level and shape against the field, last-run excuses (steward / video comment words), last-start winners,
spell and back-up, class and distance changes, draw, and how each jockey, trainer, sire and venue draw has done
AGAINST THE PRICE in the past (as-of, shrunk). No price history other than the BSP itself.

Walk-forward: fit on everything before October of a year, early stop on that year's last quarter, test on the next year
(2024, 2025, 2026). The betting rule is fixed: model chance x net return > 1.00 and BSP under $30. VM_SINGLE=1 runs one split.
  PYTHONPATH=. python research/value_model.py
"""
import glob
import os
import re
import sys
import warnings

import lightgbm as lgb
import numpy as np
import pandas as pd

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from betfair_bsp_test import load_bsp, norm, nsw_flag, COMM_NSW, COMM_OTHER  # noqa: E402

warnings.filterwarnings("ignore")
COMM = float(os.environ.get("BSP_COMM", "0.08"))
FIT_END, VAL_END = os.environ.get("VM_FIT_END", "2025-10-01"), os.environ.get("VM_VAL_END", "2026-01-01")
EXCUSE = r"check|block|held up|hamper|crowd|bump|tighten|squeez|no clear|unable to obtain|slow|missed the|dwelt|wide|without cover|lame|vet|bled|arrhythm|resent|hung|laid|lost .{0,12}plate|saddle"


def nk(x):
    if not isinstance(x, str):
        return None
    t = re.sub(r"[^A-Za-z\s'-]", "", x).split()
    return (t[0][0] + t[-1]).lower().replace("'", "").replace("-", "") if t else None


def asof_mean(df, key, val, k):
    """shrunk mean of val over the key's rows on EARLIER dates: sum / (n + k)"""
    t = df[[key, "date", val]].dropna()
    a = t.groupby([key, "date"])[val].agg(["sum", "count"]).reset_index().sort_values("date")
    a["cs"] = a.groupby(key)["sum"].cumsum() - a["sum"]
    a["cn"] = a.groupby(key)["count"].cumsum() - a["count"]
    m = df[[key, "date"]].merge(a[[key, "date", "cs", "cn"]], on=[key, "date"], how="left")
    return (m.cs.fillna(0) / (m.cn.fillna(0) + k)).values, m.cn.fillna(0).values


def load(extra=(), keep_trials=False):
    use = list(extra) + ["race_id", "date", "horse_id", "horse", "track", "distance", "going", "wpr", "weightCarried", "barrier", "priceStarting", "positionFinish",
           "marginFinish", "isBarrierTrial", "is_jumpout", "race_class", "jockey", "trainer", "horse_age", "horse_sex", "sire", "comments_steward", "comments_video"]
    fs = [f for f in sorted(glob.glob("race_results_20*.csv.gz")) if re.search(r"results_20(2[0-6])\.csv", f)]
    r = pd.concat([pd.read_csv(f, usecols=lambda c: c in use, low_memory=False) for f in fs], ignore_index=True)
    trials = r[(r.isBarrierTrial == True) | (r.is_jumpout == True)].copy() if keep_trials else None  # noqa: E712
    r = r[(r.isBarrierTrial != True) & (r.is_jumpout != True)]  # noqa: E712
    r = r[~r.race_class.astype(str).str.contains("Hurdle|Steeple", case=False)]
    r = r.drop_duplicates(["race_id", "horse_id"]).sort_values(["horse_id", "date", "race_id"]).reset_index(drop=True)
    for c in ("wpr", "priceStarting", "positionFinish", "marginFinish", "distance", "weightCarried", "barrier", "horse_age"):
        r[c] = pd.to_numeric(r[c], errors="coerce")
    r["sp"] = r.priceStarting.where(r.priceStarting > 1)
    r["won"] = (r.positionFinish == 1).astype(float)
    g = r.groupby("race_id")
    r["nr"] = g.horse_id.transform("size")
    r["sp_book"] = g.sp.transform(lambda x: (1 / x).sum())
    r["sp_ok"] = g.sp.transform(lambda x: x.notna().all()) & r.sp_book.between(1.05, 2.0)
    r["spm"] = np.where(r.sp_ok, (1 / r.sp) / r.sp_book, np.nan)        # SP chance, margin taken out
    r["ae"] = r.won - r.spm                                              # result against the price
    r["gs"] = pd.to_numeric(r.going.astype(str).str.extract(r"(\d+)")[0], errors="coerce")
    r["wet"] = (r.gs >= 5).astype(float)
    r["finpct"] = (r.positionFinish - 1) / (r.nr - 1)
    r["barfrac"] = (r.barrier - 1) / (r.nr - 1)
    r["jk"], r["tk"] = r.jockey.map(nk), r.trainer.map(nk)
    txt = (r.comments_steward.fillna("") + " " + r.comments_video.fillna("")).str.lower()
    r["excuse"] = txt.str.contains(EXCUSE, regex=True).astype(float)
    r["has_txt"] = (txt.str.len() > 3).astype(float)
    r["sex"] = r.horse_sex.astype(str).str.upper().str[:1].map({"G": 0, "M": 1, "F": 2, "C": 3, "H": 4, "R": 5})
    return (r, trials) if keep_trials else r


def features(r):
    g = r.groupby("horse_id")
    F = {}
    lw = pd.concat([g.wpr.shift(k) for k in range(1, 9)], axis=1)
    F["w1"], F["m3"], F["m8"], F["max8"], F["sd8"] = lw.iloc[:, 0], lw.iloc[:, :3].mean(axis=1), lw.mean(axis=1), lw.max(axis=1), lw.std(axis=1)
    F["trend"] = F["w1"] - F["m8"]
    F["nruns"] = g.cumcount().clip(upper=30).astype(float)
    F["days"] = g.date.diff().dt.days
    F["firstup"] = (F["days"] >= 60).astype(float)
    F["backup"] = (F["days"] <= 9).astype(float)
    d2 = g.date.diff().dt.days.groupby(r.horse_id).shift(1)
    F["secondup"] = ((d2 >= 60) & (F["days"] < 60)).astype(float)
    F["dchg"] = r.distance - g.distance.shift(1)
    F["wchg"] = r.weightCarried - g.weightCarried.shift(1)
    F["l_fin"] = g.finpct.shift(1)
    F["l_mar"] = g.marginFinish.shift(1).clip(0, 30)
    F["l_won"] = g.won.shift(1)
    F["l_excuse"] = g.excuse.shift(1)
    F["l_txt"] = g.has_txt.shift(1)
    F["l_bad"] = ((lw.iloc[:, 0] - lw.iloc[:, 1:4].mean(axis=1)) < -12).astype(float).where(lw.iloc[:, 0].notna())
    F["l_bad_exc"] = F["l_bad"] * F["l_excuse"]
    F["l_ae"] = g.ae.shift(1)                       # beat or missed its price last time
    F["ae3"] = pd.concat([g.ae.shift(k) for k in (1, 2, 3)], axis=1).mean(axis=1)
    F["l_sp"] = np.log(g.sp.shift(1))
    F["wins8"] = pd.concat([g.won.shift(k) for k in range(1, 9)], axis=1).sum(axis=1)
    F["l_jk_same"] = (r.jk == g.jk.shift(1)).astype(float).where(g.jk.shift(1).notna())
    F["exc_rate4"] = pd.concat([g.excuse.shift(k) for k in range(1, 5)], axis=1).mean(axis=1)
    F = pd.DataFrame(F)
    d = pd.concat([r, F], axis=1)
    # how connections, sires and draws have done against the price before today
    d["jk_ae"], d["jk_n"] = asof_mean(d, "jk", "ae", 150)
    d["tk_ae"], d["tk_n"] = asof_mean(d, "tk", "ae", 150)
    d["jt"] = d.jk.astype(str) + "|" + d.tk.astype(str)
    d["jt_ae"], _ = asof_mean(d, "jt", "ae", 60)
    d["jk_win"], _ = asof_mean(d.assign(w=d.won - 0.1), "jk", "w", 100)
    d["tk_win"], _ = asof_mean(d.assign(w=d.won - 0.1), "tk", "w", 100)
    d["sire_wet"] = d.sire.astype(str) + "|" + d.wet.astype(int).astype(str)
    d["sire_ae"], _ = asof_mean(d, "sire", "ae", 200)
    d["sirewet_ae"], _ = asof_mean(d, "sire_wet", "ae", 150)
    d["dband"] = (d.distance / 400).round()
    d["sire_d"] = d.sire.astype(str) + "|" + d.dband.astype(str)
    d["sired_ae"], _ = asof_mean(d, "sire_d", "ae", 150)
    d["third"] = np.minimum((d.barfrac * 3).fillna(1).astype(int), 2)
    d["vdraw"] = d.track.astype(str) + "|" + (d.distance / 200).round().astype(str) + "|" + d.third.astype(str)
    d["draw_ae"], _ = asof_mean(d, "vdraw", "ae", 150)
    d["tk_fu"] = d.tk.astype(str) + "|" + d.firstup.astype(int).astype(str)
    d["tkfu_ae"], _ = asof_mean(d, "tk_fu", "ae", 100)
    d["tk_trk"] = d.tk.astype(str) + "|" + d.track.astype(str)
    d["tktrk_ae"], _ = asof_mean(d, "tk_trk", "ae", 80)
    return d


BASE = ["w1", "m3", "m8", "max8", "sd8", "trend", "nruns", "days", "firstup", "backup", "secondup", "dchg", "wchg", "l_fin", "l_mar", "l_won", "l_excuse", "l_txt",
        "l_bad", "l_bad_exc", "l_ae", "ae3", "l_sp", "wins8", "l_jk_same", "exc_rate4", "jk_ae", "tk_ae", "jt_ae", "jk_win", "tk_win", "sire_ae", "sirewet_ae",
        "sired_ae", "draw_ae", "tkfu_ae", "tktrk_ae", "barfrac", "nr", "distance", "gs", "weightCarried", "horse_age", "sex"]
REL = ["w1", "m3", "m8", "max8", "trend", "l_fin", "l_ae", "ae3", "jk_ae", "tk_ae", "jk_win", "tk_win", "weightCarried", "days"]


def ginfo(df):
    s = df.groupby("race_id", sort=False).size().values
    return s, np.concatenate([[0], np.cumsum(s)[:-1]])


def soft(df, z):
    s, st = ginfo(df)
    z = z - np.repeat(np.maximum.reduceat(z, st), s)
    e = np.exp(z)
    return e / np.repeat(np.add.reduceat(e, st), s)


def roi_line(label, d):
    if len(d) == 0:
        return "%-46s n=0" % label
    w = d.won.values
    pnl = w * (d.bsp.values - 1) * (1 - d.comm.values) - (1 - w)
    dd = d.date.values
    mid = np.sort(dd)[len(dd) // 2]
    o = np.sort(pnl)[::-1]
    n = len(d)
    return "%-46s n=%6d (%.2f a race) win %5.1f%% avg $%6.2f ROI %+6.1f%%  halves %+6.1f/%+6.1f  ex3 %+6.1f ex10 %+6.1f" % (
        label, n, n / max(d.race_id.nunique(), 1), 100 * w.mean(), d.bsp.mean(), 100 * pnl.mean(), 100 * pnl[dd < mid].mean(), 100 * pnl[dd >= mid].mean(),
        100 * (pnl.sum() - o[:3].sum()) / n, 100 * (pnl.sum() - o[:10].sum()) / n)


def main():
    b = load_bsp()
    r = load()
    r["date"] = pd.to_datetime(r.date)
    d = features(r)
    d, FE = prepare(d, b)
    walk(d, FE)


def prepare(d, b, extra_feats=()):
    d = d[d.date >= "2022-12-31"].copy()
    d["ds"] = d.date.dt.strftime("%Y-%m-%d")
    d["hn"] = d.horse.map(norm)
    d = d.merge(b[["date", "hn", "bsp", "win_lose"]].rename(columns={"date": "ds"}), on=["ds", "hn"], how="left")
    g = d.groupby("race_id")
    ok = g.bsp.transform(lambda x: x.notna().all()) & (g.won.transform("sum") == 1) & (d.nr >= 5)
    d = d[ok].copy()
    d["book"] = d.groupby("race_id").bsp.transform(lambda x: (1 / x).sum())
    d = d[d.book.between(0.95, 1.15)].sort_values(["date", "race_id"]).reset_index(drop=True)
    d["nsw"] = nsw_flag(d.track)
    d["comm"] = np.where(d.nsw, COMM_NSW, COMM_OTHER)
    print("NSW share of runners %.1f%% (commission %.0f%%, elsewhere %.0f%%)" % (100 * d.nsw.mean(), 100 * COMM_NSW, 100 * COMM_OTHER))
    d["pm"] = (1 / d.bsp) / d.book
    d["lpm"] = np.log(d.pm)
    gk = d.groupby("race_id")
    for c in REL:
        d["r_" + c] = d[c] - gk[c].transform("mean")
        d["k_" + c] = gk[c].rank(pct=True)
    d["fav"] = (d.pm == gk.pm.transform("max")).astype(float)
    d["pm_rank"] = gk.pm.rank(ascending=False)
    FE = BASE + ["r_" + c for c in REL] + ["k_" + c for c in REL] + ["lpm", "fav", "pm_rank"] + list(extra_feats)
    print("complete races with a Betfair price for every runner: %d (%s to %s), runners %d, inputs %d" % (
        d.race_id.nunique(), d.ds.min(), d.ds.max(), len(d), len(FE)))

    # which price is the better baseline: SP with the margin taken out, or the Betfair price
    c = d[d.spm.notna()]
    c = c[c.groupby("race_id").spm.transform(lambda x: x.notna().all())]
    w = c[c.won == 1]
    dif = np.log(w.pm) - np.log(w.spm)
    print("winner log-lik on %d races: SP (margin removed) %.4f, Betfair %.4f, Betfair better by %+.4f (se %.4f)" % (
        len(w), np.log(w.spm).mean(), np.log(w.pm).mean(), dif.mean(), dif.std() / np.sqrt(len(w))))

    return d, FE


def walk(d, FE):
    folds = [("2023-10-01", "2024-01-01", "2025-01-01"), ("2024-10-01", "2025-01-01", "2026-01-01"), ("2025-10-01", "2026-01-01", "2027-01-01")]
    if os.environ.get("VM_SINGLE") == "1":
        folds = [(FIT_END, VAL_END, "2027-01-01")]
    allte = []
    for fit_end, val_end, test_end in folds:
        print("\n\n########## fit to %s, early stop to %s, test to %s ##########" % (fit_end, val_end, test_end))
        te = run(d, FE, fit_end, val_end, test_end)
        if te is not None:
            allte.append(te)
    if len(allte) > 1:
        A = pd.concat(allte)
        print("\n\n########## all test years together; rule fixed before the 2024 and 2025 tests were seen: edge > 1.00, BSP under $30 ##########")
        x = A[(A.ev > 1.0) & (A.bsp < 30)].copy()
        x["pnl"] = x.won * (x.bsp - 1) * (1 - x.comm) - (1 - x.won)
        days = x.groupby("ds").pnl.agg(["sum", "size"])
        rng = np.random.default_rng(1)
        bs = np.array([(lambda s_: s_["sum"].sum() / s_["size"].sum())(days.sample(len(days), replace=True, random_state=int(rng.integers(1e9)))) for _ in range(2000)])
        print(roi_line("value bets, all test years", x))
        print("90%% range by day %+.1f%% to %+.1f%%, chance above zero %.0f%%; model said %.2f%% winners, Betfair %.2f%%, actual %.2f%%" % (
            100 * np.quantile(bs, 0.05), 100 * np.quantile(bs, 0.95), 100 * (bs > 0).mean(), 100 * x.p.mean(), 100 * x.pm.mean(), 100 * x.won.mean()))
        for lab, sub in (("NSW (10%)", x[x.nsw]), ("other states (8%)", x[~x.nsw])):
            print(roi_line("  " + lab, sub))
        print(x.assign(q=x.ds.str[:4] + "Q" + ((x.ds.str[5:7].astype(int) - 1) // 3 + 1).astype(str)).groupby("q").pnl.agg(["size", "mean"]).round(3).T.to_string())
        w = A[A.won == 1]
        dif = np.log(w.p) - np.log(w.pm)
        print("winner log-lik gain over Betfair, all test years: %+.4f (se %.4f) on %d races" % (dif.mean(), dif.std() / np.sqrt(len(w)), len(w)))
        A[["ds", "race_id", "track", "nsw", "comm", "horse", "bsp", "pm", "p", "vp", "ev", "won"]].to_csv(os.environ.get("VM_OUT", "/tmp/value_model_test.csv.gz"), index=False)
        return A
    return None


def run(d, FE, FIT_END, VAL_END, TEST_END):
    tr, va, te = d[d.ds < FIT_END], d[(d.ds >= FIT_END) & (d.ds < VAL_END)], d[(d.ds >= VAL_END) & (d.ds < TEST_END)].copy()
    print("fit %d races, validation %d, test %d" % (tr.race_id.nunique(), va.race_id.nunique(), te.race_id.nunique()))
    if tr.race_id.nunique() < 500 or va.race_id.nunique() < 200 or te.race_id.nunique() < 200:
        print("not enough Betfair history downloaded yet for the split")
        return None

    def obj(df):
        s, st = ginfo(df)
        y = df.won.values

        def f(preds, ds):
            z = preds - np.repeat(np.maximum.reduceat(preds, st), s)
            e = np.exp(z)
            p = e / np.repeat(np.add.reduceat(e, st), s)
            return p - y, np.maximum(p * (1 - p), 1e-6)
        return f

    def ev(df):
        y = df.won.values

        def f(preds, ds):
            return "ll", float(np.log(soft(df, preds)[y == 1].clip(1e-12)).mean()), True
        return f

    res = {}
    for seed in [int(x) for x in os.environ.get('VM_SEEDS', '1,2,3').split(',')]:
        P = dict(learning_rate=0.02, num_leaves=8, min_data_in_leaf=400, feature_fraction=0.5, bagging_fraction=0.7, bagging_freq=1, lambda_l2=50,
                 verbose=-1, objective=obj(tr), metric="None", seed=seed)
        dtr = lgb.Dataset(tr[FE], label=tr.won.values, init_score=tr.lpm.values)
        dva = lgb.Dataset(va[FE], label=va.won.values, init_score=va.lpm.values, reference=dtr)
        m = lgb.train(P, dtr, num_boost_round=1500, valid_sets=[dva], feval=ev(va), callbacks=[lgb.early_stopping(100, verbose=False)])
        res[seed] = m
        print("seed %d: %d trees, validation log-lik %.4f (Betfair alone %.4f)" % (
            seed, m.best_iteration, np.log(soft(va, va.lpm.values + m.predict(va[FE]))[va.won == 1]).mean(), np.log(va.pm[va.won == 1]).mean()))
    for df in (va, te):
        corr = np.mean([m.predict(df[FE]) for m in res.values()], axis=0)
        df["p"] = soft(df, df.lpm.values + corr)
        df["vp"] = 5 * (np.log(df.p) - np.log(df.pm))
        df["ev"] = df.p * (1 + (df.bsp - 1) * (1 - df.comm))
    imp = pd.Series(np.mean([m.feature_importance("gain") for m in res.values()], axis=0), index=FE)
    print("\ninputs by share of gain: " + ", ".join("%s %.0f%%" % (k, 100 * v) for k, v in (imp / max(imp.sum(), 1e-9)).sort_values(ascending=False).head(15).items()))

    for name, df in (("validation (2025 Q4)", va), ("TEST (2026)", te)):
        w = df[df.won == 1]
        dif = np.log(w.p) - np.log(w.pm)
        print("\n===== %s: %d races =====" % (name, df.race_id.nunique()))
        print("winner log-lik: Betfair %.4f, value model %.4f, gain %+.4f (se %.4f)" % (np.log(w.pm).mean(), np.log(w.p).mean(), dif.mean(), dif.std() / np.sqrt(len(w))))
        print("value points: sd %.2f, 1%% / 99%% %.1f / %.1f" % (df.vp.std(), df.vp.quantile(0.01), df.vp.quantile(0.99)))
        t = df.assign(band=pd.cut(df.vp, [-99, -1, -0.5, -0.2, 0.2, 0.5, 1, 99])).groupby("band").apply(lambda x: pd.Series({
            "n": len(x), "Betfair %": 100 * x.pm.mean(), "model %": 100 * x.p.mean(), "actual %": 100 * x.won.mean(),
            "ROI % net": 100 * (x.won * (x.bsp - 1) * (1 - x.comm) - (1 - x.won)).mean()}))
        print("by value points (model against Betfair):")
        print(t.round(2).to_string())
        for th in (1.0, 1.02, 1.05, 1.10):
            print(roi_line("bet when chance x net return > %.2f" % th, df[df.ev > th]))
        for lo, hi in ((1, 4), (4, 10), (10, 30), (30, 1001)):
            print(roi_line("  > 1.00 and BSP $%g-%g" % (lo, hi), df[(df.ev > 1.0) & (df.bsp >= lo) & (df.bsp < hi)]))
        print(roi_line("top value point runner of each race", df[df.vp == df.groupby("race_id").vp.transform("max")]))
        print(roi_line("all runners (reference)", df))
        if name.startswith("TEST"):
            print(roi_line("RULE: edge > 1.00 and BSP under $30", df[(df.ev > 1.0) & (df.bsp < 30)]))
    return te


if __name__ == "__main__":
    main()
