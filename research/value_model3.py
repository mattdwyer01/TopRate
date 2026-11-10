"""Value model, third pass: tweaks to the Betfair-correction model, each judged on the same walk-forward (10 Nov 2026).

The model is a correction to the Betfair starting price (per-race softmax loss, ln Betfair chance as a fixed offset), inputs as value_model2 with the
meeting-bias and pace families. Test years 2024, 2025, 2026 (fit to October of the year before, early stop on that year's last quarter).
Bet rule as fixed before: model chance x net return > 1.00 and Betfair price under $30; commission 10% NSW, 8% elsewhere.
Tweaks:
  pre     more training history: 2020-07 to 2022 races added with the starting price (margin removed) as the offset, because Betfair files start in 2023
  shrink  the correction multiplied by a factor chosen on the validation quarter (tree corrections tend to be too large)
  lin     a linear version of the correction (conditional logit, ridge), and its average with the tree model
  slow    smaller trees, slower learning, more seeds
  noprice the price is the offset only, not also an input
  thr     the bet threshold chosen on the validation quarter instead of fixed at 1.00
  PYTHONPATH=. python research/value_model3.py build        (once, about 5 minutes: writes /tmp/value_model3_frame.pkl)
  PYTHONPATH=. python research/value_model3.py run [names]  (ref pre pre_half slow noprice lin pre_lin ...)
"""
import os
import sys
import warnings

import lightgbm as lgb
import numpy as np
import pandas as pd
from scipy.optimize import minimize

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import value_model as VM  # noqa: E402
import value_model2 as VM2  # noqa: E402
from betfair_bsp_test import load_bsp, norm, nsw_flag, COMM_NSW, COMM_OTHER  # noqa: E402

warnings.filterwarnings("ignore")
CACHE = os.environ.get("VM3_CACHE", "/tmp/value_model3_frame.pkl")
EXTRA = sorted(set(VM2.FAM["bias"] + VM2.FAM["pace"]))
FE_ALL = VM.BASE + ["r_" + c for c in VM.REL] + ["k_" + c for c in VM.REL] + ["lpm", "fav", "pm_rank"] + EXTRA
FOLDS = [("2023-10-01", "2024-01-01", "2025-01-01"), ("2024-10-01", "2025-01-01", "2026-01-01"), ("2025-10-01", "2026-01-01", "2027-01-01")]


def build():
    d = VM2.build()
    b = load_bsp()
    d = d[d.date >= "2020-07-01"].copy()
    d["ds"] = d.date.dt.strftime("%Y-%m-%d")
    d["hn"] = d.horse.map(norm)
    d = d.merge(b[["date", "hn", "bsp", "win_lose"]].drop_duplicates(["date", "hn"]).rename(columns={"date": "ds"}), on=["ds", "hn"], how="left")
    g = d.groupby("race_id")
    d["book"] = g.bsp.transform(lambda x: (1 / x).sum())
    bf = g.bsp.transform(lambda x: x.notna().all()) & d.book.between(0.95, 1.15) & (d.ds >= "2023-01-01")
    sp = (~bf) & d.sp_ok & (d.ds < "2023-01-01")
    d = d[(bf | sp) & (g.won.transform("sum") == 1) & (d.nr >= 5)].copy()
    d["src"] = np.where(d.ds >= "2023-01-01", "bf", "sp")
    d["pm"] = np.where(d.src == "bf", (1 / d.bsp) / d.book, d.spm)
    d = d[d.pm.notna()].sort_values(["date", "race_id"]).reset_index(drop=True)
    d["nsw"] = nsw_flag(d.track)
    d["comm"] = np.where(d.nsw, COMM_NSW, COMM_OTHER)
    d["lpm"] = np.log(d.pm)
    gk = d.groupby("race_id")
    for c in VM.REL:
        d["r_" + c] = d[c] - gk[c].transform("mean")
        d["k_" + c] = gk[c].rank(pct=True)
    d["fav"] = (d.pm == gk.pm.transform("max")).astype(float)
    d["pm_rank"] = gk.pm.rank(ascending=False)
    keep = ["race_id", "ds", "date", "track", "horse", "won", "bsp", "comm", "nsw", "pm", "src", "nr"] + FE_ALL
    d[list(dict.fromkeys(keep))].to_pickle(CACHE)
    print("frame: %d races (%d with the starting price 2020-07 to 2022, %d with a Betfair price), %d runners" % (
        d.race_id.nunique(), d[d.src == "sp"].race_id.nunique(), d[d.src == "bf"].race_id.nunique(), len(d)))


def gbm(tr, va, te, FE, seeds=(1, 2, 3), w_sp=1.0, lr=0.02, leaves=8, mdl=400):
    s, st = VM.ginfo(tr)
    y = tr.won.values
    w = np.where(tr.src.values == "sp", w_sp, 1.0)

    def obj(preds, ds):
        z = preds - np.repeat(np.maximum.reduceat(preds, st), s)
        e = np.exp(z)
        p = e / np.repeat(np.add.reduceat(e, st), s)
        return w * (p - y), w * np.maximum(p * (1 - p), 1e-6)

    yv = va.won.values

    def ev(preds, ds):
        return "ll", float(np.log(VM.soft(va, preds)[yv == 1].clip(1e-12)).mean()), True
    cv, ct, nt = [], [], []
    for seed in seeds:
        P = dict(learning_rate=lr, num_leaves=leaves, min_data_in_leaf=mdl, feature_fraction=0.5, bagging_fraction=0.7, bagging_freq=1, lambda_l2=50, verbose=-1,
                 objective=obj, metric="None", seed=seed, num_threads=4)
        dtr = lgb.Dataset(tr[FE], label=y, init_score=tr.lpm.values)
        dva = lgb.Dataset(va[FE], label=yv, init_score=va.lpm.values, reference=dtr)
        m = lgb.train(P, dtr, num_boost_round=3000, valid_sets=[dva], feval=ev, callbacks=[lgb.early_stopping(150, verbose=False)])
        cv.append(m.predict(va[FE]))
        ct.append(m.predict(te[FE]))
        nt.append(m.best_iteration)
    return np.mean(cv, axis=0), np.mean(ct, axis=0), "trees %s" % nt


def linear(tr, va, te, FE, l2s=(30, 100, 300, 1000)):
    """conditional logit correction on standardised inputs (blank = the mean), ridge strength chosen on the validation quarter"""
    mu, sd = tr[FE].mean(), tr[FE].std().replace(0, 1)

    def X(df):
        return ((df[FE] - mu) / sd).fillna(0).clip(-5, 5).values
    Xt, Xv, Xe = X(tr), X(va), X(te)
    s, st = VM.ginfo(tr)
    y, off = tr.won.values, tr.lpm.values
    nrace = len(s)

    def f(b, l2):
        z = off + Xt @ b
        z = z - np.repeat(np.maximum.reduceat(z, st), s)
        e = np.exp(z)
        p = e / np.repeat(np.add.reduceat(e, st), s)
        return -np.log(p[y == 1]).sum() / nrace + l2 * (b @ b) / nrace, (Xt.T @ (p - y)) / nrace + 2 * l2 * b / nrace
    best = None
    b0 = np.zeros(len(FE))
    for l2 in l2s:
        r = minimize(f, b0, args=(l2,), jac=True, method="L-BFGS-B", options=dict(maxiter=300))
        ll = np.log(VM.soft(va, va.lpm.values + Xv @ r.x)[va.won.values == 1]).mean()
        if best is None or ll > best[0]:
            best = (ll, l2, r.x)
    return Xv @ best[2], Xe @ best[2], "ridge %g" % best[1]


def shrink_factor(va, cv):
    grid = np.linspace(0, 1.5, 16)
    ll = [np.log(VM.soft(va, va.lpm.values + g * cv)[va.won.values == 1]).mean() for g in grid]
    return float(grid[int(np.argmax(ll))])


def bets(df, corr, thr=1.0):
    p = VM.soft(df, df.lpm.values + corr)
    ev = p * (1 + (df.bsp.values - 1) * (1 - df.comm.values))
    x = df[(ev > thr) & (df.bsp.values < 30)].copy()
    x["p"] = p[(ev > thr) & (df.bsp.values < 30)]
    x["pnl"] = x.won * (x.bsp - 1) * (1 - x.comm) - (1 - x.won)
    return x


def best_thr(va, cv):
    out = (1.0, -9)
    for t in (1.0, 1.01, 1.02, 1.03, 1.05, 1.08):
        x = bets(va, cv, t)
        if len(x) >= 150 and x.pnl.mean() > out[1]:
            out = (t, x.pnl.mean())
    return out[0]


def summary(label, X, A, corr):
    if len(X) == 0:
        print("%-34s no bets" % label)
        return
    days = X.groupby("ds").pnl.agg(["sum", "size"])
    rng = np.random.default_rng(1)
    idx = rng.integers(0, len(days), (2000, len(days)))
    bs = days["sum"].values[idx].sum(1) / days["size"].values[idx].sum(1)
    o = np.sort(X.pnl.values)[::-1]
    yr = X.groupby(X.ds.str[:4]).pnl.agg(["size", "mean"])
    w = A.won.values == 1
    dif = np.log(VM.soft(A, A.lpm.values + corr)[w]) - A.lpm.values[w]
    print("%-34s bets %6d ROI %+5.1f%% (90%% %+5.1f to %+5.1f, above zero %3.0f%%, ex10 %+5.1f%%) | %s | win %.2f%% model %.2f%% Betfair %.2f%% | gain over Betfair %+.4f (se %.4f)" % (
        label, len(X), 100 * X.pnl.mean(), 100 * np.quantile(bs, 0.05), 100 * np.quantile(bs, 0.95), 100 * (bs > 0).mean(), 100 * (X.pnl.sum() - o[:10].sum()) / len(X),
        " ".join("%s %d %+.1f%%" % (y, r["size"], 100 * r["mean"]) for y, r in yr.iterrows()), 100 * X.won.mean(), 100 * X.p.mean(), 100 * X.pm.mean(),
        dif.mean(), dif.std() / np.sqrt(len(dif))), flush=True)


VARIANTS = {
    "ref": dict(kind="gbm"),
    "pre": dict(kind="gbm", pre=True),
    "pre_half": dict(kind="gbm", pre=True, w_sp=0.5),
    "slow": dict(kind="gbm", lr=0.01, leaves=4, mdl=800, seeds=(1, 2, 3, 4, 5)),
    "pre_slow": dict(kind="gbm", pre=True, lr=0.01, leaves=4, mdl=800, seeds=(1, 2, 3, 4, 5)),
    "noprice": dict(kind="gbm", drop=["lpm", "fav", "pm_rank"]),
    "pre_noprice": dict(kind="gbm", pre=True, drop=["lpm", "fav", "pm_rank"]),
    "lin": dict(kind="lin"),
    "pre_lin": dict(kind="lin", pre=True),
    "pre_mix": dict(kind="mix", pre=True),
}


def run(names):
    d = pd.read_pickle(CACHE)
    store = {}
    for name in names:
        v = VARIANTS[name]
        FE = [c for c in FE_ALL if c not in v.get("drop", [])]
        parts = []
        for fit_end, val_end, test_end in FOLDS:
            tr = d[(d.ds < fit_end) & ((d.src == "bf") | bool(v.get("pre")))]
            va = d[(d.ds >= fit_end) & (d.ds < val_end)]
            te = d[(d.ds >= val_end) & (d.ds < test_end)]
            kw = {k: v[k] for k in ("seeds", "w_sp", "lr", "leaves", "mdl") if k in v}
            if v["kind"] == "gbm":
                cv, ct, note = gbm(tr, va, te, FE, **kw)
            elif v["kind"] == "lin":
                cv, ct, note = linear(tr, va, te, FE)
            else:
                a = gbm(tr, va, te, FE, **kw)
                l = linear(tr, va, te, FE)
                cv, ct, note = (a[0] + l[0]) / 2, (a[1] + l[1]) / 2, a[2] + ", " + l[2]
            sf = shrink_factor(va, cv)
            th = best_thr(va, cv)
            ths = best_thr(va, sf * cv)
            print("  %s test %s: fit races %d, %s, shrink %.1f, threshold %.2f / %.2f after shrink" % (name, val_end[:4], tr.race_id.nunique(), note, sf, th, ths), flush=True)
            parts.append((te, ct, sf, th, ths))
        A = pd.concat([p[0] for p in parts])
        c0 = np.concatenate([p[1] for p in parts])
        c1 = np.concatenate([p[1] * p[2] for p in parts])
        summary(name, pd.concat([bets(p[0], p[1]) for p in parts]), A, c0)
        summary(name + " + shrink", pd.concat([bets(p[0], p[1] * p[2]) for p in parts]), A, c1)
        summary(name + " + threshold", pd.concat([bets(p[0], p[1], p[3]) for p in parts]), A, c0)
        summary(name + " + shrink + threshold", pd.concat([bets(p[0], p[1] * p[2], p[4]) for p in parts]), A, c1)
        store[name] = (A[["race_id", "ds", "horse", "won", "bsp", "comm", "pm", "lpm"]], c0, c1)
    pd.to_pickle(store, "/tmp/value_model3_%s.pkl" % "+".join(names))


if __name__ == "__main__":
    if sys.argv[1] == "build":
        build()
    else:
        run(sys.argv[2:] or list(VARIANTS))
