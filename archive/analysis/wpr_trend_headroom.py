"""
wpr_trend_headroom.py - does detailed per-horse trend have headroom?

Asks one question with data: after the current model makes its projection, is
there leftover signal in a horse's OWN run-by-run trajectory that the model did
not already capture? If yes, a trajectory-aware model could help. If no, the
GBM already absorbed the trend and going more granular only adds noise.

METHOD (light, no retrain needed)
  For each resulted runner in toprate_runners.csv (has wprp_proj + wpr_actual),
  pull that horse's prior run sequence from wpr_form_history.csv (runs strictly
  before the race date), and compute a battery of detailed trajectory features
  point-in-time:
    slope_raw       OLS slope over the last up-to-6 runs
    slope_shrunk    that slope shrunk by its own standard error (b^2/(b^2+se^2)),
                    i.e. a noisy 6-point slope is pulled toward zero. This is
                    the "estimate the trend properly" version.
    accel           recent-3 slope minus prior-3 slope
    curv            quadratic term over the last up-to-6 runs
    last_vs_career  last run minus career average
    last_vs_l3      last run minus average of last 3
    vol_recent      std of the last up-to-5 runs
    breakout        last run minus career max (>0 only on a career peak)
    dir_consist     mean sign of the last up-to-5 run-to-run moves

  Then test those features against the MODEL RESIDUAL = actual - (proj + offset):
    1. correlation of each feature with the residual (nonzero = headroom)
    2. residual correlation stratified by run count (is trend estimable only
       for horses with long histories?)
    3. can the whole battery reduce the residual out of sample? (5-fold ridge CV)

  A feature that still predicts the residual is signal the model missed. If all
  are ~0 and the battery does not cut CV error, the model already has the trend.

WHY RE-RUN IT
  The signal that does flicker is in lightly-raced horses (3-6 prior runs),
  which is both the smallest sample and the least reliable trajectory. Re-run as
  the resulted-runner sample grows to see whether it firms up enough to act on.

USAGE
  python wpr_trend_headroom.py
  python wpr_trend_headroom.py --offset 2.57
  python wpr_trend_headroom.py --runners toprate_runners.csv --history wpr_form_history.csv

NO EM DASHES policy: hyphens only.
"""

import sys
import numpy as np
import pandas as pd
from numpy.random import default_rng

FEATURES = ["slope_raw", "slope_shrunk", "accel", "curv", "last_vs_career",
            "last_vs_l3", "vol_recent", "breakout", "dir_consist"]


def load_sequences(history_csv):
    """Per-horse chronological WPR sequence, scrape-deduped (latest scrape per
    horse+date), keyed by horse name."""
    fh = pd.read_csv(history_csv, low_memory=False,
                     usecols=["horse", "date", "wpr", "scrape_date"])
    fh["date"] = pd.to_datetime(fh["date"], errors="coerce")
    fh["scrape_date"] = pd.to_datetime(fh["scrape_date"], errors="coerce")
    fh["wpr"] = pd.to_numeric(fh["wpr"], errors="coerce")
    fh = fh.dropna(subset=["horse", "date", "wpr"])
    fh = fh.sort_values("scrape_date").drop_duplicates(["horse", "date"], keep="last")
    fh = fh.sort_values(["horse", "date"])
    return {h: (g["date"].values, g["wpr"].values) for h, g in fh.groupby("horse")}


def trend_feats(seq, name, race_date):
    """Detailed point-in-time trajectory features from runs before race_date.
    Returns None if fewer than 3 prior runs."""
    pr = seq.get(name)
    if pr is None:
        return None
    dates, wp = pr
    w = wp[dates < np.datetime64(race_date)]
    if len(w) < 3:
        return None
    n = len(w)
    f = {"n_runs": n}
    k = min(6, n)
    xs = np.arange(k, dtype=float)
    ws = w[-k:]
    b1, b0 = np.polyfit(xs, ws, 1)
    yhat = b0 + b1 * xs
    sse = ((ws - yhat) ** 2).sum()
    se = (np.sqrt(sse / max(k - 2, 1) / ((xs - xs.mean()) ** 2).sum())
          if k > 2 else np.inf)
    rel = b1 ** 2 / (b1 ** 2 + se ** 2) if np.isfinite(se) and (b1 ** 2 + se ** 2) > 0 else 0.0
    f["slope_raw"] = b1
    f["slope_shrunk"] = b1 * rel
    if n >= 6:
        r3 = np.polyfit(np.arange(3), w[-3:], 1)[0]
        p3 = np.polyfit(np.arange(3), w[-6:-3], 1)[0]
        f["accel"] = r3 - p3
    else:
        f["accel"] = 0.0
    f["curv"] = np.polyfit(xs, ws, 2)[0] if k >= 3 else 0.0
    f["last_vs_career"] = w[-1] - w.mean()
    f["last_vs_l3"] = w[-1] - w[-3:].mean()
    f["vol_recent"] = w[-min(5, n):].std()
    f["breakout"] = w[-1] - w.max()
    f["dir_consist"] = np.mean(np.sign(np.diff(w[-min(5, n):]))) if n >= 2 else 0.0
    return f


def main():
    args = sys.argv
    def opt(flag, default):
        return args[args.index(flag) + 1] if flag in args else default
    runners_csv = opt("--runners", "toprate_runners.csv")
    history_csv = opt("--history", "wpr_form_history.csv")
    offset = float(opt("--offset", "2.57"))

    seq = load_sequences(history_csv)
    print(f"form history horses: {len(seq):,}")

    d = pd.read_csv(runners_csv, low_memory=False)
    d["date"] = pd.to_datetime(d["date"], errors="coerce")
    d["proj"] = pd.to_numeric(d["wprp_proj"], errors="coerce")
    d["act"] = pd.to_numeric(d["wpr_actual"], errors="coerce")
    d = d.dropna(subset=["proj", "act", "horse", "date"]).copy()
    d["resid"] = d["act"] - (d["proj"] + offset)
    print(f"resulted runners: {len(d):,}   offset applied: {offset:+.2f}")

    rows, idxs = [], []
    for i, r in d.iterrows():
        f = trend_feats(seq, r["horse"], r["date"])
        if f is not None:
            rows.append(f)
            idxs.append(i)
    T = pd.DataFrame(rows, index=idxs)
    D = d.loc[idxs].join(T)
    print(f"matched with >=3 prior runs: {len(D):,}")

    print("\n== corr of each detailed-trend feature with MODEL residual ==")
    print("   (nonzero => signal the model did NOT absorb => headroom)")
    for c in FEATURES:
        s = D.dropna(subset=[c, "resid"])
        r = np.corrcoef(s[c], s["resid"])[0, 1] if len(s) > 30 else float("nan")
        print(f"   {c:16s} corr={r:+.3f}  n={len(s)}")

    print("\n== residual corr by run-count stratum ==")
    print("   (where is a per-horse trend even estimable?)")
    for lo, hi, lbl in [(3, 7, "3-6 runs"), (7, 12, "7-11 runs"), (12, 999, "12+ runs")]:
        g = D[(D["n_runs"] >= lo) & (D["n_runs"] < hi)]
        if len(g) < 40:
            print(f"   {lbl:10s} n={len(g)} (too few)")
            continue
        rr = [np.corrcoef(g[c], g["resid"])[0, 1]
              for c in ["slope_shrunk", "accel", "last_vs_l3"]]
        print(f"   {lbl:10s} n={len(g):4d}  slope_shrunk={rr[0]:+.3f}  "
              f"accel={rr[1]:+.3f}  last_vs_l3={rr[2]:+.3f}")

    DD = D.dropna(subset=FEATURES + ["resid"]).copy()
    X = DD[FEATURES].values
    X = (X - X.mean(0)) / X.std(0)
    y = DD["resid"].values
    base_mae = np.abs(y).mean()
    rng = default_rng(0)
    idx = rng.permutation(len(DD))
    folds = np.array_split(idx, 5)

    def cv_ridge(lam):
        e = []
        for k in range(5):
            te = folds[k]
            tr = np.concatenate([folds[j] for j in range(5) if j != k])
            Xt = np.c_[np.ones(len(tr)), X[tr]]
            coef = np.linalg.solve(Xt.T @ Xt + lam * np.eye(Xt.shape[1]), Xt.T @ y[tr])
            Xv = np.c_[np.ones(len(te)), X[te]]
            e.append(np.abs(y[te] - Xv @ coef).mean())
        return np.mean(e)

    print("\n== can the full battery reduce the residual? 5-fold ridge CV MAE ==")
    print(f"   base |residual| (proj+offset):   {base_mae:.3f}")
    for lam in [1, 10, 50]:
        print(f"   + trend battery (ridge {lam:>3d}):     {cv_ridge(lam):.3f}")
    print("\n   Verdict: if the battery does not beat base and all corrs are ~0,")
    print("   the model already captures the trend and a trajectory model adds noise.")


if __name__ == "__main__":
    main()
