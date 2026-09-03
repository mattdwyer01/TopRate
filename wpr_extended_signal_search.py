"""
wpr_extended_signal_search.py - the user asked to dig further before
deciding whether the best3-tiered regression (wpr_multi_signal_
regression_test.py, ~0.5% MAE gain for real production complexity) is
worth shipping. Two follow-ups:

  1. OTHER OWN-HISTORY SIGNALS NOT YET TESTED: wpr_best_anchor_signal_
     test.py only tried wpr_nett/ewm3/avg_last3/career_avg/recent5_max/
     best3. FEATURES (wpr_projection.py ~line 273) has more WPR-scale
     absolute own-history signals never checked as base-anchor
     candidates: last1, last2, peak, avg_last5, ewm5, track_wpr,
     distband_wpr, secondup_wpr, thirdup_wpr. A quick correlation check
     found ewm5 (5-run recency-weighted average, vs the shipped 3-run
     ewm3) correlates with target at 0.667, actually HIGHER than ewm3
     (0.660) or wpr_nett (0.648) - and with FULL coverage (43,752/43,752,
     no missingness problem at all, unlike best3's 62%). Tests it here
     properly (K-fold MAE, win strike, avg margin) rather than trusting
     a raw correlation number, and checks whether it's simply a better
     REPLACEMENT for ewm3 in the existing 2-signal blend, or whether the
     two are different enough to both earn a place in a combined model.

  2. CLEANER MISSINGNESS HANDLING for best3 (avoiding a hard two-model
     tier): a single composite column ("best_avail" = best3 where
     present, else recent5_max) fed into ONE regression/blend, instead
     of maintaining two separately-calibrated models gated on whether
     best3 exists for a given horse.

Same leak-corrected build, K=4 chronological folds, complete-case per
signal/combo tested.

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np
import pandas as pd
from sklearn.linear_model import LinearRegression

from wpr_alpha_08_leak_corrected_validation import build_full, fix_wpr_nett_leak
from wpr_signal_strike_margin_combo_test import merge_margin, strike_and_margin

N_FOLDS = 4
NEW_SIGNALS = ["last1", "last2", "peak", "avg_last5", "ewm5", "track_wpr",
               "distband_wpr", "secondup_wpr", "thirdup_wpr"]


def fit_ols(x, y):
    mask = x.notna() & y.notna()
    if mask.sum() < 30:
        return 0.0, 1.0
    slope, intercept = np.polyfit(x[mask], y[mask], 1)
    return intercept, slope


def mae_kfold(frame, raw_col):
    fold_maes = []
    for i in range(N_FOLDS):
        train = frame[frame["_fold"] != i]
        test = frame[frame["_fold"] == i]
        intercept, slope = fit_ols(train[raw_col], train["target"])
        pred = intercept + slope * test[raw_col]
        mask = test["target"].notna() & pred.notna()
        fold_maes.append(float((test["target"][mask] - pred[mask]).abs().mean()))
    return float(np.mean(fold_maes))


def mae_kfold_multi(frame, cols):
    """Multiple-OLS-regression version of mae_kfold, complete-case on cols."""
    sub = frame.dropna(subset=cols + ["target"]).copy()
    sub = sub.sort_values("date").reset_index(drop=True)
    sub["_f"] = -1
    for i, idx in enumerate(np.array_split(np.arange(len(sub)), N_FOLDS)):
        sub.loc[idx, "_f"] = i
    fold_maes = []
    for i in range(N_FOLDS):
        train = sub[sub["_f"] != i]
        test = sub[sub["_f"] == i]
        model = LinearRegression().fit(train[cols].to_numpy(), train["target"].to_numpy())
        pred = model.predict(test[cols].to_numpy())
        fold_maes.append(float(np.abs(test["target"].to_numpy() - pred).mean()))
    return float(np.mean(fold_maes)), len(sub)


def run():
    full = build_full()
    full = fix_wpr_nett_leak(full)
    full = merge_margin(full)
    full = full.dropna(subset=["target"]).sort_values("date").reset_index(drop=True)
    full["_fold"] = -1
    for i, idx in enumerate(np.array_split(np.arange(len(full)), N_FOLDS)):
        full.loc[idx, "_fold"] = i
    print(f"Scoped rows: {len(full):,}")

    print(f"\n{'='*100}\nPART 1: NEW STANDALONE SIGNALS NOT PREVIOUSLY TESTED "
          f"(K={N_FOLDS}-fold MAE, win strike, avg margin)\n{'='*100}")
    print(f"  {'signal':<16} {'coverage':>9} {'avg MAE':>9} {'win strike':>11} {'avg margin':>12}")
    for sig in ["wpr_nett", "ewm3"] + NEW_SIGNALS:
        if sig not in full.columns:
            print(f"  {sig}: not found, skipped")
            continue
        mae = mae_kfold(full, sig)
        strike, margin, n = strike_and_margin(full, sig)
        cov = full[sig].notna().sum()
        tag = "  <- shipped" if sig in ("wpr_nett", "ewm3") else ""
        print(f"  {sig:<16} {cov:>9,} {mae:>9.4f} {strike*100:>10.1f}% {margin:>11.2f}L{tag}")

    print(f"\n{'='*100}\nPART 2: ewm5 AS AN OUTRIGHT REPLACEMENT FOR ewm3 IN THE 2-SIGNAL BLEND\n{'='*100}")
    print(f"  {'model':<44} {'avg MAE':>9} {'n(rows)':>9}")
    for label, cols in [
        ("OLS: wpr_nett + ewm3 (shipped signal set)", ["wpr_nett", "ewm3"]),
        ("OLS: wpr_nett + ewm5 (ewm5 replaces ewm3)", ["wpr_nett", "ewm5"]),
        ("OLS: wpr_nett + ewm3 + ewm5 (both)", ["wpr_nett", "ewm3", "ewm5"]),
        ("OLS: wpr_nett + ewm5 + avg_last5", ["wpr_nett", "ewm5", "avg_last5"]),
        ("OLS: wpr_nett + ewm5 + track_wpr", ["wpr_nett", "ewm5", "track_wpr"]),
        ("OLS: wpr_nett + ewm5 + avg_last5 + track_wpr", ["wpr_nett", "ewm5", "avg_last5", "track_wpr"]),
        ("OLS: wpr_nett + ewm5 + avg_last5 + track_wpr + best3",
         ["wpr_nett", "ewm5", "avg_last5", "track_wpr", "best3"]),
    ]:
        mae, n = mae_kfold_multi(full, cols)
        print(f"  {label:<44} {mae:>9.4f} {n:>9,}")

    print(f"\n{'='*100}\nPART 3: CLEANER best3 MISSINGNESS HANDLING (one composite column, no model "
          f"tiering)\n{'='*100}")
    full["best_avail"] = full["best3"].fillna(full["recent5_max"])
    print(f"  best_avail coverage: {full['best_avail'].notna().sum():,} / {len(full):,} "
          f"(vs best3 alone: {full['best3'].notna().sum():,})")
    print(f"  {'model':<44} {'avg MAE':>9} {'n(rows)':>9}")
    for label, cols in [
        ("OLS: wpr_nett + ewm5 + avg_last5 (no best)", ["wpr_nett", "ewm5", "avg_last5"]),
        ("OLS: wpr_nett + ewm5 + avg_last5 + best_avail (composite, one model)",
         ["wpr_nett", "ewm5", "avg_last5", "best_avail"]),
        ("OLS: wpr_nett + ewm5 + avg_last5 + best3 (tiered, best3-only subset)",
         ["wpr_nett", "ewm5", "avg_last5", "best3"]),
    ]:
        mae, n = mae_kfold_multi(full, cols)
        print(f"  {label:<44} {mae:>9.4f} {n:>9,}")

    print("\nSame caveats as always: leak-free-for-wpr_nett K-fold, but one dataset/attempt.")


if __name__ == "__main__":
    run()
