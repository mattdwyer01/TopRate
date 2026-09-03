"""
wpr_best_anchor_signal_test.py - follow-up to the wpr_nett leak fix:
given that MORE weight on wpr_nett made MAE monotonically WORSE across
the entire [0.5, 1.0] range tested (wpr_alpha_08_leak_corrected_
validation.py), what IS the best anchor signal for the additive
model's base - wpr_nett alone, ewm3 alone, some other single own-
history signal, or a blend, and if a blend, what's the true MAE-
minimizing alpha (not just "is 0.5 better than 0.8", the full [0,1]
range)?

METHOD: same leak-corrected build (wpr_nett re-merged from
toprate_runners.csv by (horse, date, race_id), not build_training_
frame()'s contaminated run_id merge), same K=4 chronological folds,
same "fresh single-slope calibration per candidate per fold" discipline
as the alpha re-check. Two parts:
  1. STANDALONE signals: wpr_nett, ewm3, avg_last3, career_avg,
     recent5_max, best3 each calibrated alone (single OLS slope/
     intercept per fold, fit on training only) and scored by held-out
     MAE - answers "which single signal is most predictive on its own".
  2. FULL BLEND SWEEP: wpr_nett/ewm3 blend at alpha = 0.0, 0.1, ..., 1.0
     (the full range, not just 0.5-1.0) - answers "is some blend better
     than either pure signal, and if so what weight".

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np
import pandas as pd

from wpr_alpha_08_leak_corrected_validation import build_full, fix_wpr_nett_leak

N_FOLDS = 4
ALPHA_GRID = [0.0, 0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9, 1.0]
STANDALONE_SIGNALS = ["wpr_nett", "ewm3", "avg_last3", "career_avg", "recent5_max", "best3"]


def fit_ols(x, y):
    mask = x.notna() & y.notna()
    if mask.sum() < 30:
        return 0.0, 1.0
    slope, intercept = np.polyfit(x[mask], y[mask], 1)
    return intercept, slope


def mae_for_series(train_x, train_y, test_x, test_y):
    intercept, slope = fit_ols(train_x, train_y)
    pred = intercept + slope * test_x
    mask = test_y.notna() & pred.notna()
    return float((test_y[mask] - pred[mask]).abs().mean()), mask.sum()


def blend(frame, alpha):
    nett, ewm3 = frame["wpr_nett"], frame["ewm3"]
    both = nett.notna() & ewm3.notna()
    out = pd.Series(np.where(both, alpha * nett + (1 - alpha) * ewm3, nett.fillna(ewm3)), index=frame.index)
    return out.fillna(frame["avg_last3"]).fillna(frame["career_avg"])


def run():
    full = build_full()
    full = fix_wpr_nett_leak(full)
    full = full.dropna(subset=["target"]).sort_values("date").reset_index(drop=True)
    print(f"Scoped rows: {len(full):,}")

    fold_edges = np.array_split(np.arange(len(full)), N_FOLDS)
    full["_fold"] = -1
    for i, idx in enumerate(fold_edges):
        full.loc[idx, "_fold"] = i

    print(f"\n{'='*90}\nSTANDALONE SIGNALS (each calibrated alone, K={N_FOLDS}-fold held-out MAE)\n{'='*90}")
    for sig in STANDALONE_SIGNALS:
        if sig not in full.columns:
            print(f"  {sig}: not found, skipped")
            continue
        fold_maes, fold_ns = [], []
        for i in range(N_FOLDS):
            train = full[full["_fold"] != i]
            test = full[full["_fold"] == i]
            mae, n = mae_for_series(train[sig], train["target"], test[sig], test["target"])
            fold_maes.append(mae)
            fold_ns.append(n)
        print(f"  {sig:<14} avg MAE={np.mean(fold_maes):.4f}  (per-fold: "
              f"{', '.join(f'{m:.4f}' for m in fold_maes)})  n~{int(np.mean(fold_ns)):,}")

    print(f"\n{'='*90}\nFULL BLEND SWEEP: wpr_nett/ewm3 alpha (0=pure ewm3, 1=pure wpr_nett)\n{'='*90}")
    best_alpha, best_mae = None, float("inf")
    for alpha in ALPHA_GRID:
        full["_raw"] = blend(full, alpha)
        fold_maes = []
        for i in range(N_FOLDS):
            train = full[full["_fold"] != i]
            test = full[full["_fold"] == i]
            mae, n = mae_for_series(train["_raw"], train["target"], test["_raw"], test["target"])
            fold_maes.append(mae)
        avg = np.mean(fold_maes)
        flag = ""
        if avg < best_mae:
            best_mae, best_alpha = avg, alpha
            flag = "  <-- best so far"
        print(f"  alpha={alpha:.1f}  avg MAE={avg:.4f}  (per-fold: "
              f"{', '.join(f'{m:.4f}' for m in fold_maes)}){flag}")

    print(f"\nBest alpha in full [0,1] sweep: {best_alpha} (avg MAE {best_mae:.4f})")
    print("\nSame caveats as always: leak-free-for-wpr_nett K-fold, but one dataset/attempt.")


if __name__ == "__main__":
    run()
