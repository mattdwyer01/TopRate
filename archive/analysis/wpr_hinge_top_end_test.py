"""
wpr_hinge_top_end_test.py - the anti-shrinkage investigation continues:
a plain quadratic term fixed the 90-95 underestimation but overshot
badly beyond it (unstable, negative-then-corrected coefficients - a
small-sample overfitting signature). A HINGE term is gentler: it stays
exactly linear below a knot point, and switches to a second (steeper)
linear slope above it - no acceleration, so it can't run away in the
sparse extreme tail the way a quadratic's curvature does. This tests a
grid of knot locations via K-fold to find where the bend genuinely
happens (if anywhere) rather than assuming one, and checks the fix holds
up across the WHOLE top range (90-95, 95-100, AND 100+), not just the
single band a quadratic was able to patch.

hinge(x, k) = max(0, x - k) - the added term is 0 below the knot, and
grows linearly (1:1 with x) above it, so its own coefficient is exactly
"how much extra slope kicks in above the knot" - directly interpretable,
unlike a quadratic coefficient.

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np
import pandas as pd
from sklearn.linear_model import LinearRegression

from wpr_alpha_08_leak_corrected_validation import build_full, fix_wpr_nett_leak

N_FOLDS = 4
BANDS = [(0, 60), (60, 70), (70, 80), (80, 90), (90, 95), (95, 100), (100, 200)]
KNOT_GRID = [80, 82, 85, 88, 90, 92]


def hinge(x, k):
    return np.maximum(0.0, x - k)


def run():
    full = build_full()
    full = fix_wpr_nett_leak(full)
    full = full.dropna(subset=["target", "wpr_nett", "ewm5"]).sort_values("date").reset_index(drop=True)
    full["_raw_level"] = (full["wpr_nett"] + full["ewm5"]) / 2
    print(f"Scoped rows: {len(full):,}")

    full["_fold"] = -1
    for i, idx in enumerate(np.array_split(np.arange(len(full)), N_FOLDS)):
        full.loc[idx, "_fold"] = i

    print(f"\n{'='*100}\nKNOT GRID SEARCH (K={N_FOLDS}-fold overall MAE, knot fit fresh per fold - the "
          f"hinge coefficient itself, not just its location, is refit each fold)\n{'='*100}")
    best_knot, best_mae = None, float("inf")
    knot_maes = {}
    for k in KNOT_GRID:
        fold_maes = []
        for i in range(N_FOLDS):
            train = full[full["_fold"] != i].copy()
            test = full[full["_fold"] == i].copy()
            train["_hinge"] = hinge(train["_raw_level"], k)
            test["_hinge"] = hinge(test["_raw_level"], k)
            m = LinearRegression().fit(
                train[["wpr_nett", "ewm5", "_hinge"]].to_numpy(), train["target"].to_numpy())
            pred = m.predict(test[["wpr_nett", "ewm5", "_hinge"]].to_numpy())
            fold_maes.append(float(np.abs(test["target"].to_numpy() - pred).mean()))
        avg = np.mean(fold_maes)
        knot_maes[k] = avg
        flag = ""
        if avg < best_mae:
            best_mae, best_knot = avg, k
            flag = "  <-- best so far"
        print(f"  knot={k}  avg MAE={avg:.4f}  (per-fold: {', '.join(f'{m:.4f}' for m in fold_maes)}){flag}")

    print(f"\nLinear-only (no hinge) baseline for comparison:")
    fold_maes = []
    for i in range(N_FOLDS):
        train = full[full["_fold"] != i]
        test = full[full["_fold"] == i]
        m = LinearRegression().fit(train[["wpr_nett", "ewm5"]].to_numpy(), train["target"].to_numpy())
        pred = m.predict(test[["wpr_nett", "ewm5"]].to_numpy())
        fold_maes.append(float(np.abs(test["target"].to_numpy() - pred).mean()))
    print(f"  avg MAE={np.mean(fold_maes):.4f}")

    print(f"\n{'='*100}\nBIAS BY BAND at best knot ({best_knot}): LINEAR vs HINGE, fold-consistent predictions\n{'='*100}")
    pred_lin = pd.Series(np.nan, index=full.index)
    pred_hinge = pd.Series(np.nan, index=full.index)
    hinge_coefs = []
    for i in range(N_FOLDS):
        train = full[full["_fold"] != i].copy()
        test = full[full["_fold"] == i].copy()
        train["_hinge"] = hinge(train["_raw_level"], best_knot)
        test["_hinge"] = hinge(test["_raw_level"], best_knot)

        m_lin = LinearRegression().fit(train[["wpr_nett", "ewm5"]].to_numpy(), train["target"].to_numpy())
        m_hinge = LinearRegression().fit(
            train[["wpr_nett", "ewm5", "_hinge"]].to_numpy(), train["target"].to_numpy())
        pred_lin.loc[test.index] = m_lin.predict(test[["wpr_nett", "ewm5"]].to_numpy())
        pred_hinge.loc[test.index] = m_hinge.predict(test[["wpr_nett", "ewm5", "_hinge"]].to_numpy())
        hinge_coefs.append(m_hinge.coef_)
        print(f"  fold {i}: LINEAR coef={m_lin.coef_.round(3)}  |  HINGE coef={m_hinge.coef_.round(4)} "
              f"(3rd value = extra slope above knot {best_knot})")

    full["_bias_lin"] = full["target"] - pred_lin
    full["_bias_hinge"] = full["target"] - pred_hinge

    print(f"\n  {'band':>10} {'n':>7} {'LINEAR bias':>12} {'HINGE bias':>11} {'LINEAR MAE':>11} {'HINGE MAE':>10}")
    for lo, hi in BANDS:
        sub = full[(full["_raw_level"] >= lo) & (full["_raw_level"] < hi)]
        if len(sub) < 5:
            continue
        print(f"  {f'{lo}-{hi}':>10} {len(sub):>7,} {sub['_bias_lin'].mean():>+12.2f} "
              f"{sub['_bias_hinge'].mean():>+11.2f} {sub['_bias_lin'].abs().mean():>11.3f} "
              f"{sub['_bias_hinge'].abs().mean():>10.3f}")

    print(f"\nOverall MAE: LINEAR={full['_bias_lin'].abs().mean():.4f}  HINGE={full['_bias_hinge'].abs().mean():.4f}")

    # Full-data (non-K-fold) fit for shipping constants + Autumn Glow check
    full["_hinge_final"] = hinge(full["_raw_level"], best_knot)
    m_final = LinearRegression().fit(
        full[["wpr_nett", "ewm5", "_hinge_final"]].to_numpy(), full["target"].to_numpy())
    print(f"\nFinal full-data hinge fit (knot={best_knot}): intercept={m_final.intercept_:.4f}  "
          f"coef={m_final.coef_.round(4)}")
    nett, ewm5 = 103.0, 104.5
    raw_level = (nett + ewm5) / 2
    h = max(0.0, raw_level - best_knot)
    pred = m_final.intercept_ + m_final.coef_[0] * nett + m_final.coef_[1] * ewm5 + m_final.coef_[2] * h
    print(f"Autumn Glow (nett=103.0, ewm5=104.5, raw_level={raw_level:.2f}, hinge={h:.2f}): base = {pred:.1f}")


if __name__ == "__main__":
    run()
