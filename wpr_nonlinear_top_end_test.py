"""
wpr_nonlinear_top_end_test.py - the anti-shrinkage investigation's real
lead: wpr_anti_shrinkage_fix_test.py's bias-by-raw-level-band table (for
the ALREADY-SHIPPED wpr_nett+ewm5 fit) shows bias near zero through
60-90, then climbing steadily positive above 90 (90-95: +1.33 on n=1,146,
95-100: +0.68 on n=206) - the model UNDER-projects increasingly as raw
level rises past 90, a sign the true relationship curves upward at the
elite end rather than being a straight line all the way through, which a
plain linear fit cannot capture (it fits the dominant middle of the
distribution and extrapolates linearly past it).

Tests adding a squared raw-level term (on top of the existing linear
wpr_nett/ewm5 terms) to see whether that curvature reduces the top-band
bias without hurting the bulk of the distribution or overfitting -
K=4-fold, same discipline as every other test this session.

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np
import pandas as pd
from sklearn.linear_model import LinearRegression

from wpr_alpha_08_leak_corrected_validation import build_full, fix_wpr_nett_leak

N_FOLDS = 4
BANDS = [(0, 60), (60, 70), (70, 80), (80, 90), (90, 95), (95, 100), (100, 200)]


def run():
    full = build_full()
    full = fix_wpr_nett_leak(full)
    full = full.dropna(subset=["target", "wpr_nett", "ewm5"]).sort_values("date").reset_index(drop=True)
    full["_raw_level"] = (full["wpr_nett"] + full["ewm5"]) / 2
    full["_raw_level_sq"] = full["_raw_level"] ** 2
    print(f"Scoped rows: {len(full):,}")

    full["_fold"] = -1
    for i, idx in enumerate(np.array_split(np.arange(len(full)), N_FOLDS)):
        full.loc[idx, "_fold"] = i

    pred_linear = pd.Series(np.nan, index=full.index)
    pred_quad = pd.Series(np.nan, index=full.index)
    for i in range(N_FOLDS):
        train = full[full["_fold"] != i]
        test = full[full["_fold"] == i]

        m_lin = LinearRegression().fit(train[["wpr_nett", "ewm5"]].to_numpy(), train["target"].to_numpy())
        m_quad = LinearRegression().fit(
            train[["wpr_nett", "ewm5", "_raw_level_sq"]].to_numpy(), train["target"].to_numpy())

        pred_linear.loc[test.index] = m_lin.predict(test[["wpr_nett", "ewm5"]].to_numpy())
        pred_quad.loc[test.index] = m_quad.predict(test[["wpr_nett", "ewm5", "_raw_level_sq"]].to_numpy())

        print(f"  fold {i}: LINEAR coef={m_lin.coef_.round(3)} intercept={m_lin.intercept_:.2f}  |  "
              f"QUADRATIC coef={m_quad.coef_.round(4)} intercept={m_quad.intercept_:.2f}")

    full["_bias_lin"] = full["target"] - pred_linear
    full["_bias_quad"] = full["target"] - pred_quad

    print(f"\n{'='*100}\nBIAS BY RAW-LEVEL BAND: LINEAR (shipped) vs QUADRATIC candidate\n{'='*100}")
    print(f"  {'band':>10} {'n':>7} {'LINEAR bias':>12} {'QUAD bias':>10} {'LINEAR MAE':>11} {'QUAD MAE':>9}")
    for lo, hi in BANDS:
        sub = full[(full["_raw_level"] >= lo) & (full["_raw_level"] < hi)]
        if len(sub) < 5:
            continue
        print(f"  {f'{lo}-{hi}':>10} {len(sub):>7,} {sub['_bias_lin'].mean():>+12.2f} "
              f"{sub['_bias_quad'].mean():>+10.2f} {sub['_bias_lin'].abs().mean():>11.3f} "
              f"{sub['_bias_quad'].abs().mean():>9.3f}")

    print(f"\nOverall MAE: LINEAR={full['_bias_lin'].abs().mean():.4f}  QUADRATIC={full['_bias_quad'].abs().mean():.4f}")

    # Concrete Autumn Glow check using the FULL-DATA (non-K-fold) fit, same
    # convention as the shipped constants
    m_lin_full = LinearRegression().fit(full[["wpr_nett", "ewm5"]].to_numpy(), full["target"].to_numpy())
    m_quad_full = LinearRegression().fit(
        full[["wpr_nett", "ewm5", "_raw_level_sq"]].to_numpy(), full["target"].to_numpy())
    nett, ewm5 = 103.0, 104.5
    raw_sq = ((nett + ewm5) / 2) ** 2
    lin_pred = m_lin_full.intercept_ + m_lin_full.coef_[0] * nett + m_lin_full.coef_[1] * ewm5
    quad_pred = (m_quad_full.intercept_ + m_quad_full.coef_[0] * nett + m_quad_full.coef_[1] * ewm5
                 + m_quad_full.coef_[2] * raw_sq)
    print(f"\nAutumn Glow (nett=103.0, ewm5=104.5): LINEAR (shipped) = {lin_pred:.1f}  QUADRATIC = {quad_pred:.1f}")
    print(f"Quadratic full-data coefficients: {m_quad_full.coef_.round(5)}  intercept={m_quad_full.intercept_:.3f}")


if __name__ == "__main__":
    run()
