"""
wpr_hinge_all_tiers_test.py - extends wpr_hinge_top_end_test.py's hinge
correction (confirmed on the minimal tier) to track and full, after
confirming (in-sample check) that both show the same top-end
underestimation pattern (90-95 band: minimal +1.33, track +0.88, full
+1.50 - all three tiers, not just minimal). K=4-fold validation, same
discipline as every other candidate this session, before shipping.

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np
import pandas as pd
from sklearn.linear_model import LinearRegression

from wpr_alpha_08_leak_corrected_validation import build_full, fix_wpr_nett_leak

N_FOLDS = 4
KNOT_GRID = [75, 78, 80, 82, 85, 88, 90]
BANDS = [(0, 70), (70, 80), (80, 90), (90, 95), (95, 100), (100, 200)]


def hinge(x, k):
    return np.maximum(0.0, x - k)


def run_tier(full, tier_name, cols):
    has_track = full["track_wpr"].notna()
    has_best3 = full["best3"].notna()
    if tier_name == "full":
        mask = has_track & has_best3
    elif tier_name == "track":
        mask = has_track & ~has_best3
    else:
        mask = ~has_track
    sub = full[mask].dropna(subset=cols).sort_values("date").reset_index(drop=True)
    sub["_raw_level"] = (sub["wpr_nett"] + sub["ewm5"]) / 2
    sub["_fold"] = -1
    for i, idx in enumerate(np.array_split(np.arange(len(sub)), N_FOLDS)):
        sub.loc[idx, "_fold"] = i

    print(f"\n{'='*100}\nTIER: {tier_name}  (n={len(sub):,})\n{'='*100}")

    best_knot, best_mae = None, float("inf")
    for k in KNOT_GRID:
        fold_maes = []
        for i in range(N_FOLDS):
            train = sub[sub["_fold"] != i].copy()
            test = sub[sub["_fold"] == i].copy()
            train["_hinge"] = hinge(train["_raw_level"], k)
            test["_hinge"] = hinge(test["_raw_level"], k)
            m = LinearRegression().fit(train[cols + ["_hinge"]].to_numpy(), train["target"].to_numpy())
            pred = m.predict(test[cols + ["_hinge"]].to_numpy())
            fold_maes.append(float(np.abs(test["target"].to_numpy() - pred).mean()))
        avg = np.mean(fold_maes)
        flag = ""
        if avg < best_mae:
            best_mae, best_knot = avg, k
            flag = "  <-- best"
        print(f"  knot={k}  avg MAE={avg:.4f}{flag}")

    fold_maes_lin = []
    for i in range(N_FOLDS):
        train = sub[sub["_fold"] != i]
        test = sub[sub["_fold"] == i]
        m = LinearRegression().fit(train[cols].to_numpy(), train["target"].to_numpy())
        pred = m.predict(test[cols].to_numpy())
        fold_maes_lin.append(float(np.abs(test["target"].to_numpy() - pred).mean()))
    print(f"  linear-only baseline: avg MAE={np.mean(fold_maes_lin):.4f}")

    # bias by band + coefficient stability at best knot
    pred_lin = pd.Series(np.nan, index=sub.index)
    pred_hinge = pd.Series(np.nan, index=sub.index)
    for i in range(N_FOLDS):
        train = sub[sub["_fold"] != i].copy()
        test = sub[sub["_fold"] == i].copy()
        train["_hinge"] = hinge(train["_raw_level"], best_knot)
        test["_hinge"] = hinge(test["_raw_level"], best_knot)
        m_lin = LinearRegression().fit(train[cols].to_numpy(), train["target"].to_numpy())
        m_hinge = LinearRegression().fit(train[cols + ["_hinge"]].to_numpy(), train["target"].to_numpy())
        pred_lin.loc[test.index] = m_lin.predict(test[cols].to_numpy())
        pred_hinge.loc[test.index] = m_hinge.predict(test[cols + ["_hinge"]].to_numpy())
        print(f"  fold {i}: hinge coef (last term)={m_hinge.coef_[-1]:.4f}")

    sub["_bias_lin"] = sub["target"] - pred_lin
    sub["_bias_hinge"] = sub["target"] - pred_hinge
    print(f"\n  {'band':>10} {'n':>7} {'LINEAR bias':>12} {'HINGE bias':>11}")
    for lo, hi in BANDS:
        b = sub[(sub["_raw_level"] >= lo) & (sub["_raw_level"] < hi)]
        if len(b) < 5:
            continue
        print(f"  {f'{lo}-{hi}':>10} {len(b):>7,} {b['_bias_lin'].mean():>+12.2f} {b['_bias_hinge'].mean():>+11.2f}")

    # final full-data fit
    sub["_hinge_final"] = hinge(sub["_raw_level"], best_knot)
    m_final = LinearRegression().fit(sub[cols + ["_hinge_final"]].to_numpy(), sub["target"].to_numpy())
    print(f"\n  FINAL (full-data) fit: knot={best_knot}  intercept={m_final.intercept_:.4f}  "
          f"coef={m_final.coef_.round(4)}")
    return best_knot, m_final


def run():
    full = build_full()
    full = fix_wpr_nett_leak(full)
    full = full.dropna(subset=["target", "wpr_nett", "ewm5"])

    run_tier(full, "minimal", ["wpr_nett", "ewm5"])
    run_tier(full, "track", ["wpr_nett", "ewm5", "track_wpr"])
    run_tier(full, "full", ["wpr_nett", "ewm5", "track_wpr", "best3"])


if __name__ == "__main__":
    run()
