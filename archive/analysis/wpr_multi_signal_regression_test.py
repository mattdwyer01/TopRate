"""
wpr_multi_signal_regression_test.py - the natural follow-up to wpr_signal_
strike_margin_combo_test.py: that script's equal-weight "top4" combination
(wpr_nett/ewm3/avg_last3/best3) already beat the shipped 2-signal alpha=0.40
blend on MAE (6.6916 vs 6.7506) using naive equal weights. This tests
whether a properly FIT multiple regression across those signals does
better still, and whether the gain survives once multicollinearity is
accounted for (the 6 standalone signals correlate 0.85-0.98 with each
other - see the correlation check this session ran directly - so OLS
coefficients on more than 2-3 of them at once can be unstable even if the
fitted MAE looks good in-sample).

Coverage matters here: wpr_nett/ewm3/avg_last3 are ~99.8% complete
(43,679/43,752), but best3 is only ~62% complete (26,964/43,752) - a
production fallback would need a tier (best3-available vs not), so this
also checks whether best3 earns its keep ON THE SUBSET where it's
available, not just pooled with everything else.

METHOD: same leak-corrected build, K=4 chronological folds, complete-case
rows only per model (a row missing any of that model's inputs is dropped
for both fitting and scoring - consistent with how the shipped model
already requires wpr_nett+ewm3 present to use the blend path at all).
Both OLS and Ridge (alpha=1.0, standardized inputs) are fit per fold to
see whether regularization changes anything given the collinearity.

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np
import pandas as pd
from sklearn.linear_model import LinearRegression, Ridge
from sklearn.preprocessing import StandardScaler

from wpr_alpha_08_leak_corrected_validation import build_full, fix_wpr_nett_leak

N_FOLDS = 4

MODELS = {
    "shipped: wpr_nett*0.4 + ewm3*0.6 (fixed weight)": ["wpr_nett", "ewm3"],
    "OLS: wpr_nett + ewm3": ["wpr_nett", "ewm3"],
    "OLS: wpr_nett + ewm3 + avg_last3": ["wpr_nett", "ewm3", "avg_last3"],
    "OLS: wpr_nett + ewm3 + avg_last3 + best3": ["wpr_nett", "ewm3", "avg_last3", "best3"],
    "OLS: all 6 signals": ["wpr_nett", "ewm3", "avg_last3", "career_avg", "recent5_max", "best3"],
    "Ridge(a=1): wpr_nett + ewm3 + avg_last3 + best3": ["wpr_nett", "ewm3", "avg_last3", "best3"],
    "Ridge(a=1): all 6 signals": ["wpr_nett", "ewm3", "avg_last3", "career_avg", "recent5_max", "best3"],
}


def fixed_weight_predict(train, test, cols, weights):
    w = np.array(weights)
    train_raw = train[cols].to_numpy() @ w
    test_raw = test[cols].to_numpy() @ w
    slope, intercept = np.polyfit(train_raw, train["target"].to_numpy(), 1)
    return intercept + slope * test_raw


def ols_predict(train, test, cols):
    model = LinearRegression()
    model.fit(train[cols].to_numpy(), train["target"].to_numpy())
    return model.predict(test[cols].to_numpy()), model.coef_, model.intercept_


def ridge_predict(train, test, cols, alpha=1.0):
    scaler = StandardScaler()
    xtr = scaler.fit_transform(train[cols].to_numpy())
    xte = scaler.transform(test[cols].to_numpy())
    model = Ridge(alpha=alpha)
    model.fit(xtr, train["target"].to_numpy())
    return model.predict(xte), model.coef_, model.intercept_


def run():
    full = build_full()
    full = fix_wpr_nett_leak(full)
    full = full.dropna(subset=["target"]).sort_values("date").reset_index(drop=True)
    print(f"Scoped rows: {len(full):,}")

    fold_edges = np.array_split(np.arange(len(full)), N_FOLDS)
    full["_fold"] = -1
    for i, idx in enumerate(fold_edges):
        full.loc[idx, "_fold"] = i

    print(f"\n{'='*100}\nMULTI-SIGNAL BASE: fixed-weight blend vs fitted regression (K={N_FOLDS}-fold, "
          f"complete-case per model)\n{'='*100}")
    print(f"  {'model':<48} {'avg MAE':>9} {'n(rows)':>9}  coefficients (last fold, for inspection)")
    for name, cols in MODELS.items():
        sub_full = full.dropna(subset=cols)
        sub_full = sub_full.copy()
        sub_full["_fold2"] = -1
        fold_edges2 = np.array_split(np.arange(len(sub_full)), N_FOLDS)
        sub_full = sub_full.sort_values("date").reset_index(drop=True)
        for i, idx in enumerate(fold_edges2):
            sub_full.loc[idx, "_fold2"] = i

        fold_maes = []
        last_info = ""
        for i in range(N_FOLDS):
            train = sub_full[sub_full["_fold2"] != i]
            test = sub_full[sub_full["_fold2"] == i]
            if name.startswith("shipped"):
                pred = fixed_weight_predict(train, test, cols, [0.4, 0.6])
                last_info = "weights=[0.4, 0.6] (fixed, not fit)"
            elif name.startswith("OLS"):
                pred, coef, intercept = ols_predict(train, test, cols)
                last_info = "coef=" + ", ".join(f"{c:.3f}" for c in coef) + f"  intercept={intercept:.3f}"
            else:
                pred, coef, intercept = ridge_predict(train, test, cols)
                last_info = "coef(std)=" + ", ".join(f"{c:.3f}" for c in coef) + f"  intercept={intercept:.3f}"
            mae = float(np.abs(test["target"].to_numpy() - pred).mean())
            fold_maes.append(mae)
        avg_mae = np.mean(fold_maes)
        print(f"  {name:<48} {avg_mae:>9.4f} {len(sub_full):>9,}  {last_info}")

    print(f"\n{'='*100}\nMATCHED-SUBSET CHECK: same models, but ALL scored on only the rows where "
          f"best3 is available\n(rules out 'the best3 subset is just easier to predict' confounding "
          f"the table above)\n{'='*100}")
    matched = full.dropna(subset=["wpr_nett", "ewm3", "avg_last3", "best3"]).copy()
    matched = matched.sort_values("date").reset_index(drop=True)
    matched["_fold3"] = -1
    for i, idx in enumerate(np.array_split(np.arange(len(matched)), N_FOLDS)):
        matched.loc[idx, "_fold3"] = i
    print(f"  {'model':<48} {'avg MAE':>9} {'n(rows)':>9}")
    for name, cols in MODELS.items():
        fold_maes = []
        for i in range(N_FOLDS):
            train = matched[matched["_fold3"] != i]
            test = matched[matched["_fold3"] == i]
            if name.startswith("shipped"):
                pred = fixed_weight_predict(train, test, cols, [0.4, 0.6])
            elif name.startswith("OLS"):
                pred, _, _ = ols_predict(train, test, cols)
            else:
                pred, _, _ = ridge_predict(train, test, cols)
            fold_maes.append(float(np.abs(test["target"].to_numpy() - pred).mean()))
        print(f"  {name:<48} {np.mean(fold_maes):>9.4f} {len(matched):>9,}")

    print("\nSame caveats as always: leak-free-for-wpr_nett K-fold, but one dataset/attempt. Ridge "
          "coefficients are on STANDARDIZED inputs (comparable magnitudes across signals); OLS "
          "coefficients are on the raw WPR scale.")


if __name__ == "__main__":
    run()
