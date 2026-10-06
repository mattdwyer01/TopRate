"""
wpr_base_constrained_tier_test.py - tests whether a PROPERLY constrained
(weights >=0, summing to exactly 1 - i.e. a true convex combination) fit
of the reverted multi-signal base regression (wpr_nett, ewm5, track_wpr,
best3) both (a) avoids the below-all-inputs structural bug that got the
original unconstrained tiered regression reverted (see _BASE_BLEND_ALPHA's
history in wpr_projection.py - that fit had weights summing to 0.801,
including one NEGATIVE weight, so a horse's base could land below every
one of its own inputs) and (b) matches or beats the currently-shipped
simple two-signal alpha=0.30 wpr_nett/ewm5 blend on held-out MAE.

Simplification vs the original "3-tier" design: track_wpr already falls
back internally to avg_last3 when a horse has no prior run at today's
track (see wpr_projection.py's build_features, "track_wpr = ... else
avg_last3"), so it is essentially always populated once a horse clears
_MIN_RUNS - there is no real "missing track_wpr" case left to tier on the
way there once might have been. best3 (mean of best 3 of last 6 runs)
has the same minimal requirement as ewm5 (>=1 prior run), so it is also
essentially always available alongside ewm5. So this fits ONE constrained
4-signal regression on every row that has all four inputs, rather than
per-availability tiers - a cleaner test of the same underlying question
(does properly-constrained multi-signal weighting beat the 2-signal
blend), without the tier-selection ambiguity of the original design.

METHOD: reuses wpr_alpha_08_leak_corrected_validation.py's exact
leak-corrected data build (wpr_nett re-merged from toprate_runners.csv by
(horse, date, race_id), not build_training_frame()'s contaminated run_id
merge) and wpr_best_anchor_signal_test.py's exact K=4 chronological-fold
convention, so results are directly comparable to those two scripts'
numbers. Weights fit via SLSQP (bounds [0,1] per weight, equality
constraint sum(weights)=1, minimizing mean squared error on the training
fold), matching a regression in spirit while enforcing the "true convex
combination" property missing from the original fit. Also explicitly
checks, per held-out row, whether the constrained prediction ever falls
outside [min(inputs), max(inputs)] - should be mathematically impossible
if the fit is correct, checked empirically as a sanity guard, and to
directly answer whether this construction can reproduce the Autumn-
Glow-style failure (base below every input) that killed the original.

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np
import pandas as pd
from scipy.optimize import minimize

from wpr_alpha_08_leak_corrected_validation import build_full, fix_wpr_nett_leak

N_FOLDS = 4
SIGNALS = ["wpr_nett", "ewm5", "track_wpr", "best3"]
TWO_SIGNAL_ALPHA = 0.30  # the currently-shipped wpr_nett weight, see _BASE_BLEND_ALPHA


def fit_constrained(X, y):
    """weights >=0, sum to 1, minimizing MSE on (X, y) - a true convex
    combination, unlike the original tiered regression's unconstrained fit."""
    n = X.shape[1]
    w0 = np.full(n, 1.0 / n)
    cons = {"type": "eq", "fun": lambda w: w.sum() - 1.0}
    bounds = [(0.0, 1.0)] * n
    res = minimize(lambda w: float(np.mean((X @ w - y) ** 2)), w0,
                   method="SLSQP", bounds=bounds, constraints=[cons],
                   options={"maxiter": 200, "ftol": 1e-10})
    if not res.success:
        print(f"    WARNING: constrained fit did not converge cleanly ({res.message})")
    return res.x


def two_signal_alpha_blend(frame, alpha=TWO_SIGNAL_ALPHA):
    return alpha * frame["wpr_nett"] + (1 - alpha) * frame["ewm5"]


def run():
    full = build_full()
    full = fix_wpr_nett_leak(full)
    full = full.dropna(subset=["target"] + SIGNALS).sort_values("date").reset_index(drop=True)
    print(f"\nScoped rows (target + all 4 signals present): {len(full):,}")

    fold_edges = np.array_split(np.arange(len(full)), N_FOLDS)
    full["_fold"] = -1
    for i, idx in enumerate(fold_edges):
        full.loc[idx, "_fold"] = i

    X_all = full[SIGNALS].to_numpy(dtype=float)
    y_all = full["target"].to_numpy(dtype=float)
    two_signal_all = two_signal_alpha_blend(full).to_numpy(dtype=float)

    print(f"\n{'='*90}\nCONSTRAINED (weights >=0, sum to 1) 4-signal regression vs current 2-signal "
          f"blend\nK={N_FOLDS} chronological folds, held-out MAE\n{'='*90}")

    fold_maes_constrained, fold_maes_twosig, fold_weights = [], [], []
    total_rows_checked = 0
    total_violations = 0

    for i in range(N_FOLDS):
        train_mask = full["_fold"].to_numpy() != i
        test_mask = ~train_mask

        w = fit_constrained(X_all[train_mask], y_all[train_mask])
        fold_weights.append(w)

        pred_constrained = X_all[test_mask] @ w
        mae_constrained = float(np.abs(pred_constrained - y_all[test_mask]).mean())
        fold_maes_constrained.append(mae_constrained)

        mae_twosig = float(np.abs(two_signal_all[test_mask] - y_all[test_mask]).mean())
        fold_maes_twosig.append(mae_twosig)

        # structural check: constrained prediction must lie within
        # [min(inputs), max(inputs)] for every held-out row
        row_min = X_all[test_mask].min(axis=1)
        row_max = X_all[test_mask].max(axis=1)
        violations = int(((pred_constrained < row_min - 1e-6) | (pred_constrained > row_max + 1e-6)).sum())
        total_violations += violations
        total_rows_checked += test_mask.sum()

        print(f"  fold {i}: weights={dict(zip(SIGNALS, np.round(w, 4)))}  "
              f"sum={w.sum():.6f}")
        print(f"          constrained MAE={mae_constrained:.4f}   2-signal-blend MAE={mae_twosig:.4f}   "
              f"n={test_mask.sum():,}   out-of-range violations={violations}")

    print(f"\n{'-'*90}")
    print(f"avg constrained MAE: {np.mean(fold_maes_constrained):.4f}")
    print(f"avg 2-signal blend MAE (current shipped alpha={TWO_SIGNAL_ALPHA}): {np.mean(fold_maes_twosig):.4f}")
    print(f"delta: {np.mean(fold_maes_constrained) - np.mean(fold_maes_twosig):+.4f}")
    print(f"\nstructural check: {total_violations} / {total_rows_checked:,} held-out predictions fell "
          f"outside [min(inputs), max(inputs)] (should be 0 if the constrained fit is correct)")

    avg_weights = np.mean(fold_weights, axis=0)
    print(f"\naverage fitted weights across folds: {dict(zip(SIGNALS, np.round(avg_weights, 4)))} "
          f"(sum={avg_weights.sum():.4f})")


if __name__ == "__main__":
    run()
