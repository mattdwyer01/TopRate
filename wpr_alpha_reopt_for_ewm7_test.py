"""
wpr_alpha_reopt_for_ewm7_test.py - re-optimizes _BASE_BLEND_ALPHA (the
wpr_nett weight in base = alpha*wpr_nett + (1-alpha)*anchor) specifically
for the ewm7 anchor, now that ewm7 has shipped (see _compute_base's own
docstring: "_BASE_BLEND_ALPHA (0.30) was NOT re-optimized specifically
for the ewm7 partner - the same alpha was applied uniformly to every
anchor candidate in this comparison for a fair test; revisiting alpha
itself for ewm7 specifically is a worthwhile future refinement, not yet
done").

METHODOLOGY NOTE (important, found the hard way): the FIRST version of
this script ran the usual 10-year leave-one-era-out framework and got a
literally identical MAE at every alpha in the sweep - a dead giveaway
of a broken test, not a real null result. Root cause: wpr_nett (TopRate's
own automated pre-race rating) has 0% coverage before 2026 and only 45%
coverage even within 2026 in the 10-year dataset - it is a genuinely
recent-only signal (see wpr_projection.py's own build_features
docstring: "By far the single largest accuracy gain found in the Aug
2026 feature search"). With wpr_nett missing on 95%+ of 10-year rows,
_compute_base's fallback chain (nett.fillna(anchor)) collapses the
blend to 100% ewm7 regardless of alpha for almost the entire dataset -
alpha genuinely cannot be measured there. Switched to the SAME K=4-fold
chronological method the ORIGINAL alpha=0.30 value was derived under
(see wpr_projection.py's own history comments), scoped to ONLY the
wpr_nett-covered window (2026-04-26 onward, ~51.5k rows) so every row
in every fold actually exercises the alpha blend.

METHOD: the covered window is split into 4 equal-length chronological
chunks; each fold fits every population ADJ_TERM (track_barrier,
closing_merit, trainer_change, pop_distance, pop_going - the actual
testable-this-deep shipped subset) on the OTHER 3 chunks and scores
held-out MAE on the 4th, sweeping alpha at score time (alpha needs no
fitting - base_with_alpha is a fixed formula, not a trained model).

NO EM DASHES policy: hyphens only in this file.
"""
import pickle

import numpy as np
import pandas as pd

import wpr_projection as wp
from wpr_base_calc_10yr_retest import (
    load_combined, vectorized_ewm, compute_void_mask, D_CACHE,
)
from wpr_base_anchor_fullmodel_roi_backtest import fit_terms_on_fold, FITTED_TERMS, _merit_batch

OWN_HISTORY_KEEP = ["own_first_up", "own_second_up", "own_long_spell"]
SHIPPED_NEW_TERMS = ["trainer_change", "pop_distance", "pop_going"]
FULL_TERMS = FITTED_TERMS + OWN_HISTORY_KEEP + SHIPPED_NEW_TERMS  # actual live composition (testable subset)

SHIPPED_NEW_TERM_FEATURES = {
    "trainer_change": ("trainer_change_raw", wp._TRAINER_CHANGE_FEATURES),
    "pop_distance": ("dist_vs_last", wp._POP_DISTANCE_FEATURES),
    "pop_going": ("going_delta", wp._POP_GOING_FEATURES),
}

ALPHA_GRID = [round(a, 2) for a in np.arange(0.05, 0.65, 0.05)]
N_FOLDS = 4


def load_D():
    print(f"Loading cached D from {D_CACHE} ...")
    with open(D_CACHE, "rb") as f:
        D = pickle.load(f)
    print(f"  {len(D):,} rows")
    return D


def fit_shipped_new_term(fit_half, apply_to, value_col, features, label):
    trn = fit_half.dropna(subset=[value_col, "target", "career_avg"])
    trn = trn.rename(columns={value_col: features[0]}) if value_col != features[0] else trn
    model = wp._fit_simple_adj_model(trn, features, label)
    for _f in apply_to:
        _f.loc[:, label] = _merit_batch(_f[value_col], _f["field_size"], model, features)
    return model


def base_with_alpha(D, alpha, anchor_col="ewm7"):
    """Same fallback chain as wp._compute_base/base_with_anchor, but with
    alpha as a parameter instead of the fixed wp._BASE_BLEND_ALPHA."""
    nett, anchor = D["wpr_nett"], D[anchor_col]
    both = nett.notna() & anchor.notna()
    base = pd.Series(
        np.where(both, alpha * nett + (1 - alpha) * anchor, nett.fillna(anchor)),
        index=D.index)
    return base.fillna(D["avg_last3"]).fillna(D["career_avg"])


def additive_predict(frame, alpha):
    base = base_with_alpha(frame, alpha)
    return base.to_numpy() + wp._cap_adj_sum(frame[FULL_TERMS].to_numpy()).sum(axis=1)


def run():
    combined = load_combined()
    D = load_D()

    print("\nComputing trainer_change (own-history, leak-free)...")
    side_cols = ["horse_id", "date", "race_id", "trainer"]
    side = combined[side_cols].copy()
    side["date"] = pd.to_datetime(side["date"], errors="coerce")
    side["race_id"] = side["race_id"].astype(str)
    side = side.dropna(subset=["date"]).drop_duplicates(subset=["horse_id", "date", "race_id"], keep="first")
    D = D.copy()
    D["race_id"] = D["race_id"].astype(str)
    key_cols = ["horse_id", "date", "race_id"]
    before = len(D)
    D = D.merge(side, on=key_cols, how="left")
    assert len(D) == before, "trainer merge changed row count"
    D = D.sort_values(["horse_id", "date"])
    D["prior_trainer"] = D.groupby("horse_id")["trainer"].shift(1)
    D["trainer_change_raw"] = ((D["trainer"] != D["prior_trainer"]) & D["prior_trainer"].notna()).astype(float)

    print("\nComputing ewm7 (the shipped base anchor, not in the cached D)...")
    void_mask = compute_void_mask(combined)
    c = vectorized_ewm(combined, 7, "wpr", void_mask_col=void_mask)
    c = c.rename(columns={"ewm7_wpr": "ewm7"})
    D = D.merge(c, on=key_cols, how="left")

    # SCOPE: only rows where wpr_nett actually exists - see module
    # docstring for why the full 10-year set can't measure alpha at all.
    D = D[D["wpr_nett"].notna()].copy()
    D = D.sort_values("date")
    print(f"\nwpr_nett-covered window: {D['date'].min()} to {D['date'].max()}, {len(D):,} rows")

    # K=4-fold chronological - same method the original alpha=0.30 was
    # derived under (see module docstring), scoped to this covered window.
    fold_bounds = pd.qcut(D["date"].rank(method="first"), N_FOLDS, labels=False)
    D["_fold"] = fold_bounds

    per_fold_results = {}
    for fold in range(N_FOLDS):
        fit_half = D[D["_fold"] != fold].copy()
        held_out = D[D["_fold"] == fold].copy()
        if len(held_out) < 200:
            continue
        print(f"\nFold {fold+1}/{N_FOLDS}: fitting on the other 3 folds, "
              f"scoring held-out fold ({held_out['date'].min().date()} to {held_out['date'].max().date()}, "
              f"{len(held_out):,} rows)...")
        fit_terms_on_fold(fit_half, [fit_half, held_out], "wpr_form_history.csv.gz")
        for new_term, (value_col, features) in SHIPPED_NEW_TERM_FEATURES.items():
            fit_shipped_new_term(fit_half, [fit_half, held_out], value_col, features, new_term)

        for _f in (fit_half, held_out):
            for term in SHIPPED_NEW_TERMS:
                _f[term] = _f[term] - _f.groupby("race_id")[term].transform("mean")
            _f[FULL_TERMS] = _f[FULL_TERMS].fillna(0.0)

        maes = {}
        for alpha in ALPHA_GRID:
            pred = additive_predict(held_out, alpha)
            mae = float(np.abs(held_out["target"].to_numpy() - pred).mean())
            maes[alpha] = (mae, len(held_out))
        per_fold_results[fold] = maes
        best_alpha = min(maes, key=lambda a: maes[a][0])
        print(f"  fold {fold+1}: best alpha={best_alpha} (MAE {maes[best_alpha][0]:.4f}), "
              f"current shipped alpha=0.30 MAE {maes[0.3][0] if 0.3 in maes else float('nan'):.4f}")

    print(f"\n{'='*90}\nALPHA SWEEP MAE COMPARISON (K={N_FOLDS}-fold chronological, pooled)\n{'='*90}")
    total_n = sum(per_fold_results[f][ALPHA_GRID[0]][1] for f in per_fold_results)
    pooled_maes = {}
    for alpha in ALPHA_GRID:
        pooled = sum(per_fold_results[f][alpha][0] * per_fold_results[f][alpha][1]
                     for f in per_fold_results) / total_n
        pooled_maes[alpha] = pooled
    ref = pooled_maes[0.3]
    best_overall = min(pooled_maes, key=lambda a: pooled_maes[a])
    print(f"{'alpha':<10}{'pooled avg MAE':>18}{'delta vs 0.30':>16}")
    for alpha in ALPHA_GRID:
        delta = pooled_maes[alpha] - ref
        flag = ""
        if alpha == best_overall:
            flag = "  <-- BEST"
        if abs(alpha - 0.30) < 1e-9:
            flag += "  <-- CURRENTLY SHIPPED"
        print(f"{alpha:<10}{pooled_maes[alpha]:>18.4f}{delta:>+16.4f}{flag}")

    print(f"\nBest overall alpha: {best_overall} (pooled MAE {pooled_maes[best_overall]:.4f}, "
          f"vs 0.30's {ref:.4f}, delta {pooled_maes[best_overall]-ref:+.4f})")

    print(f"\n{'='*90}\nPER-FOLD BEST ALPHA (does the optimum move around, or is it stable)\n{'='*90}")
    for fold in per_fold_results:
        maes = per_fold_results[fold]
        best = min(maes, key=lambda a: maes[a][0])
        print(f"  fold {fold+1}: best alpha={best} (MAE {maes[best][0]:.4f})")

    print("\nReading this: if the pooled-best alpha is close to 0.30 and/or the per-fold-best")
    print("alpha bounces around a lot, 0.30 is already a reasonable choice and not worth a")
    print("special-cased change for ewm7. A clear, fold-stable pooled improvement is a green")
    print("light to ship a new _BASE_BLEND_ALPHA value.")
    print("\nSame multiple-comparisons caveat as every backtest in this codebase:")
    print("treat this as a hypothesis, not a result to ship blind.")
    print("\nDone.")


if __name__ == "__main__":
    run()
