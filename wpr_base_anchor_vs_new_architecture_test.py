"""
wpr_base_anchor_vs_new_architecture_test.py - re-validates the ewm7/
ewm10 vs ewm5 base-anchor MAE finding (wpr_base_calc_10yr_retest.py)
against the REVISED ADJ_TERMS composition just shipped (Sep 2026, see
chat): own_distance/own_going/own_trend cut, trainer_change/pop_
distance/pop_going added.

WHY THIS MATTERS: the original ewm7/ewm10 test scored the base anchor
either alone (wpr_base_anchor_roi_backtest.py, later found untrustworthy
- fitted beta pinned at the grid floor) or against the OLD full model
(wpr_base_anchor_fullmodel_roi_backtest.py, base + track_barrier +
closing_merit + the OLD own_distance/own_going/own_trend). Neither
reflects what is actually shipped today. The additive model is base +
sum(ADJ_TERMS), and the ADJ_TERMS set materially changed - a base-
anchor comparison is only meaningful against the model that will
actually use it.

Also tests the user's own follow-up proposal (Sep 2026): rather than one
fixed ewm span for every horse, use ewm10 once a horse has >=10 prior
runs to actually fill that window meaningfully, cascading down to a
shorter, faster-decaying span for lightly-raced horses (ewm7 at >=7
runs, ewm5 at >=5, ewm3 otherwise) - "ewm_cascade" below.

SCOPE: same testable-this-deep subset as every other 10-year script -
track_barrier, closing_merit, and the NEW trainer_change/pop_distance/
pop_going (all population-fit per era-fold, leak-free), plus the three
neutral own-history terms (own_first_up/own_second_up/own_long_spell,
no fitting needed). trainer_merit/jockey_merit/pace_shape stay excluded
(recency-limited data / fold-aware leak-safety, same reasons as always).

METHOD: leave-one-era-out across the same 5 real eras, MAE only (ROI
stays deliberately deferred per the user's own explicit direction until
a dedicated, trustworthy pricing methodology exists).

NO EM DASHES policy: hyphens only in this file.
"""
import pickle

import numpy as np
import pandas as pd

import wpr_projection as wp
from wpr_base_calc_10yr_retest import load_combined, vectorized_ewm, compute_void_mask, assign_era, ERA_BOUNDS, D_CACHE
from wpr_base_anchor_roi_backtest import base_with_anchor
from wpr_base_anchor_fullmodel_roi_backtest import fit_terms_on_fold, FITTED_TERMS, _merit_batch

OWN_HISTORY_KEEP = ["own_first_up", "own_second_up", "own_long_spell"]
NEW_TERMS = ["trainer_change", "pop_distance", "pop_going"]
FULL_NEW_TERMS = FITTED_TERMS + OWN_HISTORY_KEEP + NEW_TERMS  # the actual shipped composition (testable subset)

NEW_TERM_FEATURES = {
    "trainer_change": ("trainer_change_raw", wp._TRAINER_CHANGE_FEATURES),
    "pop_distance": ("dist_vs_last", wp._POP_DISTANCE_FEATURES),
    "pop_going": ("going_delta", wp._POP_GOING_FEATURES),
}

ANCHOR_CANDIDATES = ["ewm5", "ewm7", "ewm10"]


def load_D():
    print(f"Loading cached D from {D_CACHE} ...")
    with open(D_CACHE, "rb") as f:
        D = pickle.load(f)
    print(f"  {len(D):,} rows")
    return D


def fit_new_term(fit_half, apply_to, value_col, features, label):
    trn = fit_half.dropna(subset=[value_col, "target", "career_avg"])
    trn = trn.rename(columns={value_col: features[0]}) if value_col != features[0] else trn
    model = wp._fit_simple_adj_model(trn, features, label)
    for _f in apply_to:
        _f.loc[:, label] = _merit_batch(_f[value_col], _f["field_size"], model, features)
    return model


def additive_predict(frame, anchor_col):
    base = base_with_anchor(frame, anchor_col)
    return base.to_numpy() + wp._cap_adj_sum(frame[FULL_NEW_TERMS].to_numpy()).sum(axis=1)


def run():
    combined = load_combined()
    D = load_D()

    print("\nComputing trainer_change (own-history, leak-free) and ewm7/ewm10...")
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

    void_mask = compute_void_mask(combined)
    for span in (7, 10):
        c = vectorized_ewm(combined, span, "wpr", void_mask_col=void_mask)
        c = c.rename(columns={f"ewm{span}_wpr": f"ewm{span}"})
        D = D.merge(c, on=key_cols, how="left")

    # ewm_cascade (user's proposal, Sep 2026): use ewm10 once a horse has
    # enough of its OWN history (>=10 prior runs) to fill that window
    # meaningfully, cascading down to a shorter, faster-decaying span for
    # lightly-raced horses instead of applying one fixed window to every
    # horse regardless of how much own history it actually has.
    D["ewm_cascade"] = np.select(
        [D["n_runs"] >= 10, D["n_runs"] >= 7, D["n_runs"] >= 5],
        [D["ewm10"], D["ewm7"], D["ewm5"]],
        default=D["ewm3"])
    ANCHOR_CANDIDATES.append("ewm_cascade")

    D["_era"] = assign_era(D["date"])
    era_names = [e[0] for e in ERA_BOUNDS]
    print(f"\nEra row counts:\n{D['_era'].value_counts().reindex(era_names)}")

    per_era_results = {}
    for era in era_names:
        fit_half = D[D["_era"] != era].copy()
        held_out = D[D["_era"] == era].copy()
        if len(held_out) < 200:
            continue
        print(f"\nFitting on every era EXCEPT {era}, scoring held-out {era}...")
        fit_terms_on_fold(fit_half, [fit_half, held_out], "wpr_form_history.csv.gz")
        for new_term, (value_col, features) in NEW_TERM_FEATURES.items():
            fit_new_term(fit_half, [fit_half, held_out], value_col, features, new_term)

        for _f in (fit_half, held_out):
            for term in NEW_TERMS:
                _f[term] = _f[term] - _f.groupby("race_id")[term].transform("mean")
            _f[FULL_NEW_TERMS] = _f[FULL_NEW_TERMS].fillna(0.0)

        maes = {}
        for anchor in ANCHOR_CANDIDATES:
            pred = additive_predict(held_out, anchor)
            mae = float(np.abs(held_out["target"].to_numpy() - pred).mean())
            maes[anchor] = (mae, len(held_out))
        per_era_results[era] = maes
        print(f"  {era}: " + "  ".join(f"{k}={v[0]:.4f}" for k, v in maes.items()))

    print(f"\n{'='*90}\nBASE ANCHOR MAE COMPARISON, NEW ARCHITECTURE (leave-one-era-out, pooled)\n{'='*90}")
    total_n = sum(per_era_results[e]["ewm5"][1] for e in era_names if e in per_era_results)
    ewm5_pooled = sum(per_era_results[e]["ewm5"][0] * per_era_results[e]["ewm5"][1]
                       for e in era_names if e in per_era_results) / total_n

    print(f"{'anchor':<12}{'pooled avg MAE':>18}{'delta vs ewm5':>16}   per-era MAE")
    for anchor in ANCHOR_CANDIDATES:
        pooled = sum(per_era_results[e][anchor][0] * per_era_results[e][anchor][1]
                     for e in era_names if e in per_era_results) / total_n
        delta = pooled - ewm5_pooled
        flag = ""
        if anchor != "ewm5":
            flag = "  <-- BETTER than shipped ewm5" if delta < -0.005 else (
                   "  <-- WORSE than shipped ewm5" if delta > 0.005 else "  <-- ~same")
        per_era_str = "  ".join(f"{e}={per_era_results[e][anchor][0]:.3f}" for e in era_names if e in per_era_results)
        print(f"{anchor:<12}{pooled:>18.4f}{delta:>+16.4f}{flag}\n    [{per_era_str}]")

    print("\nReading this: this is the SAME comparison as wpr_base_calc_10yr_retest.py's")
    print("MAE finding, but scored against the ACTUAL new ADJ_TERMS composition just")
    print("shipped, not the old one. If ewm7/ewm10 still win here, the earlier finding")
    print("holds under the new architecture and is a green light to ship the anchor swap.")
    print("\nSame multiple-comparisons caveat as every backtest in this codebase:")
    print("treat this as a hypothesis, not a result to ship blind.")
    print("\nDone.")


if __name__ == "__main__":
    run()
