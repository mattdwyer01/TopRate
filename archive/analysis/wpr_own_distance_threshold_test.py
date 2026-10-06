"""
wpr_own_distance_threshold_test.py - user's follow-up question (Sep 2026,
see chat) after being told own_distance (a shrunk per-horse average WPR
at exact-distance-matching runs, n/(n+K) discounted toward 0) consistently
HURT held-out MAE and was dropped in favour of pop_distance (a population-
level fit on dist_vs_last) - see ADJ_TERMS' own history comment in
wpr_projection.py. The user's specific proposal: instead of always
partially discounting a low-sample own-distance average, require a HARD
MINIMUM number of exact-distance matches before trusting it at all (full
weight once past the threshold, 0 below it) - a different failure-mode fix
than shrinkage, worth testing on its own rather than assuming shrinkage's
rejection settles it.

Tests this ON TOP OF the current production baseline (own_first_up/
second_up/long_spell + track_barrier + closing_merit + pop_distance +
pop_going - trainer_change is OFF in production now, see wpr_projection.py's
ADJ_TERMS comment, so it is excluded from this baseline too) to see whether
a hard-threshold own-distance term adds INCREMENTAL signal beyond what
pop_distance already captures, not whether it replaces pop_distance.

Reuses the cached 10-year D (wpr_base_calc_10yr_retest.D_CACHE) - it
already carries dist_match_n (count of this horse's own EXACT-distance
prior runs, leak-free point-in-time) and dist_match_avg (this horse's own
raw mean WPR at those runs, pre-shrink) from when own_distance was first
built, so no feature rebuild is needed - only the new term's own
threshold/shrink logic.

Candidates (raw delta = dist_match_avg - career_avg, computed once):
  - own_dist_thresh_K, K in {1, 2, 3, 4, 5}: raw delta if dist_match_n>=K
    else 0.0 (no shrink at all once past the threshold - the user's exact
    proposal, contrasted with the original always-shrunk own_distance).
  - own_dist_thresh3_shrunk: K=3 gate, but _shrink()'d (not full-strength)
    for the rows that pass it - checks whether combining "enough evidence"
    with "still discount a little" beats either extreme alone.

Same leave-one-era-out, 5-real-era framework every other 10-year backtest
here uses (wpr_adj_term_ablation_10yr.py / wpr_population_distance_going_
trend_test.py) - real, era-stable generalisation, not a single split.

NO EM DASHES policy: hyphens only in this file.
"""
import pickle

import numpy as np
import pandas as pd

import wpr_projection as wp
from wpr_base_calc_10yr_retest import assign_era, ERA_BOUNDS, D_CACHE
from wpr_base_anchor_roi_backtest import base_with_anchor
from wpr_base_anchor_fullmodel_roi_backtest import fit_terms_on_fold, FITTED_TERMS, _merit_batch

OWN_HISTORY_KEEP = ["own_first_up", "own_second_up", "own_long_spell"]
AGREED_TERMS = FITTED_TERMS + OWN_HISTORY_KEEP  # track_barrier, closing_merit, + the 3 neutral own-history terms
POP_TERMS = ["pop_distance_term", "pop_going_term"]
CURRENT_BASELINE = AGREED_TERMS + POP_TERMS  # trainer_change is OFF in production - excluded here too

THRESHOLD_CANDIDATES = ["own_dist_thresh1", "own_dist_thresh2", "own_dist_thresh3",
                         "own_dist_thresh4", "own_dist_thresh5"]
THRESHOLD_K = {"own_dist_thresh1": 1, "own_dist_thresh2": 2, "own_dist_thresh3": 3,
               "own_dist_thresh4": 4, "own_dist_thresh5": 5}
SHRUNK_VARIANT = "own_dist_thresh3_shrunk"


def load_D():
    print(f"Loading cached D from {D_CACHE} ...")
    with open(D_CACHE, "rb") as f:
        D = pickle.load(f)
    print(f"  {len(D):,} rows")
    return D


def fit_new_term(fit_half, apply_to, value_col, label):
    trn = fit_half.dropna(subset=[value_col, "target", "career_avg"])
    model = wp._fit_simple_adj_model(trn, [value_col, "field_size"], label)
    for _f in apply_to:
        _f.loc[:, label] = _merit_batch(_f[value_col], _f["field_size"], model, [value_col, "field_size"])
    return model


def additive_predict(frame, terms):
    return frame["_base"].to_numpy() + wp._cap_adj_sum(frame[terms].to_numpy()).sum(axis=1)


def add_threshold_candidates(frame):
    raw_delta = frame["dist_match_avg"] - frame["career_avg"]
    n = frame["dist_match_n"]
    for label, k in THRESHOLD_K.items():
        frame[label] = np.where(n >= k, raw_delta, 0.0).astype(float)

    passes3 = (n >= 3) & raw_delta.notna()
    shrunk = pd.Series(0.0, index=frame.index)
    if passes3.any():
        shrunk.loc[passes3] = [wp._shrink(float(d), int(nn))
                                for d, nn in zip(raw_delta[passes3], n[passes3])]
    frame[SHRUNK_VARIANT] = shrunk.to_numpy()


def run():
    D = load_D()
    D["_era"] = assign_era(D["date"])
    era_names = [e[0] for e in ERA_BOUNDS]
    print(f"\nEra row counts:\n{D['_era'].value_counts().reindex(era_names)}")

    all_new_terms = THRESHOLD_CANDIDATES + [SHRUNK_VARIANT]
    print(f"\nComputing threshold candidates ({', '.join(all_new_terms)}) once on full D "
          f"(deterministic from cached dist_match_n/dist_match_avg/career_avg, no fitting needed)...")
    add_threshold_candidates(D)
    for label in all_new_terms:
        k = THRESHOLD_K.get(label, 3)
        n_fired = int((D["dist_match_n"] >= k).sum())
        print(f"  {label}: fires on {n_fired:,}/{len(D):,} rows ({n_fired/len(D)*100:.1f}%)")

    per_era_results = {}

    for era in era_names:
        fit_half = D[D["_era"] != era].copy()
        held_out = D[D["_era"] == era].copy()
        if len(held_out) < 200:
            continue
        print(f"\nFitting on every era EXCEPT {era}, scoring held-out {era}...")
        fit_terms_on_fold(fit_half, [fit_half, held_out], "wpr_form_history.csv.gz")
        held_out["_base"] = base_with_anchor(held_out, "ewm5")
        fit_half["_base"] = base_with_anchor(fit_half, "ewm5")

        fit_new_term(fit_half, [fit_half, held_out], "dist_vs_last", "pop_distance_term")
        fit_new_term(fit_half, [fit_half, held_out], "going_delta", "pop_going_term")

        for _f in (fit_half, held_out):
            for term in POP_TERMS:
                _f[term] = _f[term] - _f.groupby("race_id")[term].transform("mean")
            _f[POP_TERMS] = _f[POP_TERMS].fillna(0.0)
            _f[AGREED_TERMS] = _f[AGREED_TERMS].fillna(0.0)
            _f[all_new_terms] = _f[all_new_terms].fillna(0.0)

        variants = {"current_baseline": CURRENT_BASELINE}
        for cand in THRESHOLD_CANDIDATES:
            variants[f"baseline_plus_{cand}"] = CURRENT_BASELINE + [cand]
        variants[f"baseline_plus_{SHRUNK_VARIANT}"] = CURRENT_BASELINE + [SHRUNK_VARIANT]

        maes = {}
        for name, terms in variants.items():
            pred = additive_predict(held_out, terms)
            mae = float(np.abs(held_out["target"].to_numpy() - pred).mean())
            maes[name] = (mae, len(held_out))
        per_era_results[era] = maes
        print(f"  {era}: " + "  ".join(f"{k}={v[0]:.4f}" for k, v in maes.items()))

    print(f"\n{'='*90}\nMAE COMPARISON (leave-one-era-out, pooled across 5 real eras)\n{'='*90}")
    all_variant_names = list(per_era_results[list(per_era_results.keys())[0]].keys())
    total_n = sum(per_era_results[e]["current_baseline"][1] for e in per_era_results)
    baseline_pooled = sum(per_era_results[e]["current_baseline"][0] * per_era_results[e]["current_baseline"][1]
                           for e in per_era_results) / total_n

    print(f"{'variant':<38}{'pooled avg MAE':>18}{'delta vs current_baseline':>28}")
    for name in all_variant_names:
        pooled = sum(per_era_results[e][name][0] * per_era_results[e][name][1]
                     for e in per_era_results) / total_n
        delta = pooled - baseline_pooled
        flag = ""
        if name != "current_baseline":
            flag = "  <-- BETTER" if delta < -0.005 else ("  <-- WORSE" if delta > 0.005 else "  <-- ~same")
        print(f"{name:<38}{pooled:>18.4f}{delta:>+28.4f}{flag}")

    print("\nSame multiple-comparisons caveat as every backtest in this codebase:")
    print("treat this as a hypothesis, not a result to ship blind.")
    print("\nDone.")


if __name__ == "__main__":
    run()
