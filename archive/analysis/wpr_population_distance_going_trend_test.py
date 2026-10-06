"""
wpr_population_distance_going_trend_test.py - user's follow-up question
(Sep 2026, see chat) after agreeing to cut own_distance/own_going/
own_trend (all three consistently HURT held-out MAE, confirmed at both
small scale and across all 5 real 10-year eras - see wpr_adj_term_
ablation_10yr.py): "can population distance, going or trend help
instead?"

own_distance/own_going/own_trend are per-horse SHRUNK LOOKUPS - this
horse's own deviation from ITS OWN average when racing at conditions
like today's, shrunk by how many of ITS OWN prior runs match. That
requires enough matching-condition history from THIS SPECIFIC HORSE to
be reliable - shrinkage helps but can't fully compensate for a horse
with little own history at today's conditions.

This tests the OPPOSITE architecture for the same underlying concepts,
matching track_barrier/trainer_change's own design: a population-level
LightGBM model (wp._fit_simple_adj_model, same helper, same "predict
residual-from-career_avg" pattern) fit across EVERY horse at once, fed
the SAME already-computed, pre-race-known, leak-safe raw signals these
own-history terms are themselves built from:
  - dist_vs_last: today's distance minus this horse's last-run distance
    (a direct, continuous analog to what own_distance groups into bands)
  - going_delta: this horse's own wet-minus-dry performance differential
    (the same raw signal own_going's condition-matching draws from)
  - trend: last WPR minus the mean of the two runs before it (the same
    raw signal own_trend is built from)
A population fit can generalize the general RELATIONSHIP between these
continuous signals and residual across the whole population, even for
horses whose OWN history is too sparse for the per-horse version to
say anything reliable - potentially recovering real signal the shrunk-
lookup version was throwing away as noise.

BASELINE for this test: the wpr_new_adj_terms_candidate_test.py
finding already agreed on - own_distance/own_going/own_trend cut,
trainer_change added (the single best result there), track_barrier/
closing_merit kept. This tests whether adding a population version of
distance/going/trend ON TOP of that agreed baseline helps further -
same leave-one-era-out MAE framework, same 5 real eras, same batch-
vectorized term application.

NO EM DASHES policy: hyphens only in this file.
"""
import pickle

import numpy as np
import pandas as pd

import wpr_projection as wp
from wpr_base_calc_10yr_retest import load_combined, assign_era, ERA_BOUNDS, D_CACHE
from wpr_base_anchor_roi_backtest import base_with_anchor
from wpr_base_anchor_fullmodel_roi_backtest import fit_terms_on_fold, FITTED_TERMS, _merit_batch

OWN_HISTORY_KEEP = ["own_first_up", "own_second_up", "own_long_spell"]
AGREED_TERMS = FITTED_TERMS + OWN_HISTORY_KEEP  # track_barrier, closing_merit, and the 3 neutral own-history terms
BEST_SO_FAR = AGREED_TERMS + ["trainer_change_term"]  # the agreed baseline (see docstring)

POP_CANDIDATES = ["pop_distance_term", "pop_going_term", "pop_trend_term"]
POP_FEATURES = {
    "pop_distance_term": "dist_vs_last",
    "pop_going_term": "going_delta",
    "pop_trend_term": "trend",
}


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


def run():
    combined = load_combined()  # noqa: F841 - loaded for parity, all needed signals already in D_CACHE
    D = load_D()

    print("\nComputing trainer_change (own-history, leak-free, needed for BEST_SO_FAR)...")
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
    D["trainer_change"] = ((D["trainer"] != D["prior_trainer"]) & D["prior_trainer"].notna()).astype(float)

    D["_era"] = assign_era(D["date"])
    era_names = [e[0] for e in ERA_BOUNDS]
    print(f"\nEra row counts:\n{D['_era'].value_counts().reindex(era_names)}")

    per_era_results = {}
    pop_term_fits_by_era = {}

    for era in era_names:
        fit_half = D[D["_era"] != era].copy()
        held_out = D[D["_era"] == era].copy()
        if len(held_out) < 200:
            continue
        print(f"\nFitting on every era EXCEPT {era}, scoring held-out {era}...")
        fit_terms_on_fold(fit_half, [fit_half, held_out], "wpr_form_history.csv.gz")
        held_out["_base"] = base_with_anchor(held_out, "ewm5")
        fit_half["_base"] = base_with_anchor(fit_half, "ewm5")

        trainer_change_model = fit_new_term(fit_half, [fit_half, held_out], "trainer_change", "trainer_change_term")

        pop_models = {}
        for cand in POP_CANDIDATES:
            value_col = POP_FEATURES[cand]
            model = fit_new_term(fit_half, [fit_half, held_out], value_col, cand)
            pop_models[cand] = model
        pop_term_fits_by_era[era] = pop_models

        all_new_terms = ["trainer_change_term"] + POP_CANDIDATES
        for _f in (fit_half, held_out):
            for term in all_new_terms:
                _f[term] = _f[term] - _f.groupby("race_id")[term].transform("mean")
            _f[all_new_terms] = _f[all_new_terms].fillna(0.0)
            _f[AGREED_TERMS] = _f[AGREED_TERMS].fillna(0.0)

        variants = {
            "best_so_far": BEST_SO_FAR,
        }
        for cand in POP_CANDIDATES:
            variants[f"best_plus_{cand}"] = BEST_SO_FAR + [cand]
        variants["best_plus_all_3_pop"] = BEST_SO_FAR + POP_CANDIDATES
        # pop_trend_term hurt on its own and dragged down the all-3
        # combination - checking distance+going WITHOUT trend to see if
        # the two winners combine cleanly or also interact negatively
        # (same lesson as trainer_change/age/jockey_change earlier).
        variants["best_plus_distance_and_going"] = BEST_SO_FAR + ["pop_distance_term", "pop_going_term"]

        maes = {}
        for name, terms in variants.items():
            pred = additive_predict(held_out, terms)
            mae = float(np.abs(held_out["target"].to_numpy() - pred).mean())
            maes[name] = (mae, len(held_out))
        per_era_results[era] = maes
        print(f"  {era}: " + "  ".join(f"{k}={v[0]:.4f}" for k, v in maes.items()))

    print(f"\n{'='*90}\nMAE COMPARISON (leave-one-era-out, pooled across 5 real eras)\n{'='*90}")
    all_variant_names = list(per_era_results[era_names[0]].keys())
    total_n = sum(per_era_results[e]["best_so_far"][1] for e in era_names if e in per_era_results)
    baseline_pooled = sum(per_era_results[e]["best_so_far"][0] * per_era_results[e]["best_so_far"][1]
                           for e in era_names if e in per_era_results) / total_n

    print(f"{'variant':<28}{'pooled avg MAE':>18}{'delta vs best_so_far':>22}")
    for name in all_variant_names:
        pooled = sum(per_era_results[e][name][0] * per_era_results[e][name][1]
                     for e in era_names if e in per_era_results) / total_n
        delta = pooled - baseline_pooled
        flag = ""
        if name != "best_so_far":
            flag = "  <-- BETTER than agreed baseline" if delta < -0.005 else (
                   "  <-- WORSE than agreed baseline" if delta > 0.005 else "  <-- ~same")
        print(f"{name:<28}{pooled:>18.4f}{delta:>+22.4f}{flag}")

    print(f"\n{'='*90}\nPOPULATION TERM STABILITY CHECK (5 independent era-fits)\n{'='*90}")
    print(f"{'term':<20}{'mean pairwise corr':>20}{'mean |diff|':>14}{'std across fits (avg)':>24}")
    for cand in POP_CANDIDATES:
        value_col = POP_FEATURES[cand]
        scored = {}
        for era, pop_models in pop_term_fits_by_era.items():
            frame = D.copy()
            scored[era] = _merit_batch(frame[value_col], frame["field_size"],
                                        pop_models[cand], [value_col, "field_size"])
        vals = np.stack(list(scored.values()), axis=1)
        mask = ~np.isnan(vals).any(axis=1)
        vals = vals[mask]
        corrs, diffs = [], []
        for i in range(vals.shape[1]):
            for j in range(i + 1, vals.shape[1]):
                corrs.append(np.corrcoef(vals[:, i], vals[:, j])[0, 1])
                diffs.append(np.mean(np.abs(vals[:, i] - vals[:, j])))
        std_across = np.std(vals, axis=1).mean()
        print(f"{cand:<20}{np.mean(corrs):>20.3f}{np.mean(diffs):>14.3f}{std_across:>24.3f}")

    print("\nSame multiple-comparisons caveat as every backtest in this codebase:")
    print("treat this as a hypothesis, not a result to ship blind.")
    print("\nDone.")


if __name__ == "__main__":
    run()
