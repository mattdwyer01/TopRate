"""
wpr_new_adj_terms_candidate_test.py - builds proper leak-free candidate
ADJ_TERMS for the four Tier-1 signals that showed real, era-stable
residual bias in wpr_new_signals_tier1_audit.py (trainer_change,
horse_age, jockey_change, race weight basis), and tests a REVISED
architecture against the current one: drop own_distance/own_going/
own_trend (found to consistently HURT held-out MAE in wpr_adj_term_
ablation_10yr.py, both at small scale and across all 5 real 10-year
eras) and add these four new terms instead.

Each new term is fit the SAME way track_barrier/trainer_merit/jockey_
merit already are - wp._fit_simple_adj_model(trn, [value, field_size],
label), a small LightGBM predicting (target - career_avg) from the
candidate signal - no new architecture invented, reusing the codebase's
own established pattern. Applied via the batch-vectorized helper
(_merit_batch, already generic over any single-value+field_size
feature pair) rather than a per-row loop - see wpr_base_anchor_
fullmodel_roi_backtest.py's own docstring for why that matters at this
row count.

METHOD: leave-one-era-out (5 real eras), same as every other 10-year
script this session. For each fold, fits track_barrier/closing_merit
(kept) and the four new candidate terms (also refit per fold, leak-
free) on every OTHER era, scores the held-out era, and reports:
  1. Each new term's OWN marginal MAE contribution (current-minus-3
     baseline WITH vs WITHOUT that one new term).
  2. The full REVISED model (baseline minus own_distance/own_going/
     own_trend, plus all four new terms) vs the CURRENT model, pooled
     MAE across all 5 eras.
  3. Retrain-stability of each new term (5 independent era-fits,
     pairwise correlation/diff), matching track_barrier/closing_merit's
     own stability check.

race weight basis is encoded as a population-level categorical (SW/
HCP/QLTY/WFA/SWP/CW mapped to an integer code, same pattern track's
own track_code_map uses) rather than a per-horse lookup - a horse
rarely races under more than one or two weight bases, so there's no
meaningful "this horse's own history at this weight basis" version of
it, same reasoning track_barrier/trainer_merit/jockey_merit are
population-level rather than own-history terms.

NO EM DASHES policy: hyphens only in this file.
"""
import pickle

import numpy as np
import pandas as pd

import wpr_projection as wp
from wpr_base_calc_10yr_retest import load_combined, assign_era, ERA_BOUNDS, D_CACHE
from wpr_base_anchor_roi_backtest import base_with_anchor
from wpr_base_anchor_fullmodel_roi_backtest import (
    fit_terms_on_fold, FITTED_TERMS, _merit_batch,
)

OWN_HISTORY_KEEP = ["own_first_up", "own_second_up", "own_long_spell"]
OWN_HISTORY_CUT = ["own_distance", "own_going", "own_trend"]  # consistently hurt MAE, see docstring
CURRENT_TERMS = FITTED_TERMS + OWN_HISTORY_KEEP + OWN_HISTORY_CUT
BASELINE_MINUS_3_TERMS = FITTED_TERMS + OWN_HISTORY_KEEP  # the "keep everything proven, cut the 3 losers" base

# weight_basis_term (race weight basis - SW/HCP/QLTY/WFA/SWP/CW) is
# DELIBERATELY excluded here, not forgotten: weight_restriction is a
# race-level constant, identical for every runner in a race, same as
# field_size. Per-race demeaning (below) always zeroes out a column
# whose every value within a group already equals that group's own
# mean - the exact reason demeaning exists at all (a trained model
# latching onto a race-wide-constant feature as a proxy for a race-
# level bias, confirmed live for track_barrier/closing_merit/trainer_
# merit/jockey_merit before their own field_size-driven version of this
# bug was fixed, per project_race()'s own docstring). Testing it in
# this demeaned per-runner ADJ_TERM framework would trivially show "no
# effect" for a structural reason, not because the Tier-1 audit's
# finding was wrong - race weight basis is a real, era-stable bias, but
# it needs a base-calibration-by-race-type fix (e.g. a calibration
# slope that varies by weight_restriction), not a per-runner additive
# term. Left as a separate follow-up.
NEW_CANDIDATES = ["trainer_change_term", "age_term", "jockey_change_term"]
NEW_FEATURES = {
    "trainer_change_term": ("trainer_change", None),
    "age_term": ("horse_age_num", None),
    "jockey_change_term": ("jockey_change", None),
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
    combined = load_combined()
    D = load_D()

    print("\nMerging jockey/trainer/age from race_results...")
    side_cols = ["horse_id", "date", "race_id", "jockey", "trainer", "horse_age"]
    side = combined[side_cols].copy()
    side["date"] = pd.to_datetime(side["date"], errors="coerce")
    side["race_id"] = side["race_id"].astype(str)
    side = side.dropna(subset=["date"]).drop_duplicates(subset=["horse_id", "date", "race_id"], keep="first")

    D = D.copy()
    D["race_id"] = D["race_id"].astype(str)
    key_cols = ["horse_id", "date", "race_id"]
    before = len(D)
    D = D.merge(side, on=key_cols, how="left")
    assert len(D) == before, "signal merge changed row count"

    D = D.sort_values(["horse_id", "date"])
    D["prior_jockey"] = D.groupby("horse_id")["jockey"].shift(1)
    D["prior_trainer"] = D.groupby("horse_id")["trainer"].shift(1)
    D["jockey_change"] = ((D["jockey"] != D["prior_jockey"]) & D["prior_jockey"].notna()).astype(float)
    D["trainer_change"] = ((D["trainer"] != D["prior_trainer"]) & D["prior_trainer"].notna()).astype(float)
    D["horse_age_num"] = pd.to_numeric(D["horse_age"], errors="coerce")

    D["_era"] = assign_era(D["date"])
    era_names = [e[0] for e in ERA_BOUNDS]
    print(f"\nEra row counts:\n{D['_era'].value_counts().reindex(era_names)}")

    per_era_results = {}
    new_term_fits_by_era = {}

    for era in era_names:
        fit_half = D[D["_era"] != era].copy()
        held_out = D[D["_era"] == era].copy()
        if len(held_out) < 200:
            continue
        print(f"\nFitting on every era EXCEPT {era}, scoring held-out {era}...")
        fit_terms_on_fold(fit_half, [fit_half, held_out], "wpr_form_history.csv.gz")
        held_out["_base"] = base_with_anchor(held_out, "ewm5")
        fit_half["_base"] = base_with_anchor(fit_half, "ewm5")

        term_models = {}
        for cand in NEW_CANDIDATES:
            value_col, _ = NEW_FEATURES[cand]
            model = fit_new_term(fit_half, [fit_half, held_out], value_col, cand)
            term_models[cand] = model
        new_term_fits_by_era[era] = term_models

        # Per-race demeaning - same treatment every existing population-
        # level term (track_barrier/closing_merit/trainer_merit/jockey_
        # merit) already gets, and for the same reason: only a runner's
        # value RELATIVE to its own race matters for picking a winner,
        # not the model's absolute predicted level, which otherwise
        # pushes every runner in an easy/hard race the same direction.
        for _f in (fit_half, held_out):
            for cand in NEW_CANDIDATES:
                _f[cand] = _f[cand] - _f.groupby("race_id")[cand].transform("mean")
            _f[NEW_CANDIDATES] = _f[NEW_CANDIDATES].fillna(0.0)
            _f[CURRENT_TERMS] = _f[CURRENT_TERMS].fillna(0.0)

        variants = {
            "current_full": CURRENT_TERMS,
            "minus_3_losers": BASELINE_MINUS_3_TERMS,
            "revised_all_4_new": BASELINE_MINUS_3_TERMS + NEW_CANDIDATES,
        }
        for cand in NEW_CANDIDATES:
            variants[f"minus3_plus_{cand}"] = BASELINE_MINUS_3_TERMS + [cand]

        maes = {}
        for name, terms in variants.items():
            pred = additive_predict(held_out, terms)
            mae = float(np.abs(held_out["target"].to_numpy() - pred).mean())
            maes[name] = (mae, len(held_out))
        per_era_results[era] = maes
        print(f"  {era}: current_full={maes['current_full'][0]:.4f}  "
              f"minus_3_losers={maes['minus_3_losers'][0]:.4f}  "
              f"revised_all_4_new={maes['revised_all_4_new'][0]:.4f}")

    print(f"\n{'='*90}\nMAE COMPARISON (leave-one-era-out, pooled across 5 real eras)\n{'='*90}")
    all_variant_names = list(per_era_results[era_names[0]].keys())
    total_n = sum(per_era_results[e]["current_full"][1] for e in era_names if e in per_era_results)
    current_pooled = sum(per_era_results[e]["current_full"][0] * per_era_results[e]["current_full"][1]
                          for e in era_names if e in per_era_results) / total_n

    print(f"{'variant':<24}{'pooled avg MAE':>18}{'delta vs current':>18}")
    for name in all_variant_names:
        pooled = sum(per_era_results[e][name][0] * per_era_results[e][name][1]
                     for e in era_names if e in per_era_results) / total_n
        delta = pooled - current_pooled
        flag = ""
        if name != "current_full":
            flag = "  <-- BETTER than current" if delta < -0.01 else (
                   "  <-- WORSE than current" if delta > 0.01 else "  <-- ~same")
        print(f"{name:<24}{pooled:>18.4f}{delta:>+18.4f}{flag}")

    print("\nReading this: 'current_full' is the live-equivalent MAE (scoped to what's")
    print("testable this deep). 'minus_3_losers' isolates the effect of dropping own_")
    print("distance/own_going/own_trend alone. 'revised_all_4_new' is the full proposed")
    print("architecture (minus the 3 losers, plus all 4 new terms). The minus3_plus_X")
    print("rows isolate each new term's OWN marginal contribution on top of the trimmed base.")

    print(f"\n{'='*90}\nNEW-TERM STABILITY CHECK (5 independent era-fits, same as track_barrier's)\n{'='*90}")
    print(f"{'term':<20}{'mean pairwise corr':>20}{'mean |diff|':>14}{'std across fits (avg)':>24}")
    for cand in NEW_CANDIDATES:
        value_col, _ = NEW_FEATURES[cand]
        scored = {}
        for era, term_models in new_term_fits_by_era.items():
            frame = D.copy()
            scored[era] = _merit_batch(frame[value_col], frame["field_size"],
                                        term_models[cand], [value_col, "field_size"])
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
