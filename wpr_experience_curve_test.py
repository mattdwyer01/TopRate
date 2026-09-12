"""
wpr_experience_curve_test.py - user's follow-up question (Sep 2026, see
chat): for lightly-raced horses (under ~10 starts), is there a natural
"improvement curve" - does a horse on start 2 tend to rate above its
start-1 level, start 3 above start 2, etc - that the current model isn't
already capturing?

This is DIFFERENT from own_trend/pop_trend (already tested and rejected,
see ADJ_TERMS' own history comment) - those compare a horse's OWN recent
WPR level against its OWN earlier runs (a per-horse relative measure).
This tests something else: n_runs (how many real prior runs this horse
has, i.e. what start number it is on today) as a POPULATION-LEVEL
predictor of residual = target - career_avg, same architecture as
pop_distance/pop_going (wp._fit_simple_adj_model) - "does EVERY horse at
n_runs=1 tend to outperform its own career_avg by roughly the same amount,
regardless of its own trend so far" - a maturation/experience effect, not
an own-history trend.

n_runs is already one of the base model's 53 FEATURES (confidence-
interval quantile models see it), but NOT part of the additive
base+ADJ_TERMS point projection that actually drives ratings/prices
(base = wpr_nett/ewm blend + ADJ_TERMS sum - see CLAUDE.md) - so this is
a real, previously untested gap in the POINT projection specifically.

Candidates (population-fit, same pattern as pop_distance/pop_going):
  - pop_experience_all: n_runs (+field_size) fit across the WHOLE
    population, no restriction - lets the model find any curve shape,
    including plateau/decline for seasoned campaigners.
  - pop_experience_lightly_raced: same fit, but restricted to n_runs<=12
    rows only (fit AND applied only there, 0 elsewhere) - isolates the
    "young horse improving" question the user actually asked, rather
    than picking up unrelated seasoned-campaigner variation.

Tested ON TOP OF the current production baseline (own_first_up/second_up/
long_spell + track_barrier + closing_merit + pop_distance + pop_going -
trainer_change is OFF in production, excluded here too), same leave-one-
era-out 10yr framework as wpr_own_distance_threshold_test.py /
wpr_population_distance_going_trend_test.py.

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
AGREED_TERMS = FITTED_TERMS + OWN_HISTORY_KEEP
POP_TERMS = ["pop_distance_term", "pop_going_term"]
CURRENT_BASELINE = AGREED_TERMS + POP_TERMS

LIGHTLY_RACED_CUTOFF = 12
CANDIDATES = ["pop_experience_all", "pop_experience_lightly_raced"]


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


def fit_experience_terms(fit_half, apply_to):
    model_all = fit_new_term(fit_half, apply_to, "n_runs", "pop_experience_all")

    lightly_raced = fit_half[fit_half["n_runs"] <= LIGHTLY_RACED_CUTOFF]
    trn = lightly_raced.dropna(subset=["n_runs", "target", "career_avg"])
    model_lr = wp._fit_simple_adj_model(trn, ["n_runs", "field_size"], "pop_experience_lightly_raced")
    for _f in apply_to:
        vals = _merit_batch(_f["n_runs"], _f["field_size"], model_lr, ["n_runs", "field_size"])
        vals = np.where(_f["n_runs"].to_numpy() <= LIGHTLY_RACED_CUTOFF, vals, 0.0)
        _f.loc[:, "pop_experience_lightly_raced"] = vals
    return model_all, model_lr


def run():
    D = load_D()
    D["_era"] = assign_era(D["date"])
    era_names = [e[0] for e in ERA_BOUNDS]
    print(f"\nEra row counts:\n{D['_era'].value_counts().reindex(era_names)}")

    per_era_results = {}
    fits_by_era = {}

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
        model_all, model_lr = fit_experience_terms(fit_half, [fit_half, held_out])
        fits_by_era[era] = (model_all, model_lr)

        all_new_terms = POP_TERMS + CANDIDATES
        for _f in (fit_half, held_out):
            for term in POP_TERMS + ["pop_experience_all"]:
                _f[term] = _f[term] - _f.groupby("race_id")[term].transform("mean")
            # pop_experience_lightly_raced is 0.0 for n_runs>12 rows by
            # construction above - still demean WITHIN each race (same
            # convention every population term uses, see project_race()'s
            # own comment on why: a trained model can otherwise latch onto
            # a field-shared feature as a race-wide bias).
            _f["pop_experience_lightly_raced"] = (
                _f["pop_experience_lightly_raced"]
                - _f.groupby("race_id")["pop_experience_lightly_raced"].transform("mean"))
            _f[all_new_terms] = _f[all_new_terms].fillna(0.0)
            _f[AGREED_TERMS] = _f[AGREED_TERMS].fillna(0.0)

        variants = {"current_baseline": CURRENT_BASELINE}
        for cand in CANDIDATES:
            variants[f"baseline_plus_{cand}"] = CURRENT_BASELINE + [cand]
        variants["baseline_plus_both"] = CURRENT_BASELINE + CANDIDATES

        maes = {}
        maes_lr_only = {}
        lr_mask = held_out["n_runs"] <= LIGHTLY_RACED_CUTOFF
        for name, terms in variants.items():
            pred = additive_predict(held_out, terms)
            mae = float(np.abs(held_out["target"].to_numpy() - pred).mean())
            maes[name] = (mae, len(held_out))
            mae_lr = float(np.abs(held_out.loc[lr_mask, "target"].to_numpy() - pred[lr_mask.to_numpy()]).mean())
            maes_lr_only[name] = (mae_lr, int(lr_mask.sum()))
        per_era_results[era] = (maes, maes_lr_only)
        print(f"  {era} (all rows): " + "  ".join(f"{k}={v[0]:.4f}" for k, v in maes.items()))
        print(f"  {era} (n_runs<={LIGHTLY_RACED_CUTOFF} only, {int(lr_mask.sum()):,} rows): "
              + "  ".join(f"{k}={v[0]:.4f}" for k, v in maes_lr_only.items()))

    def pool(key_idx, name):
        total_n = sum(per_era_results[e][key_idx][name][1] for e in per_era_results)
        return sum(per_era_results[e][key_idx][name][0] * per_era_results[e][key_idx][name][1]
                   for e in per_era_results) / total_n, total_n

    all_variant_names = list(per_era_results[list(per_era_results.keys())[0]][0].keys())

    for key_idx, label in [(0, "ALL ROWS"), (1, f"n_runs<={LIGHTLY_RACED_CUTOFF} ONLY")]:
        print(f"\n{'='*90}\nMAE COMPARISON, {label} (leave-one-era-out, pooled across 5 real eras)\n{'='*90}")
        baseline_pooled, _ = pool(key_idx, "current_baseline")
        print(f"{'variant':<34}{'pooled avg MAE':>18}{'delta vs current_baseline':>28}")
        for name in all_variant_names:
            pooled, n = pool(key_idx, name)
            delta = pooled - baseline_pooled
            flag = ""
            if name != "current_baseline":
                flag = "  <-- BETTER" if delta < -0.005 else ("  <-- WORSE" if delta > 0.005 else "  <-- ~same")
            print(f"{name:<34}{pooled:>18.4f}{delta:>+28.4f}{flag}  (n={n:,})")

    print(f"\n{'='*90}\nEXPERIENCE CURVE SHAPE (population model's own predicted residual by n_runs)\n{'='*90}")
    print("Averaging the pop_experience_lightly_raced model's raw (pre-demean) prediction\n"
          "across the 5 era-fits, at field_size=10 (typical), for n_runs=1..12:")
    sample_fs = 10.0
    for nr in range(1, LIGHTLY_RACED_CUTOFF + 1):
        preds = []
        for era, (model_all, model_lr) in fits_by_era.items():
            row = pd.DataFrame([{"n_runs": float(nr), "field_size": sample_fs}])
            preds.append(float(model_lr.predict(row)[0]))
        print(f"  n_runs={nr:>2}: mean predicted residual = {np.mean(preds):+.3f}  (across-era range "
              f"{min(preds):+.3f} to {max(preds):+.3f})")

    print("\nSame multiple-comparisons caveat as every backtest in this codebase:")
    print("treat this as a hypothesis, not a result to ship blind.")
    print("\nDone.")


if __name__ == "__main__":
    run()
