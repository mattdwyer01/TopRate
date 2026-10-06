"""
wpr_trainer_jockey_quality_change_mae_test.py - MAE test for the
quality-aware trainer_change/jockey_change candidate (step 2, after
wpr_trainer_jockey_quality_change_test.py has built and pickled D with
trainer_quality_delta/jockey_quality_delta already computed).

Fits a small population model on the quality delta (new trainer/jockey's
win% minus the old one's, at the time of the switch - leak-free asof
lookup, see the build script's own docstring), same _fit_simple_adj_model
pattern every other population term uses, and compares against the
CURRENT shipped trainer_change (binary flag) on held-out MAE.

SCOPE: like trainer_merit/jockey_merit, only testable within the
trainer_win_pct_365d-covered subset (toprate_runners.csv's own recent
window - the full history doesn't have this data). Uses the same H1/H2
split on the covered subset's own dates that trainer_merit/jockey_merit
validation already established (wpr_adj_term_ablation_and_stability.py),
not the full 10-year era framework (doesn't apply here - see
wpr_alpha_reopt_for_ewm7_test.py's own docstring for the same class of
scope limitation).

DELIBERATELY EXCLUDES track_barrier/closing_merit/trainer_merit/
jockey_merit/pace_shape from the comparison base (each needs its own
two-stage own-history+population fit, unrelated to what this test is
actually asking) - own_first_up/second_up/long_spell + pop_distance/
pop_going + trainer_change (or its quality-delta replacement) form the
comparison base instead. This means the absolute MAE numbers here will
NOT match production's real MAE - only the RELATIVE delta between
variants (all missing the same terms equally) is the actual question.

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np
import pandas as pd

import wpr_projection as wp
from wpr_base_anchor_fullmodel_roi_backtest import _merit_batch

D_PKL = "/tmp/claude-0/-home-user-TopRate/95a262de-71bd-5daf-b05e-b7e3031f09dd/scratchpad/quality_delta_D.pkl"

OWN_HISTORY_KEEP = ["own_first_up", "own_second_up", "own_long_spell"]
BASE_TERMS = OWN_HISTORY_KEEP + ["pop_distance", "pop_going"]
CURRENT_TERMS = BASE_TERMS + ["trainer_change"]
CANDIDATE_TRAINER_ONLY = BASE_TERMS + ["trainer_quality_term"]
CANDIDATE_BOTH = BASE_TERMS + ["trainer_quality_term", "jockey_quality_term"]
ALL_TERMS_UNION = list(set(CURRENT_TERMS + CANDIDATE_BOTH))


def fit_and_apply(fit_half, apply_to, value_col, label):
    trn = fit_half.dropna(subset=[value_col, "target", "career_avg"])
    model = wp._fit_simple_adj_model(trn, [value_col, "field_size"], label)
    for _f in apply_to:
        _f.loc[:, label] = _merit_batch(_f[value_col], _f["field_size"], model, [value_col, "field_size"])
    return model


def additive_predict(frame, terms):
    return frame["_base"].to_numpy() + wp._cap_adj_sum(frame[terms].to_numpy()).sum(axis=1)


def run():
    print(f"Loading D from {D_PKL} ...")
    D = pd.read_pickle(D_PKL)
    print(f"  {len(D):,} rows")

    print("Computing base (wp._compute_base, row by row - small recent-window dataset, no need to vectorise)...")
    D["_base"] = [wp._compute_base(row.to_dict()) for _, row in D.iterrows()]

    covered = D.dropna(subset=["trainer_win_pct_365d", "target", "career_avg"])
    print(f"\nCovered subset (trainer_win_pct_365d available): {len(covered):,} rows")
    mid = covered["date"].quantile(0.5)
    print(f"H1/H2 split at {mid}")

    h1 = D[D["date"] < mid].copy()
    h2 = D[D["date"] >= mid].copy()

    results = {}
    for fit_half, held_out, label in [(h1, h2, "H1->H2"), (h2, h1, "H2->H1")]:
        fit_half = fit_half.copy()
        held_out = held_out.copy()

        for value_col, term in [("dist_vs_last", "pop_distance"), ("going_delta", "pop_going"),
                                 ("trainer_change_raw", "trainer_change")]:
            fit_and_apply(fit_half, [fit_half, held_out], value_col, term)

        fit_and_apply(fit_half, [fit_half, held_out], "trainer_quality_delta", "trainer_quality_term")
        fit_and_apply(fit_half, [fit_half, held_out], "jockey_quality_delta", "jockey_quality_term")

        for _f in (fit_half, held_out):
            for term in ["pop_distance", "pop_going", "trainer_change", "trainer_quality_term", "jockey_quality_term"]:
                _f[term] = _f[term] - _f.groupby("race_id")[term].transform("mean")
            _f[ALL_TERMS_UNION] = _f[ALL_TERMS_UNION].fillna(0.0)

        maes = {}
        for name, terms in [
            ("current (binary trainer_change)", CURRENT_TERMS),
            ("quality delta (trainer only)", CANDIDATE_TRAINER_ONLY),
            ("quality delta (trainer + jockey)", CANDIDATE_BOTH),
        ]:
            pred = additive_predict(held_out, terms)
            mae = float(np.abs(held_out["target"].to_numpy() - pred).mean())
            maes[name] = (mae, len(held_out))
        results[label] = maes
        print(f"\n{label} ({len(held_out):,} held-out rows):")
        for name, (mae, n) in maes.items():
            print(f"  {name:<35}{mae:.4f}")

    print(f"\n{'='*80}\nPOOLED (H1->H2 + H2->H1)\n{'='*80}")
    total_n = sum(results[l]["current (binary trainer_change)"][1] for l in results)
    pooled_current = sum(results[l]["current (binary trainer_change)"][0] * results[l]["current (binary trainer_change)"][1]
                          for l in results) / total_n
    for name in ["current (binary trainer_change)", "quality delta (trainer only)", "quality delta (trainer + jockey)"]:
        pooled = sum(results[l][name][0] * results[l][name][1] for l in results) / total_n
        delta = pooled - pooled_current
        flag = ""
        if name != "current (binary trainer_change)":
            flag = "  <-- BETTER" if delta < -0.01 else ("  <-- WORSE" if delta > 0.01 else "  <-- ~same")
        print(f"  {name:<35}{pooled:.4f}{delta:+.4f}{flag}")

    print("\nSame multiple-comparisons caveat as every backtest in this codebase:")
    print("treat this as a hypothesis, not a result to ship blind.")
    print("\nDone.")


if __name__ == "__main__":
    run()
