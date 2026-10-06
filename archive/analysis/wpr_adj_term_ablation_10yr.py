"""
wpr_adj_term_ablation_10yr.py - the 10-year-deep upgrade of
wpr_adj_term_ablation_and_stability.py (see chat, Sep 2026: "should we
not be using the 10 year dataset for adjustment review? all adjs
should be reviewed again"). That script's H1/H2 split on wpr_form_
history.csv.gz suffers the SAME recency-skew problem the base-anchor
work already found and fixed for (98%+ of rows 2022 onward) - and its
stability check only ever compares TWO independent fits (H1 vs H2).

This reuses the already-built 10-year D_CACHE (wpr_base_calc_10yr_
retest.py) and the 5 real eras (2017-2020, 2021-2022, 2023, 2024,
2025-2026) to redo both parts with genuine era diversity:

1. LEAVE-ONE-TERM-OUT MAE ABLATION: same idea as the small-scale
   script (drop one ADJ_TERM at a time, compare held-out MAE), but
   leave-one-ERA-out (5 folds) instead of H1/H2 (2 folds) - a much
   better test of whether a term's contribution holds up across
   genuinely different market eras, not just one arbitrary 50/50 split.

2. RETRAIN-STABILITY CHECK: fits track_barrier/closing_merit on EACH of
   the 5 eras independently (5 fits, not 2), then scores the SAME
   pooled population with all 5 fits and reports the SPREAD across all
   5 (not just one pairwise comparison) - directly answers "how much
   would this term's value for a given horse/race have differed
   depending on the accident of which market era it was fit on", with
   5 data points per row instead of 2.

SCOPE: same limitation as every other 10-year-deep script this session
- trainer_merit/jockey_merit need trainer_win_pct_365d/jockey_win_
pct_90d, which only exist in toprate_runners.csv's last ~4 months of
daily snapshots, so they CANNOT be tested this deep (they stay covered
by the small-scale wpr_adj_term_ablation_and_stability.py script
instead, which is the right tool for them). pace_shape stays excluded
for the fold-aware-leak-safety reason already documented throughout
this session. This script covers: track_barrier, closing_merit, and
the six own-history terms (own_distance, own_going, own_first_up,
own_second_up, own_trend, own_long_spell).

NO EM DASHES policy: hyphens only in this file.
"""
import pickle

import numpy as np
import pandas as pd

import wpr_projection as wp
from wpr_base_calc_10yr_retest import load_combined, assign_era, ERA_BOUNDS, D_CACHE
from wpr_base_anchor_roi_backtest import base_with_anchor
from wpr_base_anchor_fullmodel_roi_backtest import (
    fit_terms_on_fold, FITTED_TERMS, _closing_raw_resid_one,
    _track_barrier_batch, _closing_merit_batch,
)

OWN_HISTORY_TERMS = ["own_distance", "own_going", "own_first_up", "own_second_up",
                      "own_trend", "own_long_spell"]
ABLATION_TERMS = FITTED_TERMS + OWN_HISTORY_TERMS  # trainer_merit/jockey_merit/pace_shape excluded, see docstring


def load_D():
    print(f"Loading cached D from {D_CACHE} ...")
    with open(D_CACHE, "rb") as f:
        D = pickle.load(f)
    print(f"  {len(D):,} rows")
    return D


def _additive_predict(frame, drop_term=None):
    # _cap_adj_sum operates generically on whatever (n_rows, n_terms) array
    # it's given (confirmed directly in wpr_projection.py) - no need to pad
    # out to the full 11-wide wp.ADJ_TERMS just to use it on this 8-term subset.
    terms = [t for t in ABLATION_TERMS if t != drop_term] if drop_term else list(ABLATION_TERMS)
    return frame["_base"].to_numpy() + wp._cap_adj_sum(frame[terms].to_numpy()).sum(axis=1)


def run_ablation(D, era_names):
    """Leave-one-era-out: for each era, every OTHER era fits the trained
    terms, and MAE for the full/leave-one-out variants is scored on that
    era only. Returns per-era MAE dicts plus the 5 independent model
    fits (for the stability check)."""
    per_era_maes = {}
    all_models = {}
    for era in era_names:
        fit_half = D[D["_era"] != era].copy()
        held_out = D[D["_era"] == era].copy()
        if len(held_out) < 200:
            continue
        print(f"\nFitting on every era EXCEPT {era}, scoring held-out {era}...")
        models = fit_terms_on_fold(fit_half, [fit_half, held_out], "wpr_form_history.csv.gz")
        all_models[era] = models

        held_out["_base"] = base_with_anchor(held_out, "ewm5")
        variants = ["full"] + [f"minus_{t}" for t in ABLATION_TERMS]
        maes = {}
        for v in variants:
            drop = None if v == "full" else v[len("minus_"):]
            pred = _additive_predict(held_out, drop_term=drop)
            mae = float(np.abs(held_out["target"].to_numpy() - pred).mean())
            maes[v] = (mae, len(held_out))
        per_era_maes[era] = maes
        print(f"  {era}: full MAE = {maes['full'][0]:.4f}  (n={maes['full'][1]:,})")
    return per_era_maes, all_models


def report_ablation(per_era_maes, era_names):
    print(f"\n{'='*90}\nLEAVE-ONE-TERM-OUT MAE ABLATION (leave-one-era-out, 5 real eras)\n{'='*90}")
    variants = ["full"] + [f"minus_{t}" for t in ABLATION_TERMS]
    total_n = sum(per_era_maes[e]["full"][1] for e in era_names if e in per_era_maes)
    full_pooled = sum(per_era_maes[e]["full"][0] * per_era_maes[e]["full"][1]
                       for e in era_names if e in per_era_maes) / total_n

    print(f"{'variant':<20}{'pooled avg MAE':>18}{'delta vs full':>16}   per-era MAE")
    for v in variants:
        pooled_mae = sum(per_era_maes[e][v][0] * per_era_maes[e][v][1]
                          for e in era_names if e in per_era_maes) / total_n
        delta = pooled_mae - full_pooled
        flag = ""
        if v != "full":
            flag = "  <-- removing HURTS" if delta > 0.01 else (
                   "  <-- removing HELPS/neutral" if delta < -0.01 else "  <-- ~neutral")
        per_era_str = "  ".join(f"{e}={per_era_maes[e][v][0]:.3f}" for e in era_names if e in per_era_maes)
        print(f"{v:<20}{pooled_mae:>18.4f}{delta:>+16.4f}{flag}\n    [{per_era_str}]")

    print("\nReading this: 'full' is the current shipped-equivalent MAE (both terms in,")
    print("scoped to what's testable this deep). A POSITIVE delta for 'minus_X' means")
    print("removing X makes MAE WORSE across genuinely different market eras (earning")
    print("its keep); near-zero or negative means X isn't adding much this deep.")


def run_stability(D, era_names, all_models):
    """Applies EACH era's independently-fit track_barrier/closing_merit
    models to the SAME fixed population (all of D) and reports the
    spread across all 5 fits per row - a genuine 5-way stability check,
    not just one pairwise H1-vs-H2 comparison."""
    print(f"\n{'='*90}\nRETRAIN-STABILITY CHECK (same rows, scored by {len(all_models)} independent era-fits)\n{'='*90}")

    scored = {}
    for era, models in all_models.items():
        frame = D.copy()
        tcm = models["track_code_map"]
        frame.loc[:, "track_code"] = frame["track"].map(tcm).fillna(-1).astype(int)
        frame.loc[:, "track_barrier"] = _track_barrier_batch(frame, tcm, models["track_barrier_model"])
        _computed = [_closing_raw_resid_one(p, models["pace_baseline_lookup"]) for p in frame["closing_pairs"]]
        frame.loc[:, "closing_raw_resid"] = [c[0] for c in _computed]
        frame.loc[:, "closing_n_pairs"] = [c[1] for c in _computed]
        frame.loc[:, "closing_merit"] = _closing_merit_batch(frame, models["closing_merit_model"])
        for _term in FITTED_TERMS:
            frame[_term] = frame[_term] - frame.groupby("race_id")[_term].transform("mean")
        scored[era] = frame

    print(f"\n{'n rows scored by every fit':>28}: {len(D):,}")
    print(f"{'term':<16}{'mean pairwise corr':>20}{'mean |diff|':>14}{'std across fits (avg)':>24}")
    for t in FITTED_TERMS:
        vals = np.stack([scored[era][t].to_numpy() for era in all_models], axis=1)
        mask = ~np.isnan(vals).any(axis=1)
        vals = vals[mask]
        corrs = []
        diffs = []
        for i in range(vals.shape[1]):
            for j in range(i + 1, vals.shape[1]):
                corrs.append(np.corrcoef(vals[:, i], vals[:, j])[0, 1])
                diffs.append(np.mean(np.abs(vals[:, i] - vals[:, j])))
        std_across = np.std(vals, axis=1).mean()
        print(f"{t:<16}{np.mean(corrs):>20.3f}{np.mean(diffs):>14.3f}{std_across:>24.3f}")

    print("\nReading this: high mean pairwise corr (near 1.0) and low mean|diff|/std across")
    print("fits = stable (barely depends on which era happened to fit it). Low corr or a")
    print("std across fits that is large relative to the term's own typical magnitude =")
    print("volatile - a real, era-to-era instability, not a 2-way coin flip.")


def run():
    combined = load_combined()  # noqa: F841 - kept for parity/side-checks if needed
    D = load_D()
    D["_era"] = assign_era(D["date"])
    era_names = [e[0] for e in ERA_BOUNDS]
    print(f"\nEra row counts:\n{D['_era'].value_counts().reindex(era_names)}")

    per_era_maes, all_models = run_ablation(D, era_names)
    report_ablation(per_era_maes, era_names)
    run_stability(D, era_names, all_models)

    print("\nSame multiple-comparisons caveat as every backtest in this codebase:")
    print("treat this as a hypothesis, not a result to ship blind.")
    print("\nDone.")


if __name__ == "__main__":
    run()
