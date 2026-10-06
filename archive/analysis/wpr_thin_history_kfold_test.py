"""
wpr_thin_history_kfold_test.py - does the EXISTING model architecture
(unchanged) already work reasonably for horses with 1-2 real prior runs,
or is _MIN_RUNS=3 excluding them for a real reason? Currently these
horses get NO projection at all - a different gap from the true-debutant
case (0 real runs, addressed separately via wpr_trial_debut_rating_kfold_
test.py's trial-based estimate) - they DO have real WPR history, just too
little of it to clear the gate.

WHY THIS IS TESTABLE WITHOUT NEW FEATURES: _compute_base()'s existing
fallback chain (wpr_nett -> ewm3 -> avg_last3 -> career_avg) and every
_shrink()-based ADJ_TERM already degrade gracefully with a small sample
size (n/(n+K) shrinkage) - nothing about the architecture assumes >=3
runs specifically. The question is purely whether n=1 or n=2 is too
noisy to beat "no projection" in practice, not whether new machinery is
needed.

_MIN_RUNS gates row INCLUSION in build_training_frame() itself, not just
serving - a cached training frame built under the shipped _MIN_RUNS=3
contains ZERO rows with 1-2 prior runs (they were excluded at
construction time). This script monkeypatches wpr._MIN_RUNS=1 for a
fresh full rebuild (like wpr_adj_cap_favourite_test.py's cap sweep did)
so those rows exist to test at all, then evaluates ONLY the newly-
eligible group (n_runs 1 or 2) - horses with 3+ runs are unaffected by
_MIN_RUNS regardless and are not the question here.

METHOD: K=4 chronological folds. Per fold: fit track_barrier/closing_
merit/trainer_merit/jockey_merit population lookups on training folds
(leak-free, as always), score the held-out fold's n_runs in {1, 2} rows
using the UNCHANGED existing model (base calibration, ADJ_TERMS, shared
adjustment slope - nothing new). Compares against the "population mean"
baseline for that same group (the honest comparison, since these horses
get nothing today), split out by n_runs=1 vs n_runs=2 separately (a
single real run is a much thinner anchor than two).

NO EM DASHES policy: hyphens only in this file.
"""
import pickle
from pathlib import Path

import numpy as np
import pandas as pd

import wpr_projection as wpr
from wpr_own_pace_backtest import add_base, add_track_barrier, merge_won_by_horse_date
from wpr_trainer_jockey_adj_strike_eval import (
    FORM_CSV, merge_trainer_jockey_by_horse_date, add_closing_merit,
    fit_bucket_lookup, apply_bucket,
)

CACHE_PATH = Path("/tmp/wpr_thin_history_frame_cache.pkl")
N_FOLDS = 4


def build_full():
    """Separate cache from the usual _MIN_RUNS=3 one (different key
    entirely - a different _MIN_RUNS produces a fundamentally different
    row set, not just a filtered version of the same one) - monkeypatches
    wpr._MIN_RUNS=1 for the WHOLE rebuild, same pattern as
    wpr_adj_cap_favourite_test.py's own-delta-cap sweep."""
    form_mtime = Path(FORM_CSV).stat().st_mtime
    if CACHE_PATH.exists():
        with open(CACHE_PATH, "rb") as fh:
            cached_mtime, full = pickle.load(fh)
        if cached_mtime == form_mtime:
            print(f"Loaded cached thin-history frame ({len(full):,} rows) - skipping the ~15-20 min rebuild.")
            full = full.drop(columns=["_base"], errors="ignore")
            return add_base(full)
        print("Cache is stale - rebuilding.")

    original_min_runs = wpr._MIN_RUNS
    wpr._MIN_RUNS = 1
    try:
        print("Rebuilding training frame with _MIN_RUNS=1 (full history, this takes a while)...")
        full = wpr.build_training_frame(FORM_CSV, verbose=True, n_jobs=-1)
    finally:
        wpr._MIN_RUNS = original_min_runs
    full["date"] = pd.to_datetime(full["date"])
    full = merge_won_by_horse_date(full)
    full = merge_trainer_jockey_by_horse_date(full)
    with open(CACHE_PATH, "wb") as fh:
        pickle.dump((form_mtime, full), fh)
    return add_base(full)


def fit_direction(fit_half, apply_frames, fit_cutoff):
    add_track_barrier(fit_half, apply_frames)
    add_closing_merit(apply_frames, fit_cutoff)
    edges_t, lookup_t = fit_bucket_lookup(fit_half, "trainer_win_pct_365d")
    edges_j, lookup_j = fit_bucket_lookup(fit_half, "jockey_win_pct_90d")
    for f in apply_frames:
        apply_bucket(f, "trainer_win_pct_365d", edges_t, lookup_t, "trainer_merit")
        apply_bucket(f, "jockey_win_pct_90d", edges_j, lookup_j, "jockey_merit")
        f["_base_calib"] = f["_base"].apply(wpr._calibrate_base)
        f["adj_total"] = wpr._cap_adj_sum(f[wpr.ADJ_TERMS].to_numpy()).sum(axis=1) * wpr._CALIB_ADJ_SLOPE
        f["proj"] = f["_base_calib"] + f["adj_total"]


def run():
    full = build_full()
    print(f"\nFull frame (min_runs=1): {len(full):,} rows")
    print(f"n_runs distribution (bottom of range): {full['n_runs'].value_counts().sort_index().head(6).to_dict()}")

    non_pop_terms = [t for t in wpr.ADJ_TERMS
                     if t not in ("track_barrier", "closing_merit", "trainer_merit", "jockey_merit")]
    full = full.dropna(subset=["target", "_base", "career_avg", "n_runs"] + non_pop_terms +
                        ["barrier", "field_size", "track", "cur_distance",
                         "trainer_win_pct_365d", "jockey_win_pct_90d"])
    full = full.sort_values("date").reset_index(drop=True)
    print(f"Scoped rows: {len(full):,}")

    thin = full[full["n_runs"].isin([1, 2])]
    print(f"n_runs=1: {(full['n_runs'] == 1).sum():,}   n_runs=2: {(full['n_runs'] == 2).sum():,}   "
          f"(total thin-history rows to evaluate: {len(thin):,})")

    fold_edges = np.array_split(np.arange(len(full)), N_FOLDS)
    full["_fold"] = -1
    for i, idx in enumerate(fold_edges):
        full.loc[idx, "_fold"] = i

    print(f"\n{'='*100}\nK={N_FOLDS}-fold: existing model (unchanged) vs population-mean baseline, "
          f"for n_runs in {{1, 2}}\n{'='*100}")

    results = {1: {"base_mae": [], "model_mae": []}, 2: {"base_mae": [], "model_mae": []}}
    for i in range(N_FOLDS):
        test = full[full["_fold"] == i].copy()
        train = full[full["_fold"] != i].copy()
        fit_direction(train, [train, test], train["date"].max())

        for nr in (1, 2):
            train_g = train[train["n_runs"] == nr]
            test_g = test[test["n_runs"] == nr]
            if len(test_g) < 20 or len(train_g) < 20:
                print(f"  fold {i}, n_runs={nr}: too few rows (train={len(train_g)}, test={len(test_g)}), skipped")
                continue
            train_mean = train_g["target"].mean()
            mae_base = (test_g["target"] - train_mean).abs().mean()
            mae_model = (test_g["target"] - test_g["proj"]).abs().mean()
            results[nr]["base_mae"].append(mae_base)
            results[nr]["model_mae"].append(mae_model)
            print(f"  fold {i}, n_runs={nr} (n={len(test_g):,}): "
                  f"baseline(train mean={train_mean:.1f}) MAE={mae_base:.4f}   "
                  f"model MAE={mae_model:.4f}   "
                  f"({'better' if mae_model < mae_base else 'worse/same'})")

    print(f"\n{'='*100}\nSummary\n{'='*100}")
    for nr in (1, 2):
        b, m = results[nr]["base_mae"], results[nr]["model_mae"]
        if not b:
            continue
        print(f"  n_runs={nr}: avg baseline MAE={np.mean(b):.4f}  avg model MAE={np.mean(m):.4f}  "
              f"model better in every fold: {all(mm < bb for mm, bb in zip(m, b))}")

    print("\nSame multiple-comparisons caveat as the other bet-selection scripts: treat this")
    print("as a hypothesis for a future walk-forward period, not a result to ship blindly.")


if __name__ == "__main__":
    run()
