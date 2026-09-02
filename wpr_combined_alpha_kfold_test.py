"""
wpr_combined_alpha_kfold_test.py - properly validated follow-up to the
comprehensive circumstance screen: combines the surviving candidates
(lightly-raced 3-7 runs, small field <=8, gear change today, improving
recent trend) into ONE formula instead of testing them as independent
flags, and validates with K=4 chronological folds instead of a single
50/50 split - the screen's own seasoned-horse buckets showed real
in-sample alpha-selection noise (a bucket's own fitted alpha scored
WORSE held-out than just using the global figure), so a single split
isn't enough evidence to act on before a real formula change.

CANDIDATE FORMULA:
  is_uncertain = (n_runs < 8) OR (is_small_field) OR (gear_changes today)
                 OR (own_trend > 0, i.e. improving off its last 2 runs)
  alpha = base_alpha + BUMP if is_uncertain else base_alpha (capped at 1.0)

For each of K=4 chronological folds (each held out once, fit on the
other 3 combined - NOT just one 50/50 split), grid-searches (base_alpha,
bump) jointly on the training folds, minimising MAE on those rows, then
scores the held-out fold with that fit. Reports per-fold MAE (so any
instability is visible, not hidden by averaging) for three candidates:
  (a) shipped flat 0.5
  (b) single global alpha, no circumstance layer (bump=0 forced)
  (c) the combined circumstance-aware formula (base_alpha + bump free)
so the marginal value of the circumstance layer ON TOP OF a corrected
global alpha is isolated, not conflated with the base_alpha shift itself
(which Test A already validated independently).

NO EM DASHES policy: hyphens only in this file.
"""
import pickle
from pathlib import Path

import numpy as np
import pandas as pd

import wpr_projection as wpr
from wpr_own_pace_backtest import add_base, merge_won_by_horse_date
from wpr_trainer_jockey_adj_strike_eval import FORM_CSV, merge_trainer_jockey_by_horse_date
from wpr_bet_selection_post_retrain import merge_price_pfm

CACHE_PATH = Path("/tmp/wpr_full_training_frame_cache.pkl")
BASE_ALPHA_GRID = [0.5, 0.6, 0.7, 0.8, 0.9, 1.0]
BUMP_GRID = [0.0, 0.05, 0.1, 0.15, 0.2]
N_FOLDS = 4


def build_full():
    form_mtime = Path(FORM_CSV).stat().st_mtime
    if CACHE_PATH.exists():
        with open(CACHE_PATH, "rb") as fh:
            cached_mtime, full = pickle.load(fh)
        if cached_mtime == form_mtime:
            print(f"Loaded cached training frame ({len(full):,} rows) - skipping the ~15-20 min rebuild.")
            return full
        print("Cache is stale - rebuilding.")
    print("Rebuilding training frame (full history, this takes a while)...")
    full = wpr.build_training_frame(FORM_CSV, verbose=True, n_jobs=-1)
    full["date"] = pd.to_datetime(full["date"])
    full = merge_won_by_horse_date(full)
    full = merge_trainer_jockey_by_horse_date(full)
    full = merge_price_pfm(full)
    full = add_base(full)
    non_pop_terms = [t for t in wpr.ADJ_TERMS
                     if t not in ("track_barrier", "closing_merit", "trainer_merit", "jockey_merit")]
    full = full.dropna(subset=["target", "_base", "career_avg"] + non_pop_terms +
                        ["barrier", "field_size", "track", "cur_distance"])
    sp = pd.to_numeric(full["fixed_win_price"], errors="coerce")
    sp_fallback = pd.to_numeric(full["starting_price_sp"], errors="coerce")
    full["sp"] = sp.fillna(sp_fallback)
    full = full.dropna(subset=["sp"])
    full = full[full["sp"] > 1.0]
    with open(CACHE_PATH, "wb") as fh:
        pickle.dump((form_mtime, full), fh)
    return full


def is_uncertain_mask(frame):
    gear_changed = frame["gear_changes"].apply(
        lambda v: v is not None and str(v).strip() not in ("", "[]", "None", "nan"))
    return (
        (frame["n_runs"] < 8)
        | (frame["is_small_field"] == 1)
        | gear_changed
        | (frame["own_trend"] > 0)
    )


def raw_base_combined(frame, base_alpha, bump, uncertain):
    alpha = np.where(uncertain, np.minimum(base_alpha + bump, 1.0), base_alpha)
    nett, ewm3 = frame["wpr_nett"], frame["ewm3"]
    both = nett.notna() & ewm3.notna()
    blended = pd.Series(np.where(both, alpha * nett + (1 - alpha) * ewm3, nett.fillna(ewm3)), index=frame.index)
    blended = blended.fillna(frame["avg_last3"]).fillna(frame["career_avg"])
    return blended.apply(wpr._calibrate_base)


def fit_combined(train, allow_bump):
    uncertain = is_uncertain_mask(train)
    best = (0.5, 0.0, float("inf"))
    bumps = BUMP_GRID if allow_bump else [0.0]
    for base_alpha in BASE_ALPHA_GRID:
        for bump in bumps:
            base = raw_base_combined(train, base_alpha, bump, uncertain)
            mae = (train["target"] - base).abs().mean()
            if mae < best[2]:
                best = (base_alpha, bump, mae)
    return best[0], best[1]


def score(test, base_alpha, bump):
    uncertain = is_uncertain_mask(test)
    base = raw_base_combined(test, base_alpha, bump, uncertain)
    return (test["target"] - base).abs().mean()


def run():
    full = build_full()
    print(f"\nScoped rows: {len(full):,}")
    full = full.sort_values("date").reset_index(drop=True)
    fold_edges = np.array_split(np.arange(len(full)), N_FOLDS)
    full["_fold"] = -1
    for i, idx in enumerate(fold_edges):
        full.loc[idx, "_fold"] = i
    print(f"Fold date ranges:")
    for i in range(N_FOLDS):
        fdates = full.loc[full["_fold"] == i, "date"]
        print(f"  fold {i}: {fdates.min().date()} to {fdates.max().date()} (n={len(fdates):,})")

    results = {"shipped": [], "global_only": [], "combined": []}
    print(f"\n{'='*90}\nK={N_FOLDS}-fold chronological validation\n{'='*90}")
    for i in range(N_FOLDS):
        test = full[full["_fold"] == i]
        train = full[full["_fold"] != i]

        mae_shipped = score(test, 0.5, 0.0)

        alpha_only, _ = fit_combined(train, allow_bump=False)
        mae_global = score(test, alpha_only, 0.0)

        base_alpha_c, bump_c = fit_combined(train, allow_bump=True)
        mae_combined = score(test, base_alpha_c, bump_c)

        results["shipped"].append(mae_shipped)
        results["global_only"].append(mae_global)
        results["combined"].append(mae_combined)

        print(f"\n--- fold {i} held out (n={len(test):,}) ---")
        print(f"  shipped (alpha=0.5, no bump):     MAE={mae_shipped:.4f}")
        print(f"  global alpha only (fit={alpha_only}, no bump): MAE={mae_global:.4f}")
        print(f"  combined (fit base_alpha={base_alpha_c}, bump={bump_c}): MAE={mae_combined:.4f}")

    print(f"\n{'='*90}\nAverage across all {N_FOLDS} folds\n{'='*90}")
    print(f"  shipped (0.5):              {np.mean(results['shipped']):.4f}  (std {np.std(results['shipped']):.4f})")
    print(f"  global alpha only:          {np.mean(results['global_only']):.4f}  (std {np.std(results['global_only']):.4f})")
    print(f"  combined (circumstance-aware): {np.mean(results['combined']):.4f}  (std {np.std(results['combined']):.4f})")
    print(f"\n  marginal gain of circumstance layer over global-alpha-only: "
          f"{np.mean(results['global_only']) - np.mean(results['combined']):+.4f} MAE")
    print(f"  (if this is small/inconsistent across folds relative to the shipped->global gain,")
    print(f"   the circumstance layer isn't earning its complexity beyond just raising alpha globally)")

    print("\nSame multiple-comparisons caveat as the other bet-selection scripts: treat any")
    print("row here as a hypothesis for a future walk-forward period, not a result to ship blindly.")


if __name__ == "__main__":
    run()
