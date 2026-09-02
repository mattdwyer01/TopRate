"""
wpr_merit_slope_kfold_test.py - K=4-fold chronological re-validation of
wpr_merit_slope_split_test.py's finding (a single 50/50 split, both
directions checked, but not the K=4-fold bar used for the alpha=0.8
decision): does giving trainer_merit/jockey_merit their own calibration
slope (separate from the shared _CALIB_ADJ_SLOPE=0.1791 the other 8
ADJ_TERMS use) hold up across 4 independent chronological folds, not
just one split?

METHOD: same as the alpha K=4-fold validation
(wpr_alpha_08_proper_validation.py, wpr_combined_alpha_kfold_test.py) -
4 chronological folds, each held out once, fit on the other 3 combined.
Per fold: fit track_barrier/closing_merit/trainer_merit/jockey_merit
population lookups on the training folds only (leak-free), fit a 2-group
OLS (group A = the other 8 ADJ_TERMS, group B = trainer_merit +
jockey_merit) against target - calibrated_base on the training folds,
score held-out MAE for both the shipped shared-slope model and the
split-slope model.

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

CACHE_PATH = Path("/tmp/wpr_full_training_frame_cache.pkl")
GROUP_A = ["own_distance", "own_going", "own_first_up", "own_second_up",
           "own_trend", "own_long_spell", "track_barrier", "closing_merit"]
GROUP_B = ["trainer_merit", "jockey_merit"]
N_FOLDS = 4


def build_full():
    """IMPORTANT: the cache is keyed only on wpr_form_history.csv.gz's mtime,
    not on wpr._BASE_BLEND_ALPHA - a cache built while alpha was still 0.50
    (as this one was, early in the session, before the Sep 2026 alpha=0.80
    change) carries a STALE "_base" column computed under the OLD alpha. If
    a later script trusts that cached "_base" as-is while also calling the
    CURRENT (alpha=0.80-fit) _calibrate_base() on it, the mismatch produces
    a large, spurious mean residual (found directly: 0.71 points, entirely
    an artifact of this staleness, not a real calibration bias - confirmed
    by re-deriving "_base" fresh, which drops the mean residual to ~0.007).
    So "_base" is ALWAYS dropped and recomputed fresh below, cache hit or
    not - cheap (a vectorised column op), unlike the ~15-20 min feature
    rebuild the cache actually exists to avoid."""
    form_mtime = Path(FORM_CSV).stat().st_mtime
    if CACHE_PATH.exists():
        with open(CACHE_PATH, "rb") as fh:
            cached_mtime, full = pickle.load(fh)
        if cached_mtime == form_mtime:
            print(f"Loaded cached training frame ({len(full):,} rows) - skipping the ~15-20 min rebuild.")
            full = full.drop(columns=["_base"], errors="ignore")
            return add_base(full)
        print("Cache is stale - rebuilding.")
    print("Rebuilding training frame (full history, this takes a while)...")
    full = wpr.build_training_frame(FORM_CSV, verbose=True, n_jobs=-1)
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
        f["_group_a_raw"] = f[GROUP_A].sum(axis=1)
        f["_group_b_raw"] = f[GROUP_B].sum(axis=1)
        f["_resid"] = f["target"] - f["_base_calib"]


def fit_ols_two_group(fit_rows):
    X = np.column_stack([np.ones(len(fit_rows)), fit_rows["_group_a_raw"], fit_rows["_group_b_raw"]])
    y = fit_rows["_resid"].to_numpy()
    coef, *_ = np.linalg.lstsq(X, y, rcond=None)
    return coef[0], coef[1], coef[2]


def mae_split(frame, intercept, slope_a, slope_b):
    pred = frame["_base_calib"] + intercept + slope_a * frame["_group_a_raw"] + slope_b * frame["_group_b_raw"]
    return (frame["target"] - pred).abs().mean()


def mae_shipped(frame):
    pred = frame["_base_calib"] + wpr._CALIB_ADJ_SLOPE * (frame["_group_a_raw"] + frame["_group_b_raw"])
    return (frame["target"] - pred).abs().mean()


def run():
    full = build_full()
    non_pop_terms = [t for t in wpr.ADJ_TERMS
                     if t not in ("track_barrier", "closing_merit", "trainer_merit", "jockey_merit")]
    full = full.dropna(subset=["target", "_base", "career_avg"] + non_pop_terms +
                        ["barrier", "field_size", "track", "cur_distance",
                         "trainer_win_pct_365d", "jockey_win_pct_90d"])
    full = full.sort_values("date").reset_index(drop=True)
    print(f"Scoped rows: {len(full):,}")

    fold_edges = np.array_split(np.arange(len(full)), N_FOLDS)
    full["_fold"] = -1
    for i, idx in enumerate(fold_edges):
        full.loc[idx, "_fold"] = i
    for i in range(N_FOLDS):
        fdates = full.loc[full["_fold"] == i, "date"]
        print(f"  fold {i}: {fdates.min().date()} to {fdates.max().date()} (n={len(fdates):,})")

    print(f"\n{'='*100}\nK={N_FOLDS}-fold chronological validation: merit-specific slope vs shared slope\n{'='*100}")
    fold_results = []
    for i in range(N_FOLDS):
        test = full[full["_fold"] == i].copy()
        train = full[full["_fold"] != i].copy()

        fit_direction(train, [train, test], train["date"].max())
        icpt, sa, sb = fit_ols_two_group(train)

        m_shipped = mae_shipped(test)
        m_split = mae_split(test, icpt, sa, sb)
        fold_results.append((sa, sb, m_shipped, m_split))
        print(f"\n--- fold {i} held out (n={len(test):,}) ---")
        print(f"  fit-half slopes: group A (other 8 terms) = {sa:.4f}, "
              f"group B (trainer+jockey merit) = {sb:.4f}")
        print(f"  held-out MAE: shipped shared slope (0.1791) = {m_shipped:.4f}, "
              f"split slopes = {m_split:.4f}  "
              f"({'better' if m_split < m_shipped else 'worse/same'})")

    print(f"\n{'='*100}\nSummary across all {N_FOLDS} folds\n{'='*100}")
    sas = [r[0] for r in fold_results]
    sbs = [r[1] for r in fold_results]
    shipped_maes = [r[2] for r in fold_results]
    split_maes = [r[3] for r in fold_results]
    print(f"  group A (other 8 terms) fitted slope per fold: {[f'{s:.4f}' for s in sas]}")
    print(f"  group B (trainer+jockey merit) fitted slope per fold: {[f'{s:.4f}' for s in sbs]}")
    print(f"  shipped shared slope: {wpr._CALIB_ADJ_SLOPE}")
    print(f"  avg held-out MAE: shipped = {np.mean(shipped_maes):.4f} (std {np.std(shipped_maes):.4f}), "
          f"split = {np.mean(split_maes):.4f} (std {np.std(split_maes):.4f})")
    all_folds_better = all(s < h for s, h in zip(split_maes, shipped_maes))
    print(f"  split-slope held-out MAE better in EVERY fold: {all_folds_better}")
    print(f"  group B's fitted slope always > group A's: {all(b > a for a, b in zip(sas, sbs))}")
    print(f"  group B's fitted slope range: {min(sbs):.4f} to {max(sbs):.4f} "
          f"(mean {np.mean(sbs):.4f}) vs shipped {wpr._CALIB_ADJ_SLOPE}")

    print("\nSame multiple-comparisons caveat as the other bet-selection scripts: treat any")
    print("row here as a hypothesis for a future walk-forward period, not a result to ship blindly.")


if __name__ == "__main__":
    run()
