"""
wpr_merit_slope_split_test.py - is trainer_merit/jockey_merit specifically
under-weighted by the single shared _CALIB_ADJ_SLOPE=0.1791 applied to the
WHOLE ADJ_TERMS sum, or is 0.1791 actually a reasonable weight for these
two terms too?

WHY: the shipped trainer_merit/jockey_merit lookup residuals (target -
career_avg, shrunk toward the population mean with K=300) span roughly
+/-2.0-2.2 raw points - a real, meaningful signal (a top-decile trainer/
jockey genuinely outperforms career average by ~1.6, a bottom-decile one
underperforms by ~2.0-2.2). But _CALIB_ADJ_SLOPE=0.1791 is a SINGLE slope
fit to the SUM of all 10 ADJ_TERMS at once (the 6 per-horse own_* terms,
which are individually noisier and likely double-count the same
underlying "in-form" signal across several correlated terms, PLUS
track_barrier/closing_merit/trainer_merit/jockey_merit, which are
population-level and not obviously correlated with the own_* cluster in
the same way). If the shared slope is mostly compensating for the own_*
cluster's double-counting, trainer_merit/jockey_merit could be
genuinely under-weighted by inheriting the same discount.

METHOD: split ADJ_TERMS into two groups -
  group A: the 8 non-merit terms (6 own_* + track_barrier + closing_merit)
  group B: trainer_merit + jockey_merit
Fit a SEPARATE OLS slope for each group's raw (pre-_CALIB_ADJ_SLOPE) sum
against residual = target - calibrated_base, on a FIT half only (same
leak-free population-term fitting as every other script in this series:
track_barrier/closing_merit/trainer_merit/jockey_merit lookups fit on the
FIT half, applied to both halves). Compares held-out MAE of:
  (a) shipped: both groups scaled by the same 0.1791
  (b) split: each group scaled by its own fit-half-derived slope
in both chronological-split directions, pooled.

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

# 3-way split, to check whether it's specifically trainer/jockey merit that's
# underweighted, or ANY population-level term vs the correlated own-history
# cluster (own_* terms plausibly double-count the same "in-form" signal
# across several terms at once, which the shared slope may be compensating
# for at the expense of the population-level terms generally, not trainer/
# jockey specifically).
GROUP_OWN = ["own_distance", "own_going", "own_first_up", "own_second_up",
             "own_trend", "own_long_spell"]
GROUP_POP_OTHER = ["track_barrier", "closing_merit"]
GROUP_MERIT = ["trainer_merit", "jockey_merit"]


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
    full = add_base(full)
    with open(CACHE_PATH, "wb") as fh:
        pickle.dump((form_mtime, full), fh)
    return full


def fit_direction(fit_half, h1, h2, fit_cutoff):
    """Fits track_barrier/closing_merit/trainer_merit/jockey_merit on
    fit_half, applies to h1 and h2, adds calibrated base and group A/B raw
    sums to both."""
    add_track_barrier(fit_half, [h1, h2])
    add_closing_merit([h1, h2], fit_cutoff)
    edges_t, lookup_t = fit_bucket_lookup(fit_half, "trainer_win_pct_365d")
    edges_j, lookup_j = fit_bucket_lookup(fit_half, "jockey_win_pct_90d")
    for f in (h1, h2):
        apply_bucket(f, "trainer_win_pct_365d", edges_t, lookup_t, "trainer_merit")
        apply_bucket(f, "jockey_win_pct_90d", edges_j, lookup_j, "jockey_merit")
        f["_base_calib"] = f["_base"].apply(wpr._calibrate_base)
        f["_group_a_raw"] = f[GROUP_A].sum(axis=1)
        f["_group_b_raw"] = f[GROUP_B].sum(axis=1)
        f["_resid"] = f["target"] - f["_base_calib"]


def fit_ols_two_group(fit_rows):
    """OLS with intercept: resid ~ group_a_raw + group_b_raw. Returns
    (intercept, slope_a, slope_b)."""
    X = np.column_stack([np.ones(len(fit_rows)), fit_rows["_group_a_raw"], fit_rows["_group_b_raw"]])
    y = fit_rows["_resid"].to_numpy()
    coef, *_ = np.linalg.lstsq(X, y, rcond=None)
    return coef[0], coef[1], coef[2]


def fit_ols_three_group(fit_rows):
    """OLS with intercept: resid ~ own_raw + pop_other_raw + merit_raw.
    Returns (intercept, slope_own, slope_pop_other, slope_merit)."""
    own_raw = fit_rows[GROUP_OWN].sum(axis=1)
    pop_other_raw = fit_rows[GROUP_POP_OTHER].sum(axis=1)
    merit_raw = fit_rows[GROUP_MERIT].sum(axis=1)
    X = np.column_stack([np.ones(len(fit_rows)), own_raw, pop_other_raw, merit_raw])
    y = fit_rows["_resid"].to_numpy()
    coef, *_ = np.linalg.lstsq(X, y, rcond=None)
    return coef[0], coef[1], coef[2], coef[3]


def score(frame, intercept, slope_a, slope_b):
    pred = frame["_base_calib"] + intercept + slope_a * frame["_group_a_raw"] + slope_b * frame["_group_b_raw"]
    return (frame["target"] - pred).abs().mean()


def score_shipped(frame):
    pred = frame["_base_calib"] + wpr._CALIB_ADJ_SLOPE * (frame["_group_a_raw"] + frame["_group_b_raw"])
    return (frame["target"] - pred).abs().mean()


def run():
    full = build_full()
    non_pop_terms = [t for t in wpr.ADJ_TERMS
                     if t not in ("track_barrier", "closing_merit", "trainer_merit", "jockey_merit")]
    full = full.dropna(subset=["target", "_base", "career_avg"] + non_pop_terms +
                        ["barrier", "field_size", "track", "cur_distance",
                         "trainer_win_pct_365d", "jockey_win_pct_90d"])
    print(f"Scoped rows: {len(full):,}")

    mid = full["date"].quantile(0.5)
    h1, h2 = full[full["date"] < mid].copy(), full[full["date"] >= mid].copy()
    print(f"H1: {len(h1):,} rows (< {mid.date()}), H2: {len(h2):,} rows (>= {mid.date()})\n")

    print("=== H1-fit / H2-validate ===")
    h1a, h2a = h1.copy(), h2.copy()
    fit_direction(h1a, h1a, h2a, h1["date"].max())
    icpt1, sa1, sb1 = fit_ols_two_group(h1a)
    print(f"  fit-half slopes: group A (8 non-merit terms) = {sa1:.4f}, "
          f"group B (trainer+jockey merit) = {sb1:.4f}, intercept = {icpt1:.4f}")
    print(f"  shipped shared slope for comparison: {wpr._CALIB_ADJ_SLOPE}")
    mae_shipped_h2 = score_shipped(h2a)
    mae_split_h2 = score(h2a, icpt1, sa1, sb1)
    print(f"  held-out (H2) MAE: shipped shared slope = {mae_shipped_h2:.4f}, "
          f"split slopes = {mae_split_h2:.4f} ({'better' if mae_split_h2 < mae_shipped_h2 else 'worse/same'})")

    print("\n=== H2-fit / H1-validate ===")
    h1b, h2b = h1.copy(), h2.copy()
    fit_direction(h2b, h1b, h2b, h2["date"].max())
    icpt2, sa2, sb2 = fit_ols_two_group(h2b)
    print(f"  fit-half slopes: group A (8 non-merit terms) = {sa2:.4f}, "
          f"group B (trainer+jockey merit) = {sb2:.4f}, intercept = {icpt2:.4f}")
    print(f"  shipped shared slope for comparison: {wpr._CALIB_ADJ_SLOPE}")
    mae_shipped_h1 = score_shipped(h1b)
    mae_split_h1 = score(h1b, icpt2, sa2, sb2)
    print(f"  held-out (H1) MAE: shipped shared slope = {mae_shipped_h1:.4f}, "
          f"split slopes = {mae_split_h1:.4f} ({'better' if mae_split_h1 < mae_shipped_h1 else 'worse/same'})")

    print(f"\n=== Summary (2-way: merit vs everything else) ===")
    print(f"  group B (trainer+jockey merit) fitted slope: {sb1:.4f} (from H1) / {sb2:.4f} (from H2)")
    print(f"  group A (other 8 terms) fitted slope:        {sa1:.4f} (from H1) / {sa2:.4f} (from H2)")
    print(f"  shipped shared slope:                        {wpr._CALIB_ADJ_SLOPE}")
    both_better = mae_split_h2 < mae_shipped_h2 and mae_split_h1 < mae_shipped_h1
    print(f"  split-slope held-out MAE improved in BOTH directions: {both_better}")

    print(f"\n=== 3-way split: own-history cluster vs track_barrier+closing_merit vs trainer+jockey merit ===")
    print("Checks whether it's population-level terms IN GENERAL that are underweighted by the shared")
    print("slope (own-history terms plausibly double-count the same in-form signal across several")
    print("correlated terms at once), or specifically trainer/jockey merit.")
    icpt1_3, sown1, spop1, smerit1 = fit_ols_three_group(h1a)
    icpt2_3, sown2, spop2, smerit2 = fit_ols_three_group(h2b)
    print(f"  H1-fit:  own-history={sown1:.4f}  track_barrier+closing_merit={spop1:.4f}  "
          f"trainer+jockey merit={smerit1:.4f}")
    print(f"  H2-fit:  own-history={sown2:.4f}  track_barrier+closing_merit={spop2:.4f}  "
          f"trainer+jockey merit={smerit2:.4f}")
    if smerit1 > spop1 and smerit2 > spop2:
        print("  trainer/jockey merit's own fitted slope is higher than track_barrier+closing_merit's")
        print("  in both directions too - NOT just 'population-level terms in general', specifically")
        print("  trainer/jockey merit stands out even against the other population-level terms.")
    elif spop1 > sown1 and spop2 > sown2 and smerit1 > sown1 and smerit2 > sown2:
        print("  Both population-level groups (track_barrier+closing_merit AND trainer/jockey merit)")
        print("  fit higher than the own-history cluster in both directions - looks like population-")
        print("  level terms in general are underweighted by the shared slope, not trainer/jockey")
        print("  merit specifically (though merit's own slope may still be the largest of the three).")
    else:
        print("  Pattern is inconsistent across directions for at least one comparison - not fully")
        print("  conclusive at the 3-way split; see the raw numbers above.")

    print("\nSame multiple-comparisons caveat as the other bet-selection scripts: treat any")
    print("row here as a hypothesis for a future walk-forward period, not a result to ship blindly.")


if __name__ == "__main__":
    run()
