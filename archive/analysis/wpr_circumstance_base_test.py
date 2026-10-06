"""
wpr_circumstance_base_test.py - does the nett/ewm3 blend ratio (alpha)
actually work better if fit SEPARATELY per circumstance, instead of one
global 50/50 for every horse regardless of how much or what kind of
history it has?

WHY (Sep 2026, direct user request): _compute_base() uses a single
formula for every horse - the only thing that varies by circumstance is
which INPUTS are available (a fallback chain on missing data), not the
WEIGHTING given circumstance. This tests four candidate circumstances
where the right blend plausibly differs:

  - first_up: today is this horse's first run back from a >60-day spell
    (_SPELL_GAP_DAYS). ewm3 reflects PRE-spell form, not current fitness -
    plausibly less relevant here than for a horse racing continuously.
  - lightly_raced: n_runs < 8 (still well above the model's own _MIN_RUNS
    floor of 3, but on the thin end) - ewm3 computed from very few runs is
    inherently noisier than one computed from a long history.
  - seasoned: n_runs >= 25 - both nett and ewm3 rest on a long track
    record; plausibly the current 50/50 already works fine here, useful
    as a control group.
  - mid_prep: everyone else (racing continuously, not lightly raced or
    seasoned) - the baseline case the shipped alpha was presumably tuned
    closest to by sheer population weight.

METHOD: for the FIT half, fit alpha SEPARATELY per circumstance bucket -
grid search over ALPHA_GRID, minimising MAE (target vs calibrated base)
WITHIN that bucket's own fit-half rows only - then apply each bucket's
own fitted alpha to the MATCHING circumstance rows in the held-out half.
Reports held-out MAE per circumstance under (a) the single shipped alpha
applied uniformly and (b) each bucket's own leak-free-fit alpha, so the
comparison is apples-to-apples on the exact same held-out rows.

first_up needs one extra column not already in the cached frame
(days_since is present; the flag itself is derived from it here).

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
ALPHA_GRID = [0.0, 0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9, 1.0]
LIGHTLY_RACED_MAX = 7
SEASONED_MIN = 25


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


def assign_circumstance(frame):
    frame = frame.copy()
    is_first_up = frame["first_up"] == 1 if "first_up" in frame.columns else frame["days_since"] > 60
    circumstance = pd.Series("mid_prep", index=frame.index)
    circumstance[frame["n_runs"] < LIGHTLY_RACED_MAX] = "lightly_raced"
    circumstance[frame["n_runs"] >= SEASONED_MIN] = "seasoned"
    circumstance[is_first_up.fillna(False)] = "first_up"  # first-up wins over the n_runs buckets
    frame["circumstance"] = circumstance
    return frame


def raw_base_at_alpha(frame, alpha):
    nett, ewm3 = frame["wpr_nett"], frame["ewm3"]
    both = nett.notna() & ewm3.notna()
    blended = pd.Series(np.where(both, alpha * nett + (1 - alpha) * ewm3, nett.fillna(ewm3)), index=frame.index)
    blended = blended.fillna(frame["avg_last3"]).fillna(frame["career_avg"])
    return blended.apply(wpr._calibrate_base)


def fit_best_alpha(fit_rows):
    """Grid search alpha minimising MAE (target vs calibrated base) on
    this circumstance bucket's own fit-half rows only."""
    best_alpha, best_mae = 0.5, float("inf")
    for alpha in ALPHA_GRID:
        base = raw_base_at_alpha(fit_rows, alpha)
        mae = (fit_rows["target"] - base).abs().mean()
        if mae < best_mae:
            best_mae, best_alpha = mae, alpha
    return best_alpha, best_mae


def run():
    full = assign_circumstance(build_full())
    print(f"\nScoped rows: {len(full):,}")
    print(full["circumstance"].value_counts())

    mid = full["date"].quantile(0.5)
    h1, h2 = full[full["date"] < mid].copy(), full[full["date"] >= mid].copy()

    print(f"\n{'='*90}\nPer-circumstance alpha: leak-free fit-half selection, held-out comparison\n{'='*90}")
    for circ in ["first_up", "lightly_raced", "mid_prep", "seasoned"]:
        h1_circ = h1[h1["circumstance"] == circ]
        h2_circ = h2[h2["circumstance"] == circ]
        if len(h1_circ) < 100 or len(h2_circ) < 100:
            print(f"\n--- {circ}: too few rows to fit reliably (H1={len(h1_circ)}, H2={len(h2_circ)}) ---")
            continue

        alpha_from_h1, _ = fit_best_alpha(h1_circ)
        alpha_from_h2, _ = fit_best_alpha(h2_circ)

        # Score H2's rows (this circumstance) with alpha fit on H1, and vice versa - genuinely held-out.
        base_shipped_h2 = raw_base_at_alpha(h2_circ, 0.5)
        base_fitted_h2 = raw_base_at_alpha(h2_circ, alpha_from_h1)
        base_shipped_h1 = raw_base_at_alpha(h1_circ, 0.5)
        base_fitted_h1 = raw_base_at_alpha(h1_circ, alpha_from_h2)

        mae_shipped = pd.concat([
            (h2_circ["target"] - base_shipped_h2).abs(),
            (h1_circ["target"] - base_shipped_h1).abs(),
        ]).mean()
        mae_fitted = pd.concat([
            (h2_circ["target"] - base_fitted_h2).abs(),
            (h1_circ["target"] - base_fitted_h1).abs(),
        ]).mean()

        print(f"\n--- {circ} (n={len(h1_circ) + len(h2_circ):,}) ---")
        print(f"  leak-free fitted alpha: {alpha_from_h1} (from H1) / {alpha_from_h2} (from H2)")
        print(f"  held-out MAE: shipped alpha=0.5 -> {mae_shipped:.4f}   "
              f"circumstance-fit alpha -> {mae_fitted:.4f}   "
              f"({'better' if mae_fitted < mae_shipped else 'worse or no change'})")

    print("\nSame multiple-comparisons caveat as the other bet-selection scripts: treat any")
    print("row here as a hypothesis for a future walk-forward period, not a result to ship blindly.")


if __name__ == "__main__":
    run()
