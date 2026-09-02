"""
wpr_comprehensive_circumstance_screen.py - broad, systematic screen of
candidate circumstances for whether the nett/ewm3 base blend ratio
(alpha) should differ, instead of one flat 50/50 for every horse.

WHY (Sep 2026, direct user request: "don't just stop at first-up vs
mid-prep vs lightly-raced vs seasoned, look at all possible variables you
can possibly think of"). _compute_base() currently uses a single formula
regardless of circumstance - the earlier 4-bucket test (first_up,
lightly_raced, mid_prep, seasoned) is one instance of a much broader
question. This tests every plausible circumstance variable already
available in the training frame, univariately, as a systematic screen -
not every possible interaction (that's combinatorially unbounded and
would multiply the multiple-comparisons problem far past anything
defensible), but every SINGLE candidate dimension, so real signal isn't
missed just because it wasn't hand-picked in advance.

VARIABLES SCREENED (all pre-race-known, all already in the training
frame - no new feature engineering needed):
  first_up, second_up, camp_run (run number within current prep),
  n_runs (career experience), days_since (gap since last run),
  class_move (today's class vs recent runs), own_trend, career_momentum,
  wpr_traj (recent form direction/momentum), std_last5, std_career,
  consistency_ratio (recent-form volatility - how much to trust a single
  point estimate), recent_vs_peak, pct_of_peak, peak_recency (proximity
  to the horse's own best form), field_size, is_small_field, going_delta
  (going change from recent runs), gear_changes (any change today vs
  none), run_style, pace_dependence.

METHOD: for each variable, bucket the FIT half's rows by it, grid-search
alpha per bucket (minimising MAE of calibrated base vs target, ON THAT
BUCKET'S FIT-HALF ROWS ONLY), then score the MATCHING bucket in the
HELD-OUT half with that leak-free-fit alpha vs the shipped flat 0.5,
pooling both directions. No population-lookup refitting needed here
(only base/alpha is being tested, not the ADJ_TERMS), so this is cheap -
runs directly off the cached frame with plain grid search, no per-half
track_barrier/trainer_merit refits.

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
MIN_BUCKET_N = 300  # per half, per bucket - below this the alpha fit is noise


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


def raw_base_at_alpha(frame, alpha):
    nett, ewm3 = frame["wpr_nett"], frame["ewm3"]
    both = nett.notna() & ewm3.notna()
    blended = pd.Series(np.where(both, alpha * nett + (1 - alpha) * ewm3, nett.fillna(ewm3)), index=frame.index)
    blended = blended.fillna(frame["avg_last3"]).fillna(frame["career_avg"])
    return blended.apply(wpr._calibrate_base)


def fit_best_alpha(fit_rows):
    best_alpha, best_mae = 0.5, float("inf")
    for alpha in ALPHA_GRID:
        mae = (fit_rows["target"] - raw_base_at_alpha(fit_rows, alpha)).abs().mean()
        if mae < best_mae:
            best_mae, best_alpha = mae, alpha
    return best_alpha, best_mae


def screen_variable(name, h1, h2, bucket_fn, global_alpha_h1, global_alpha_h2):
    h1 = h1.copy()
    h2 = h2.copy()
    h1["_bucket"] = bucket_fn(h1)
    h2["_bucket"] = bucket_fn(h2)
    print(f"\n--- {name} ---")
    any_real_gain = False
    for bucket in sorted(set(h1["_bucket"].dropna().unique()) | set(h2["_bucket"].dropna().unique()), key=str):
        h1b = h1[h1["_bucket"] == bucket]
        h2b = h2[h2["_bucket"] == bucket]
        if len(h1b) < MIN_BUCKET_N or len(h2b) < MIN_BUCKET_N:
            continue
        alpha_from_h1, _ = fit_best_alpha(h1b)
        alpha_from_h2, _ = fit_best_alpha(h2b)

        # Benchmark against the GLOBAL leak-free-fit alpha (already ~1.0,
        # per Test A - ewm3 hurts MAE across the WHOLE population, not just
        # specific circumstances), not the shipped 0.5 - comparing against
        # 0.5 would just have every bucket "discover" the same global
        # effect independently, which isn't circumstance-specific signal.
        mae_global = pd.concat([
            (h2b["target"] - raw_base_at_alpha(h2b, global_alpha_h1)).abs(),
            (h1b["target"] - raw_base_at_alpha(h1b, global_alpha_h2)).abs(),
        ]).mean()
        mae_fitted = pd.concat([
            (h2b["target"] - raw_base_at_alpha(h2b, alpha_from_h1)).abs(),
            (h1b["target"] - raw_base_at_alpha(h1b, alpha_from_h2)).abs(),
        ]).mean()
        gain = mae_global - mae_fitted
        flag = "  <-- candidate" if gain > 0.05 else ""
        if gain > 0.05:
            any_real_gain = True
        print(f"    {bucket!s:>18}: n={len(h1b)+len(h2b):6,d}  fit alpha={alpha_from_h1}/{alpha_from_h2}  "
              f"(global={global_alpha_h1}/{global_alpha_h2})  "
              f"MAE@global={mae_global:.4f} MAE@bucket-fit={mae_fitted:.4f} gain={gain:+.4f}{flag}")
    if not any_real_gain:
        print("    (no bucket differs meaningfully from the global optimal alpha)")


def run():
    full = build_full()
    print(f"\nScoped rows: {len(full):,}")
    mid = full["date"].quantile(0.5)
    h1, h2 = full[full["date"] < mid].copy(), full[full["date"] >= mid].copy()

    global_alpha_h1, _ = fit_best_alpha(h1)
    global_alpha_h2, _ = fit_best_alpha(h2)
    print(f"\nGlobal leak-free-fit alpha (whole population, no circumstance split): "
          f"{global_alpha_h1} (from H1) / {global_alpha_h2} (from H2)")
    print("Every bucket below is benchmarked against THIS, not the shipped 0.5 - otherwise every")
    print("bucket just independently rediscovers this same global effect, which isn't circumstance-specific.")

    def screen(name, bucket_fn):
        screen_variable(name, h1, h2, bucket_fn, global_alpha_h1, global_alpha_h2)

    print(f"\n{'='*90}\nComprehensive circumstance screen: per-bucket leak-free alpha vs the GLOBAL fit\n{'='*90}")

    screen("first_up (0=no, 1=yes)", lambda f: f["first_up"])
    screen("second_up (0=no, 1=yes)", lambda f: f["second_up"])
    screen("camp_run (run number this prep)",
                     lambda f: pd.cut(f["camp_run"], [0, 1, 2, 3, 4, 100], labels=["1", "2", "3", "4", "5+"]))
    screen("n_runs (career experience)",
                     lambda f: pd.cut(f["n_runs"], [0, 5, 7, 10, 15, 25, 1000],
                                       labels=["3-5", "6-7", "8-10", "11-15", "16-25", "26+"]))
    screen("days_since (gap since last run)",
                     lambda f: pd.cut(f["days_since"], [0, 14, 21, 35, 60, 90, 100000],
                                       labels=["<=14", "15-21", "22-35", "36-60", "61-90", "91+"]))
    screen("class_move (today's class vs recent)",
                     lambda f: pd.cut(f["class_move"], [-1000, -8, -2, 2, 8, 1000],
                                       labels=["big drop", "slight drop", "neutral", "slight rise", "big rise"]))
    screen("own_trend (last run vs prior 2)",
                     lambda f: pd.qcut(f["own_trend"], 4, duplicates="drop"))
    screen("career_momentum",
                     lambda f: pd.qcut(f["career_momentum"], 4, duplicates="drop"))
    screen("wpr_traj (trajectory)",
                     lambda f: pd.qcut(f["wpr_traj"], 4, duplicates="drop"))
    screen("std_last5 (recent-form volatility)",
                     lambda f: pd.qcut(f["std_last5"], 4, duplicates="drop"))
    screen("std_career (career volatility)",
                     lambda f: pd.qcut(f["std_career"], 4, duplicates="drop"))
    screen("consistency_ratio",
                     lambda f: pd.qcut(f["consistency_ratio"], 4, duplicates="drop"))
    screen("recent_vs_peak (below own best)",
                     lambda f: pd.qcut(f["recent_vs_peak"], 4, duplicates="drop"))
    screen("pct_of_peak",
                     lambda f: pd.qcut(f["pct_of_peak"], 4, duplicates="drop"))
    screen("peak_recency (runs since peak)",
                     lambda f: pd.qcut(f["peak_recency"], 4, duplicates="drop"))
    screen("field_size",
                     lambda f: pd.cut(f["field_size"], [0, 6, 8, 10, 12, 100],
                                       labels=["<=6", "7-8", "9-10", "11-12", "13+"]))
    screen("is_small_field (0=no, 1=yes)", lambda f: f["is_small_field"])
    screen("going_delta (going change)",
                     lambda f: pd.qcut(f["going_delta"], 4, duplicates="drop"))
    screen("gear_changes (any change today)",
                     lambda f: f["gear_changes"].apply(lambda v: "none" if (v is None or str(v).strip() in ("", "[]", "None", "nan")) else "changed"))
    screen("run_style",
                     lambda f: pd.qcut(f["run_style"], 4, duplicates="drop"))
    screen("pace_dependence",
                     lambda f: pd.qcut(f["pace_dependence"], 4, duplicates="drop"))

    print("\nSame multiple-comparisons caveat as the other bet-selection scripts, more so here given")
    print("~20 variables screened at once: treat any '<-- candidate' flag as a hypothesis worth a")
    print("dedicated, focused leak-free test on its own - not a result to ship directly from this screen.")


if __name__ == "__main__":
    run()
