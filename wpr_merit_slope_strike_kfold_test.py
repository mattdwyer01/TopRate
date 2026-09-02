"""
wpr_merit_slope_strike_kfold_test.py - re-checks the merit-slope-split
question (does trainer_merit/jockey_merit deserve its own calibration
slope, separate from the shared _CALIB_ADJ_SLOPE=0.1791 the other 8
ADJ_TERMS use) against the RIGHT bar this time.

WHY THIS SUPERSEDES wpr_merit_slope_kfold_test.py's MAE-based verdict
  trainer_merit/jockey_merit were never adopted on MAE in the first
  place - wpr_trainer_jockey_adj_strike_eval.py's own docstring is
  explicit: "MAE got slightly worse in all three variants, the same
  accepted tradeoff track_barrier/closing_merit were adopted under."
  Top-1 strike rate improving in BOTH chronological-split directions was
  the actual adoption bar for this term family. wpr_merit_slope_kfold_
  test.py (after fixing the stale-base cache bug - see that script's own
  build_full() docstring, same fix reused here) found the higher merit
  slope's fit-half preference doesn't reliably improve held-out MAE - but
  that was always the wrong question for this specific term. This script
  asks the right one: does it improve strike rate and Summary-tab-style
  edge/ROI, the metrics that actually justified adopting these two terms
  at all.

METHOD: K=4 chronological folds (same as every other K-fold script this
session). Per fold: fit track_barrier/closing_merit/trainer_merit/
jockey_merit population lookups on the training folds only, fit the
2-group OLS slope split (group A = other 8 terms, group B = trainer+
jockey merit) against target - calibrated_base on the training folds,
then score the held-out fold's top-1 strike rate and Summary-tab-style
edge/ROI (0.05/0.10/0.20, price<=$26) for both the shipped shared-slope
model and the split-slope model, using a price-beta grid search fit on
the training folds' own resulting projection (same convention as
wpr_alpha_08_proper_validation.py/wpr_piecewise_removal_test.py).

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
    fit_bucket_lookup, apply_bucket, top1_strike_rate,
)
from wpr_bet_selection_post_retrain import report

CACHE_PATH = Path("/tmp/wpr_full_training_frame_cache.pkl")
GROUP_A = ["own_distance", "own_going", "own_first_up", "own_second_up",
           "own_trend", "own_long_spell", "track_barrier", "closing_merit"]
GROUP_B = ["trainer_merit", "jockey_merit"]
N_FOLDS = 4
BETA_GRID = [0.05, 0.10, 0.15, 0.20, 0.25, 0.30, 0.40]
PRICE_CAP = 26.0
EDGE_THRESHOLDS = [0.05, 0.10, 0.20]


def build_full():
    """Same stale-"_base"-cache fix as wpr_merit_slope_kfold_test.py - see
    that script's own build_full() docstring for the full explanation
    (cache keyed only on wpr_form_history.csv.gz's mtime, not on
    wpr._BASE_BLEND_ALPHA, so a cache built under an old alpha carries a
    stale "_base" column that must be dropped and recomputed fresh)."""
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


def proj_shipped(frame):
    return frame["_base_calib"] + wpr._CALIB_ADJ_SLOPE * (frame["_group_a_raw"] + frame["_group_b_raw"])


def proj_split(frame, intercept, slope_a, slope_b):
    return frame["_base_calib"] + intercept + slope_a * frame["_group_a_raw"] + slope_b * frame["_group_b_raw"]


def best_beta(train, proj_col):
    best_b, best_brier = 0.15, float("inf")
    for b in BETA_GRID:
        rows = []
        for rid, g in train.groupby("race_id"):
            if len(g) < 4:
                continue
            pv = g[proj_col].to_numpy(dtype=float)
            e = np.exp(b * (pv - pv.max()))
            p = e / e.sum()
            rows.extend(zip(p, g["won"]))
        arr = pd.DataFrame(rows, columns=["p", "won"])
        brier = float(((arr["p"] - arr["won"]) ** 2).mean()) if len(arr) else float("inf")
        if brier < best_brier:
            best_brier, best_b = brier, b
    return best_b


def score_variant(train, test, proj_col_train, proj_col_test):
    b = best_beta(train, proj_col_train)

    def _prob(g):
        pv = g[proj_col_test].to_numpy(dtype=float)
        e = np.exp(b * (pv - pv.max()))
        return pd.Series(e / e.sum(), index=g.index)

    test = test.copy()
    test["model_prob"] = test.groupby("race_id", group_keys=False).apply(_prob)

    def _edge(g):
        p_mkt = (1.0 / g["sp"]) / (1.0 / g["sp"]).sum()
        return g["model_prob"] - p_mkt

    test["edge"] = test.groupby("race_id", group_keys=False).apply(_edge)

    strike, wins, n_top1 = top1_strike_rate(test, proj_col_test)
    return b, strike, wins, n_top1, test


def run():
    full = build_full()
    non_pop_terms = [t for t in wpr.ADJ_TERMS
                     if t not in ("track_barrier", "closing_merit", "trainer_merit", "jockey_merit")]
    full = full.dropna(subset=["target", "_base", "career_avg"] + non_pop_terms +
                        ["barrier", "field_size", "track", "cur_distance",
                         "trainer_win_pct_365d", "jockey_win_pct_90d", "sp"])
    full = full[full["sp"] > 1.0]
    full = full.sort_values("date").reset_index(drop=True)
    print(f"Scoped rows: {len(full):,}")

    fold_edges = np.array_split(np.arange(len(full)), N_FOLDS)
    full["_fold"] = -1
    for i, idx in enumerate(fold_edges):
        full.loc[idx, "_fold"] = i

    print(f"\n{'='*100}\nK={N_FOLDS}-fold: shipped shared slope vs merit-specific slope, "
          f"scored on strike rate + edge/ROI\n{'='*100}")

    shipped_strikes, split_strikes = [], []
    shipped_pooled, split_pooled = [], []
    for i in range(N_FOLDS):
        test = full[full["_fold"] == i].copy()
        train = full[full["_fold"] != i].copy()

        fit_direction(train, [train, test], train["date"].max())
        icpt, sa, sb = fit_ols_two_group(train)

        train["proj_shipped"] = proj_shipped(train)
        test["proj_shipped"] = proj_shipped(test)
        train["proj_split"] = proj_split(train, icpt, sa, sb)
        test["proj_split"] = proj_split(test, icpt, sa, sb)

        b_ship, strike_ship, wins_ship, n_ship, scored_ship = score_variant(
            train, test, "proj_shipped", "proj_shipped")
        b_split, strike_split, wins_split, n_split, scored_split = score_variant(
            train, test, "proj_split", "proj_split")

        shipped_strikes.append(strike_ship)
        split_strikes.append(strike_split)
        shipped_pooled.append(scored_ship)
        split_pooled.append(scored_split)

        print(f"\n--- fold {i} held out (n={len(test):,}) ---")
        print(f"  fit-half slopes: group A = {sa:.4f}, group B (trainer+jockey merit) = {sb:.4f}")
        print(f"  top-1 strike: shipped={wins_ship}/{n_ship}={strike_ship:.2f}%  "
              f"split={wins_split}/{n_split}={strike_split:.2f}%  "
              f"({'better' if strike_split > strike_ship else 'worse/same'})")

    print(f"\n{'='*100}\nSummary across all {N_FOLDS} folds\n{'='*100}")
    print(f"  top-1 strike rate per fold: shipped={[f'{s:.2f}' for s in shipped_strikes]}")
    print(f"  top-1 strike rate per fold: split=  {[f'{s:.2f}' for s in split_strikes]}")
    better_count = sum(sp > sh for sp, sh in zip(split_strikes, shipped_strikes))
    print(f"  split-slope strike rate better in {better_count}/{N_FOLDS} folds")
    print(f"  avg strike rate: shipped={np.mean(shipped_strikes):.2f}%  split={np.mean(split_strikes):.2f}%")

    print(f"\n  Summary-tab-style edge/ROI (pooled across all {N_FOLDS} held-out folds):")
    pooled_ship = pd.concat(shipped_pooled, ignore_index=True)
    pooled_split = pd.concat(split_pooled, ignore_index=True)
    for thr in EDGE_THRESHOLDS:
        print(f"  -- edge >= {thr:.2f} --")
        report(pooled_ship[(pooled_ship["edge"] >= thr) & (pooled_ship["sp"] <= PRICE_CAP)], "shipped shared slope")
        report(pooled_split[(pooled_split["edge"] >= thr) & (pooled_split["sp"] <= PRICE_CAP)], "split merit slope")

    print("\nSame multiple-comparisons caveat as the other bet-selection scripts: treat any")
    print("row here as a hypothesis for a future walk-forward period, not a result to ship blindly.")


if __name__ == "__main__":
    run()
