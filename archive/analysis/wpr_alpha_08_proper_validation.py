"""
wpr_alpha_08_proper_validation.py - the properly-done version of "should
we raise _BASE_BLEND_ALPHA to 0.8-0.9", per explicit user request to
revisit the Aug 2026 alpha=0.8 decision (independently rediscovered this
session via wpr_combined_alpha_kfold_test.py's K=4-fold validation).

WHY THIS NEEDS TO BE MORE THOROUGH than the earlier quick tests in this
series: every earlier alpha comparison in this session reused the
SHIPPED piecewise base calibration (_CALIB_LOW_BREAK/_CALIB_HIGH_BREAK/
segment slopes), which was fit assuming alpha=0.5. wpr_projection.py's
own docstring is explicit that this is invalid: "changing the blend
changes the raw base's whole distribution, so the breakpoints/slopes...
are NOT independent of that choice - re-fit both together, never one
without the other." So every prior alpha comparison in this session
under-tested candidates other than 0.5 (their calibration was mismatched
to their own raw-base distribution). This script fixes that: for each
candidate alpha, re-derives its OWN piecewise calibration (p10/p80
breakpoints of that alpha's raw base distribution, then a fresh 3-segment
OLS fit of target ~ raw_base within each segment) on each fold's training
data, exactly replicating the methodology the shipped 0.5/64.25/81.96
constants themselves came from.

ALSO checks downstream effects the base-only MAE tests never did:
market-favourite calibration (does raising alpha help or hurt the
extreme-tail overconfidence found earlier) and Summary-tab-style edge/ROI
at the shipped tier thresholds - not just raw point-accuracy.

METHOD: K=4 chronological folds (same as wpr_combined_alpha_kfold_test.py
- a single 50/50 split understated fold-to-fold instability earlier in
this series). For each fold, each candidate alpha:
  1. Fit track_barrier/closing_merit/trainer_merit/jockey_merit population
     lookups on the training folds only (same leak-free convention as
     every other script in this series).
  2. Fit that alpha's OWN piecewise base calibration on the training
     folds' raw base distribution (see above).
  3. Score the held-out fold: MAE, price-beta grid search (fit on
     training folds' own resulting wprp_proj), market-favourite
     calibration gap, and edge/ROI at the shipped Summary tab thresholds
     (0.05/0.10/0.20, price<=$26).

NO EM DASHES policy: hyphens only in this file.
"""
import pickle
from pathlib import Path

import numpy as np
import pandas as pd

import wpr_projection as wpr
from wpr_own_pace_backtest import add_base, add_track_barrier, merge_won_by_horse_date
from wpr_trainer_jockey_adj_strike_eval import FORM_CSV, merge_trainer_jockey_by_horse_date, \
    add_closing_merit, fit_bucket_lookup, apply_bucket
from wpr_bet_selection_post_retrain import merge_price_pfm, report

CACHE_PATH = Path("/tmp/wpr_full_training_frame_cache.pkl")
ALPHA_CANDIDATES = [0.5, 0.7, 0.8, 0.9, 1.0]
BETA_GRID = [0.05, 0.10, 0.15, 0.20, 0.25, 0.30, 0.40]
N_FOLDS = 4
PRICE_CAP = 26.0
EDGE_THRESHOLDS = [0.05, 0.10, 0.20]


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
    full["used_sp_fallback"] = sp.isna() & sp_fallback.notna()
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
    return blended.fillna(frame["avg_last3"]).fillna(frame["career_avg"])


def fit_piecewise_calibration(train_raw_base, train_target):
    """Replicates the shipped calibration's own derivation exactly:
    p10/p80 breakpoints of the raw base distribution, then a fresh OLS
    fit (intercept, slope) of target ~ raw_base within each of the 3
    resulting segments, all on the TRAINING data only."""
    p10, p80 = np.percentile(train_raw_base, [10, 80])
    segments = {}
    for name, mask in [
        ("low", train_raw_base <= p10),
        ("mid", (train_raw_base > p10) & (train_raw_base <= p80)),
        ("high", train_raw_base > p80),
    ]:
        x, y = train_raw_base[mask], train_target[mask]
        if mask.sum() < 30:
            segments[name] = (0.0, 1.0)
            continue
        slope, intercept = np.polyfit(x, y, 1)
        segments[name] = (intercept, slope)
    return p10, p80, segments


def apply_piecewise_calibration(raw_base, calib):
    p10, p80, segments = calib
    low_i, low_s = segments["low"]
    mid_i, mid_s = segments["mid"]
    high_i, high_s = segments["high"]
    return np.select(
        [raw_base <= p10, raw_base > p80],
        [low_i + low_s * raw_base, high_i + high_s * raw_base],
        default=mid_i + mid_s * raw_base,
    )


def fit_and_score_alpha(train, test, alpha):
    train = train.copy()
    test = test.copy()
    add_track_barrier(train, [train, test])
    add_closing_merit([train, test], train["date"].max())
    edges_t, lookup_t = fit_bucket_lookup(train, "trainer_win_pct_365d")
    edges_j, lookup_j = fit_bucket_lookup(train, "jockey_win_pct_90d")
    apply_bucket(train, "trainer_win_pct_365d", edges_t, lookup_t, "trainer_merit")
    apply_bucket(train, "jockey_win_pct_90d", edges_j, lookup_j, "jockey_merit")
    apply_bucket(test, "trainer_win_pct_365d", edges_t, lookup_t, "trainer_merit")
    apply_bucket(test, "jockey_win_pct_90d", edges_j, lookup_j, "jockey_merit")

    train_raw = raw_base_at_alpha(train, alpha)
    calib = fit_piecewise_calibration(train_raw.to_numpy(), train["target"].to_numpy())
    train["_base_cand"] = apply_piecewise_calibration(train_raw.to_numpy(), calib)
    test_raw = raw_base_at_alpha(test, alpha)
    test["_base_cand"] = apply_piecewise_calibration(test_raw.to_numpy(), calib)

    for f in (train, test):
        f["adj_total"] = wpr._cap_adj_sum(f[wpr.ADJ_TERMS].to_numpy()).sum(axis=1) * wpr._CALIB_ADJ_SLOPE
        f["wprp_proj_cand"] = f["_base_cand"] + f["adj_total"]

    best_beta, best_brier = 0.15, float("inf")
    for b in BETA_GRID:
        rows = []
        for rid, g in train.groupby("race_id"):
            if len(g) < 4:
                continue
            pv = g["wprp_proj_cand"].to_numpy(dtype=float)
            e = np.exp(b * (pv - pv.max()))
            p = e / e.sum()
            rows.extend(zip(p, g["won"]))
        arr = pd.DataFrame(rows, columns=["p", "won"])
        brier = float(((arr["p"] - arr["won"]) ** 2).mean()) if len(arr) else float("inf")
        if brier < best_brier:
            best_brier, best_beta = brier, b

    def _prob(g):
        pv = g["wprp_proj_cand"].to_numpy(dtype=float)
        e = np.exp(best_beta * (pv - pv.max()))
        return pd.Series(e / e.sum(), index=g.index)

    test["model_prob"] = test.groupby("race_id", group_keys=False).apply(_prob)

    def _edge(g):
        p_mkt = (1.0 / g["sp"]) / (1.0 / g["sp"]).sum()
        return g["model_prob"] - p_mkt

    test["edge"] = test.groupby("race_id", group_keys=False).apply(_edge)

    mae = (test["target"] - test["_base_cand"]).abs().mean()
    top_idx = test.groupby("race_id")["wprp_proj_cand"].idxmax()
    tops = test.loc[top_idx]
    high = tops[tops["model_prob"] >= 0.5]
    fav_actual = high["won"].mean() if len(high) else float("nan")
    fav_implied = high["model_prob"].mean() if len(high) else float("nan")

    return test, mae, best_beta, len(high), fav_actual, fav_implied


def run():
    full = build_full()
    print(f"\nScoped rows: {len(full):,}")
    full = full.sort_values("date").reset_index(drop=True)
    fold_edges = np.array_split(np.arange(len(full)), N_FOLDS)
    full["_fold"] = -1
    for i, idx in enumerate(fold_edges):
        full.loc[idx, "_fold"] = i

    for alpha in ALPHA_CANDIDATES:
        print(f"\n{'='*90}\nalpha = {alpha}\n{'='*90}")
        fold_maes, fold_fav_gaps = [], []
        all_test_scored = []
        for i in range(N_FOLDS):
            test = full[full["_fold"] == i]
            train = full[full["_fold"] != i]
            scored, mae, beta, n_fav, fav_actual, fav_implied = fit_and_score_alpha(train, test, alpha)
            fold_maes.append(mae)
            gap = (fav_actual - fav_implied) * 100 if n_fav else float("nan")
            fold_fav_gaps.append(gap)
            all_test_scored.append(scored)
            print(f"  fold {i}: MAE={mae:.4f}  beta={beta}  >=50% group n={n_fav}  "
                  f"implied={fav_implied*100:.1f}% actual={fav_actual*100:.1f}% gap={gap:+.1f}pp")

        pooled = pd.concat(all_test_scored, ignore_index=True)
        print(f"\n  avg MAE across folds: {np.mean(fold_maes):.4f} (std {np.std(fold_maes):.4f})")
        print(f"  avg favourite-calibration gap: {np.nanmean(fold_fav_gaps):+.1f}pp")
        print(f"  Summary-tab-style edge/ROI (pooled across all 4 held-out folds):")
        for thr in EDGE_THRESHOLDS:
            sub = pooled[(pooled["edge"] >= thr) & (pooled["sp"] <= PRICE_CAP)]
            report(sub, f"edge>={thr:.2f}, price<=${PRICE_CAP:.0f}")

    print("\nSame multiple-comparisons caveat as the other bet-selection scripts: treat any")
    print("row here as a hypothesis for a future walk-forward period, not a result to ship blindly.")


if __name__ == "__main__":
    run()
