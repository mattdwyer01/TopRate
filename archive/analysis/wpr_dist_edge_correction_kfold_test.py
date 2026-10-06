"""
wpr_dist_edge_correction_kfold_test.py - the harder half of the distance
question the user raised early this session ("if it is 1000m and it has
never ran below 1200m... a different method would be needed"). The
hybrid band fallback (own_distance, shipped) only helps horses with a
NEARBY prior run; this targets horses running genuinely OUTSIDE their
ever-proven distance range (dist_edge != 0 - a candidate feature already
computed in build_features() but never used anywhere).

SCOPING FINDING (this session): dist_edge's own documented pattern still
holds on the current model - held-out MAE 5.79 in-range vs 6.31 (1-400m
longer than ever tried), 8.84 (400m+ longer), 6.73 (shorter), 8.92 (much
shorter). More importantly: the residual (target - current projection)
is systematically NEGATIVE across the whole dist_edge!=0 population (the
model over-predicts these runners, not just noisier around zero) - a
real, uncorrected bias, not just added variance. A run_style (settling-
position) interaction showed a directionally sensible but weak pattern
(closers doing relatively better than predicted stepping up, worse
stepping down) - too weak on its own to build on yet; this script tests
the more defensible, simpler question first: does correcting the plain
systematic bias (regardless of running style) help.

METHOD: K=4 chronological folds. Per fold: fit population terms as
always (leak-free), fit a simple dist_edge -> residual correction on the
training folds' dist_edge!=0 rows only (binned mean residual per
dist_edge bucket, shrunk toward 0 by bucket sample size - same _shrink()
convention as every other own-history term), apply it as an ADDITIONAL
correction on top of the existing (unchanged) projection for the held-
out fold's dist_edge!=0 rows. Compares corrected vs uncorrected MAE and
Summary-tab-style edge/ROI on that subset specifically.

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
from wpr_bet_selection_post_retrain import merge_price_pfm, report

CACHE_PATH = Path("/tmp/wpr_full_training_frame_cache.pkl")
N_FOLDS = 4
DIST_EDGE_BINS = [-np.inf, -400, -200, -1, 1, 200, 400, np.inf]
CORRECTION_K = 30.0  # shrinkage strength for the per-bucket correction
BETA_GRID = [0.05, 0.10, 0.15, 0.20, 0.25, 0.30, 0.40]
PRICE_CAP = 26.0
EDGE_THRESHOLDS = [0.05, 0.10, 0.20]


def build_full():
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
    full = merge_price_pfm(full)
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
        f["resid"] = f["target"] - f["proj"]


def fit_dist_edge_correction(train):
    """Bucketed mean residual per dist_edge bin (dist_edge==0 excluded -
    that's the already-well-calibrated population, no correction needed
    there), shrunk toward 0 by bucket sample size - same convention as
    every _shrink()-based own-history term."""
    d = train[train["dist_edge"] != 0]
    bucket = pd.cut(d["dist_edge"], DIST_EDGE_BINS)
    lookup = {}
    for b, g in d.groupby(bucket, observed=True):
        n = len(g)
        if n < 5:
            continue
        m = g["resid"].mean()
        lookup[b] = m * n / (n + CORRECTION_K)
    return lookup


def apply_dist_edge_correction(frame, lookup):
    bucket = pd.cut(frame["dist_edge"], DIST_EDGE_BINS)
    return bucket.map(lookup).fillna(0.0)


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


def score(train, test, proj_col):
    b = best_beta(train, proj_col)

    def _prob(g):
        pv = g[proj_col].to_numpy(dtype=float)
        e = np.exp(b * (pv - pv.max()))
        return pd.Series(e / e.sum(), index=g.index)

    test = test.copy()
    test["model_prob"] = test.groupby("race_id", group_keys=False).apply(_prob)

    def _edge(g):
        p_mkt = (1.0 / g["sp"]) / (1.0 / g["sp"]).sum()
        return g["model_prob"] - p_mkt

    test["edge"] = test.groupby("race_id", group_keys=False).apply(_edge)
    strike, wins, n_top1 = top1_strike_rate(test, proj_col)
    return strike, wins, n_top1, test


def run():
    full = build_full()
    non_pop_terms = [t for t in wpr.ADJ_TERMS
                     if t not in ("track_barrier", "closing_merit", "trainer_merit", "jockey_merit")]
    full = full.dropna(subset=["target", "_base", "career_avg", "dist_edge"] + non_pop_terms +
                        ["barrier", "field_size", "track", "cur_distance",
                         "trainer_win_pct_365d", "jockey_win_pct_90d", "sp"])
    full = full[full["sp"] > 1.0]
    full = full.sort_values("date").reset_index(drop=True)
    print(f"Scoped rows: {len(full):,}")
    print(f"dist_edge != 0 rows: {(full['dist_edge'] != 0).sum():,} "
          f"({(full['dist_edge'] != 0).mean()*100:.1f}%)")

    fold_edges = np.array_split(np.arange(len(full)), N_FOLDS)
    full["_fold"] = -1
    for i, idx in enumerate(fold_edges):
        full.loc[idx, "_fold"] = i

    print(f"\n{'='*100}\nK={N_FOLDS}-fold: dist_edge correction, scored on the dist_edge != 0 subset only\n{'='*100}")

    mae_uncorr_all, mae_corr_all = [], []
    strike_uncorr_all, strike_corr_all = [], []
    pooled_uncorr, pooled_corr = [], []
    for i in range(N_FOLDS):
        test = full[full["_fold"] == i].copy()
        train = full[full["_fold"] != i].copy()
        fit_direction(train, [train, test], train["date"].max())

        lookup = fit_dist_edge_correction(train)
        test_edge = test[test["dist_edge"] != 0].copy()
        train_edge = train[train["dist_edge"] != 0].copy()
        if len(test_edge) < 30:
            print(f"  fold {i}: too few dist_edge!=0 rows ({len(test_edge)}), skipped")
            continue

        test_edge["proj_corr"] = test_edge["proj"] + apply_dist_edge_correction(test_edge, lookup)
        train_edge["proj_corr"] = train_edge["proj"] + apply_dist_edge_correction(train_edge, lookup)

        mae_uncorr = (test_edge["target"] - test_edge["proj"]).abs().mean()
        mae_corr = (test_edge["target"] - test_edge["proj_corr"]).abs().mean()
        mae_uncorr_all.append(mae_uncorr)
        mae_corr_all.append(mae_corr)

        strike_u, wins_u, n_u, scored_u = score(train_edge, test_edge, "proj")
        strike_c, wins_c, n_c, scored_c = score(train_edge, test_edge, "proj_corr")
        strike_uncorr_all.append(strike_u)
        strike_corr_all.append(strike_c)
        pooled_uncorr.append(scored_u)
        pooled_corr.append(scored_c)

        print(f"\n--- fold {i} (dist_edge!=0 n={len(test_edge):,}) ---")
        print(f"  correction buckets fit: { {str(k): round(v, 3) for k, v in lookup.items()} }")
        print(f"  MAE: uncorrected={mae_uncorr:.4f}  corrected={mae_corr:.4f}  "
              f"({'better' if mae_corr < mae_uncorr else 'worse/same'})")
        print(f"  top-1 strike: uncorrected={wins_u}/{n_u}={strike_u:.2f}%  "
              f"corrected={wins_c}/{n_c}={strike_c:.2f}%  "
              f"({'better' if strike_c > strike_u else 'worse/same'})")

    print(f"\n{'='*100}\nSummary\n{'='*100}")
    print(f"  avg MAE: uncorrected={np.mean(mae_uncorr_all):.4f}  corrected={np.mean(mae_corr_all):.4f}")
    print(f"  corrected better on MAE in every fold: "
          f"{all(c < u for c, u in zip(mae_corr_all, mae_uncorr_all))}")
    print(f"  avg top-1 strike: uncorrected={np.mean(strike_uncorr_all):.2f}%  "
          f"corrected={np.mean(strike_corr_all):.2f}%")

    pooled_u = pd.concat(pooled_uncorr, ignore_index=True)
    pooled_c = pd.concat(pooled_corr, ignore_index=True)
    print(f"\n  Summary-tab-style edge/ROI (pooled, dist_edge != 0 subset only):")
    for thr in EDGE_THRESHOLDS:
        report(pooled_u[(pooled_u["edge"] >= thr) & (pooled_u["sp"] <= PRICE_CAP)], f"uncorrected, edge>={thr:.2f}")
        report(pooled_c[(pooled_c["edge"] >= thr) & (pooled_c["sp"] <= PRICE_CAP)], f"corrected,   edge>={thr:.2f}")

    print("\nSame multiple-comparisons caveat as the other bet-selection scripts: treat this")
    print("as a hypothesis for a future walk-forward period, not a result to ship blindly.")


if __name__ == "__main__":
    run()
