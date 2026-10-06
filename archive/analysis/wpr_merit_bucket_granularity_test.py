"""
wpr_merit_bucket_granularity_test.py - does trainer_merit/jockey_merit's
current 10-bucket (decile) granularity dilute a truly elite/truly poor
trainer or jockey's own effect by lumping them in with merely-good/
merely-poor peers in the same wide bucket?

WHY: wpr_merit_slope_strike_kfold_test.py confirmed the shared 0.1791
calibration slope isn't the problem (giving these terms their own,
bigger slope doesn't help strike rate/ROI at all). But a coarser
question remains unexamined: with only 10 buckets, the top decile
(trainer_win_pct_365d roughly >=17.3, per the shipped edges) contains
everyone from "solidly above average" to "genuinely exceptional" and
averages them into one shrunk residual - if the truly exceptional tail
is rare enough to be a small slice of that top decile, its own more
extreme true effect gets diluted toward the decile's blended average
before the slope is even applied. Finer buckets (more of them, so the
top/bottom slices are narrower) would let a genuinely elite tail show
its own more extreme residual, if one exists.

METHOD: same K=4-fold chronological validation, same track_barrier/
closing_merit/trainer_merit/jockey_merit leak-free per-fold fitting,
same shipped _CALIB_ADJ_SLOPE=0.1791 (holding the slope question
constant - this test is ONLY about bucket count) and shipped
_TJ_MERIT_K=300 shrinkage (already validated as not distinguishable
from noise across a wide K range - see wpr_trainer_jockey_k_sweep_test.py).
Sweeps N_BUCKETS in {10 (shipped), 15, 20, 30}, scores top-1 strike rate
and Summary-tab-style edge/ROI per fold, same adoption bar as every
other trainer/jockey merit test in this series.

NO EM DASHES policy: hyphens only in this file.
"""
import pickle
from pathlib import Path

import numpy as np
import pandas as pd

import wpr_projection as wpr
from wpr_own_pace_backtest import add_base, add_track_barrier, merge_won_by_horse_date
from wpr_trainer_jockey_adj_strike_eval import (
    FORM_CSV, merge_trainer_jockey_by_horse_date, add_closing_merit, top1_strike_rate,
)
from wpr_bet_selection_post_retrain import report

CACHE_PATH = Path("/tmp/wpr_full_training_frame_cache.pkl")
N_FOLDS = 4
BUCKET_GRID = [10, 15, 20, 30]
SHRINK_K = 300.0  # matches shipped _TJ_MERIT_K - not the question this test asks
BETA_GRID = [0.05, 0.10, 0.15, 0.20, 0.25, 0.30, 0.40]
PRICE_CAP = 26.0
EDGE_THRESHOLDS = [0.05, 0.10, 0.20]


def build_full():
    """Same stale-"_base"-cache fix as the other merit-slope scripts this
    session - see wpr_merit_slope_kfold_test.py's build_full() docstring."""
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


def fit_bucket_lookup_n(fit_rows, col, n_buckets):
    d = fit_rows.dropna(subset=[col, "target", "career_avg"])
    edges = np.unique(np.quantile(d[col], np.linspace(0, 1, n_buckets + 1)))
    resid = d["target"] - d["career_avg"]
    global_mean = resid.mean()
    bucket = np.digitize(d[col], edges[1:-1])
    lookup = {}
    for b in range(len(edges) - 1):
        m = resid[bucket == b]
        if len(m):
            n = len(m)
            shrunk = (n * m.mean() + SHRINK_K * global_mean) / (n + SHRINK_K)
            lookup[b] = float(shrunk - global_mean)
        else:
            lookup[b] = 0.0
    return edges, lookup


def apply_bucket(frame, col, edges, lookup, out_col):
    vals = frame[col]
    bucket = np.digitize(vals, edges[1:-1])
    frame[out_col] = [lookup.get(b, 0.0) if v == v else 0.0 for b, v in zip(bucket, vals)]


def fit_direction(fit_half, apply_frames, fit_cutoff, n_buckets):
    add_track_barrier(fit_half, apply_frames)
    add_closing_merit(apply_frames, fit_cutoff)
    edges_t, lookup_t = fit_bucket_lookup_n(fit_half, "trainer_win_pct_365d", n_buckets)
    edges_j, lookup_j = fit_bucket_lookup_n(fit_half, "jockey_win_pct_90d", n_buckets)
    for f in apply_frames:
        apply_bucket(f, "trainer_win_pct_365d", edges_t, lookup_t, "trainer_merit")
        apply_bucket(f, "jockey_win_pct_90d", edges_j, lookup_j, "jockey_merit")
        f["_base_calib"] = f["_base"].apply(wpr._calibrate_base)
        f["adj_total"] = wpr._cap_adj_sum(f[wpr.ADJ_TERMS].to_numpy()).sum(axis=1) * wpr._CALIB_ADJ_SLOPE
        f["proj"] = f["_base_calib"] + f["adj_total"]
    return lookup_t, lookup_j, edges_t, edges_j


def best_beta(train):
    best_b, best_brier = 0.15, float("inf")
    for b in BETA_GRID:
        rows = []
        for rid, g in train.groupby("race_id"):
            if len(g) < 4:
                continue
            pv = g["proj"].to_numpy(dtype=float)
            e = np.exp(b * (pv - pv.max()))
            p = e / e.sum()
            rows.extend(zip(p, g["won"]))
        arr = pd.DataFrame(rows, columns=["p", "won"])
        brier = float(((arr["p"] - arr["won"]) ** 2).mean()) if len(arr) else float("inf")
        if brier < best_brier:
            best_brier, best_b = brier, b
    return best_b


def score_fold(train, test):
    b = best_beta(train)

    def _prob(g):
        pv = g["proj"].to_numpy(dtype=float)
        e = np.exp(b * (pv - pv.max()))
        return pd.Series(e / e.sum(), index=g.index)

    test = test.copy()
    test["model_prob"] = test.groupby("race_id", group_keys=False).apply(_prob)

    def _edge(g):
        p_mkt = (1.0 / g["sp"]) / (1.0 / g["sp"]).sum()
        return g["model_prob"] - p_mkt

    test["edge"] = test.groupby("race_id", group_keys=False).apply(_edge)
    strike, wins, n_top1 = top1_strike_rate(test, "proj")
    return strike, wins, n_top1, test


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

    summary = []
    for n_buckets in BUCKET_GRID:
        print(f"\n{'='*100}\nN_BUCKETS = {n_buckets}\n{'='*100}")
        strikes = []
        pooled_all = []
        top_bucket_residuals = []
        for i in range(N_FOLDS):
            test = full[full["_fold"] == i].copy()
            train = full[full["_fold"] != i].copy()
            lookup_t, lookup_j, edges_t, edges_j = fit_direction(
                train, [train, test], train["date"].max(), n_buckets)
            strike, wins, n_top1, scored = score_fold(train, test)
            strikes.append(strike)
            pooled_all.append(scored)
            top_bucket_residuals.append((max(lookup_t.values()), max(lookup_j.values()),
                                          min(lookup_t.values()), min(lookup_j.values())))
            print(f"  fold {i}: top-1 strike = {wins}/{n_top1} = {strike:.2f}%   "
                  f"extreme bucket residuals: trainer [{min(lookup_t.values()):+.3f}, {max(lookup_t.values()):+.3f}]  "
                  f"jockey [{min(lookup_j.values()):+.3f}, {max(lookup_j.values()):+.3f}]")

        pooled = pd.concat(pooled_all, ignore_index=True)
        avg_strike = np.mean(strikes)
        print(f"\n  avg top-1 strike rate: {avg_strike:.2f}%")
        roi_rows = {}
        for thr in EDGE_THRESHOLDS:
            sub = pooled[(pooled["edge"] >= thr) & (pooled["sp"] <= PRICE_CAP)]
            report(sub, f"edge>={thr:.2f}, price<=${PRICE_CAP:.0f}")
            profit = np.where(sub["won"] == 1, sub["sp"] - 1, -1.0)
            roi_rows[thr] = profit.sum() / len(sub) * 100 if len(sub) else float("nan")
        summary.append((n_buckets, avg_strike, roi_rows))

    print(f"\n{'='*100}\nSUMMARY: bucket count vs avg strike rate / ROI\n{'='*100}")
    for n_buckets, avg_strike, roi_rows in summary:
        roi_str = "  ".join(f"edge>={thr:.2f}: {roi:+.1f}%" for thr, roi in roi_rows.items())
        print(f"  N_BUCKETS={n_buckets:3d}  avg strike={avg_strike:.2f}%   {roi_str}")

    print("\nSame multiple-comparisons caveat as the other bet-selection scripts: treat any")
    print("row here as a hypothesis for a future walk-forward period, not a result to ship blindly.")


if __name__ == "__main__":
    run()
