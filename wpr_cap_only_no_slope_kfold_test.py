"""
wpr_cap_only_no_slope_kfold_test.py - tests the proposed alternative to
_CALIB_ADJ_SLOPE: instead of a shared slope (0.1791) uniformly shrinking
the whole ADJ_TERMS sum, force slope=1.0 (no shrinkage at all) and rely
purely on _OWN_DELTA_TOTAL_CAP (tightened) to control extremity.

WHY THIS IS A DIFFERENT MECHANISM, NOT AN EQUIVALENT ONE: a cap only
bites the tail - any raw sum already under the cap passes through
completely unchanged. A slope shrinks EVERY row uniformly, including the
~90% of runners whose raw sum never approaches the current cap (6.0) at
all - for those, removing the slope while leaving the cap loose leaves
their adjustment ~5.6x larger than today (1/0.1791). Tightening the cap
enough to compensate has its own problem: _cap_adj_sum's proportional
scaling means once a raw sum exceeds a tight cap, it gets scaled down to
EXACTLY that cap value regardless of how far past it started - two
horses with raw sums of +2 and +5 both land at the same +1.0 ceiling if
the cap is 1.0, destroying the gradient between "mildly deserves an
adjustment" and "strongly deserves one" that a proportional slope
preserves for the whole range.

METHOD: K=4 chronological folds. Per fold: fit population terms as
always (leak-free). For each candidate TOTAL cap C, replace the current
(shipped cap=6.0, slope=0.1791) combination with (cap=C, slope=1.0) -
i.e. wpr._OWN_DELTA_TOTAL_CAP monkeypatched to C for the capping step,
then the capped sum added directly with no further scaling. Compares
held-out MAE, top-1 strike rate, and Summary-tab-style edge/ROI against
the shipped combination, across the FULL population (not just a dist_
edge/first_up subset - this changes every runner's adjustment, not a
targeted correction).

RESULT: confirms the theoretical concern exactly. MAE degrades
monotonically and substantially as the cap loosens (avg MAE 5.8980 at
cap=0.5 -> 6.3271 at cap=6.0, a 7.4% relative degradation at the loosest
cap vs shipped's 5.8919) - the "systematically too extreme" pattern from
the Aug 2026 history, reproduced cleanly once the slope is removed. Even
the TIGHTEST cap tested never quite beats the shipped combination: cap=
0.5 comes close on MAE (5.8980 vs 5.8919) and edges out on aggregate
strike rate (33.01% vs 32.95%), but loses on ROI at every edge threshold
(edge>=0.05: +57.6% vs +60.3%, edge>=0.10: +80.5% vs +82.2%, edge>=0.20:
+98.8% vs +99.1%). No cap value beats the current slope+cap combination -
the best a cap-only approach can do is approximately match it by being
tight enough that it behaves similarly to a slope anyway (crude uniform
shrinkage via wholesale collapse to the cap ceiling). The slope is doing
real, distributed work across the whole population that a cap, by
construction, only ever partially replicates. No production change -
the shipped _CALIB_ADJ_SLOPE/_OWN_DELTA_TOTAL_CAP combination stands.

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
CAP_CANDIDATES = [0.5, 1.0, 1.075, 1.5, 2.0, 3.0, 6.0]
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


def proj_shipped(f):
    adj = wpr._cap_adj_sum(f[wpr.ADJ_TERMS].to_numpy()).sum(axis=1) * wpr._CALIB_ADJ_SLOPE
    return f["_base_calib"] + adj


def proj_cap_only(f, cap):
    original_cap = wpr._OWN_DELTA_TOTAL_CAP
    wpr._OWN_DELTA_TOTAL_CAP = cap
    try:
        adj = wpr._cap_adj_sum(f[wpr.ADJ_TERMS].to_numpy()).sum(axis=1)  # slope=1.0, no scaling
    finally:
        wpr._OWN_DELTA_TOTAL_CAP = original_cap
    return f["_base_calib"] + adj


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
    mae = (test["target"] - test[proj_col]).abs().mean()
    strike, wins, n_top1 = top1_strike_rate(test, proj_col)
    return mae, strike, wins, n_top1, test


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

    print(f"\n{'='*100}\nShipped: cap={wpr._OWN_DELTA_TOTAL_CAP}, slope={wpr._CALIB_ADJ_SLOPE}\n{'='*100}")
    mae_ship, strike_ship = [], []
    pooled_ship = []
    for i in range(N_FOLDS):
        test = full[full["_fold"] == i].copy()
        train = full[full["_fold"] != i].copy()
        fit_direction(train, [train, test], train["date"].max())
        test["proj"] = proj_shipped(test)
        train["proj"] = proj_shipped(train)
        mae, strike, wins, n_top1, scored = score(train, test, "proj")
        mae_ship.append(mae); strike_ship.append(strike); pooled_ship.append(scored)
        print(f"  fold {i}: MAE={mae:.4f}  strike={wins}/{n_top1}={strike:.2f}%")
    print(f"  avg: MAE={np.mean(mae_ship):.4f}  strike={np.mean(strike_ship):.2f}%")

    summary = [("shipped (cap=6.0, slope=0.1791)", np.mean(mae_ship), np.mean(strike_ship))]
    ship_pooled = pd.concat(pooled_ship, ignore_index=True)

    for cap in CAP_CANDIDATES:
        print(f"\n{'='*100}\nCap-only, no slope: total cap={cap}\n{'='*100}")
        mae_c, strike_c = [], []
        pooled_c = []
        for i in range(N_FOLDS):
            test = full[full["_fold"] == i].copy()
            train = full[full["_fold"] != i].copy()
            fit_direction(train, [train, test], train["date"].max())
            test["proj"] = proj_cap_only(test, cap)
            train["proj"] = proj_cap_only(train, cap)
            mae, strike, wins, n_top1, scored = score(train, test, "proj")
            mae_c.append(mae); strike_c.append(strike); pooled_c.append(scored)
            print(f"  fold {i}: MAE={mae:.4f}  strike={wins}/{n_top1}={strike:.2f}%")
        avg_mae, avg_strike = np.mean(mae_c), np.mean(strike_c)
        print(f"  avg: MAE={avg_mae:.4f}  strike={avg_strike:.2f}%")
        summary.append((f"cap={cap}, no slope", avg_mae, avg_strike))

        cap_pooled = pd.concat(pooled_c, ignore_index=True)
        for thr in EDGE_THRESHOLDS:
            report(ship_pooled[(ship_pooled["edge"] >= thr) & (ship_pooled["sp"] <= PRICE_CAP)],
                   f"shipped, edge>={thr:.2f}")
            report(cap_pooled[(cap_pooled["edge"] >= thr) & (cap_pooled["sp"] <= PRICE_CAP)],
                   f"cap={cap}, edge>={thr:.2f}")

    print(f"\n{'='*100}\nSUMMARY\n{'='*100}")
    for label, mae, strike in summary:
        print(f"  {label:<35} avg MAE={mae:.4f}  avg strike={strike:.2f}%")

    print("\nSame multiple-comparisons caveat as the other bet-selection scripts: treat this")
    print("as a hypothesis for a future walk-forward period, not a result to ship blindly.")


if __name__ == "__main__":
    run()
