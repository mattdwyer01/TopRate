"""
wpr_joint_calib_kfold_test.py - is the shipped combination of base
calibration (_CALIB_INTERCEPT/_CALIB_BASE_SLOPE, re-fit today for
alpha=0.8) and adjustment calibration (_CALIB_ADJ_SLOPE=0.1791, NOT
re-fit today) still internally consistent?

WHY: the original decomposed calibration ("Serving-time calibration" in
wpr_projection.py's own docstring above ADJ_TERMS) was a JOINT regression:
target = a + b_base*raw_base + b_adj*capped_adj_sum, fit ONE TIME,
together, on whatever base/adjustment definitions were current then. When
alpha was raised to 0.8 today, _CALIB_INTERCEPT/_CALIB_BASE_SLOPE were
re-fit with a SEPARATE single-variable regression (target ~ raw_base
alone), NOT jointly with the adjustment term - _CALIB_ADJ_SLOPE was left
untouched. Checked directly: raw_base and the capped adjustment sum are
correlated at 0.51 (not surprising - a horse in strong recent form tends
to have both a high base AND positive own_trend/closing_merit deltas) -
a real omitted-variable-bias risk for the separate fit, and the joint fit
gives b_adj=0.24 vs the shipped 0.1791 (full-data, in-sample). In-sample
MAE is nearly identical either way (5.8933 vs 5.8961) - the classic
multicollinearity signature where credit shifts between two correlated
regressors without much affecting the overall fit - so which
parameterization is genuinely better must be checked held-out, not
in-sample (same lesson as every other slope question this session).

METHOD: K=4 chronological folds. Per fold: fit track_barrier/closing_merit/
trainer_merit/jockey_merit population lookups on the training folds only
(leak-free, as always), fit the JOINT (a, b_base, b_adj) OLS on the
training folds using the CURRENT alpha=0.8 raw base, score held-out MAE,
market-favourite calibration, top-1 strike rate, and Summary-tab-style
edge/ROI for:
  (a) shipped: separately-fit base calibration (today's alpha=0.8 refit)
      + the untouched _CALIB_ADJ_SLOPE=0.1791
  (b) joint: this fold's own jointly-fit (a, b_base, b_adj)

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
N_FOLDS = 4
BETA_GRID = [0.05, 0.10, 0.15, 0.20, 0.25, 0.30, 0.40]
PRICE_CAP = 26.0
EDGE_THRESHOLDS = [0.05, 0.10, 0.20]


def build_full():
    """Same stale-"_base"-cache fix as every other merit-related script
    this session - see wpr_merit_slope_kfold_test.py's build_full()
    docstring for the full explanation."""
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
        f["adj_capped"] = wpr._cap_adj_sum(f[wpr.ADJ_TERMS].to_numpy()).sum(axis=1)


def fit_shipped_base_calib(train_raw_base, train_target):
    """Replicates exactly what was done to derive today's shipped
    _CALIB_INTERCEPT/_CALIB_BASE_SLOPE - single-variable regression,
    ignoring the adjustment term entirely."""
    slope, intercept = np.polyfit(train_raw_base, train_target, 1)
    return intercept, slope


def fit_joint(train_raw_base, train_adj_capped, train_target):
    X = np.column_stack([np.ones(len(train_target)), train_raw_base, train_adj_capped])
    coef, *_ = np.linalg.lstsq(X, train_target, rcond=None)
    return coef[0], coef[1], coef[2]


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
    top_idx = test.groupby("race_id")[proj_col].idxmax()
    tops = test.loc[top_idx]
    high = tops[tops["model_prob"] >= 0.5]
    fav_actual = high["won"].mean() if len(high) else float("nan")
    fav_implied = high["model_prob"].mean() if len(high) else float("nan")
    strike, wins, n_top1 = top1_strike_rate(test, proj_col)

    return mae, len(high), fav_actual, fav_implied, strike, wins, n_top1, test


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

    print(f"\n{'='*100}\nK={N_FOLDS}-fold: shipped (separate base fit + 0.1791 adj) vs joint decomposed fit\n{'='*100}")

    ship_maes, joint_maes = [], []
    ship_gaps, joint_gaps = [], []
    ship_strikes, joint_strikes = [], []
    ship_pooled, joint_pooled = [], []
    joint_coefs = []
    for i in range(N_FOLDS):
        test = full[full["_fold"] == i].copy()
        train = full[full["_fold"] != i].copy()
        fit_direction(train, [train, test], train["date"].max())

        ship_icpt, ship_slope = fit_shipped_base_calib(train["_base"].to_numpy(), train["target"].to_numpy())
        j_a, j_bbase, j_badj = fit_joint(train["_base"].to_numpy(), train["adj_capped"].to_numpy(),
                                          train["target"].to_numpy())
        joint_coefs.append((j_a, j_bbase, j_badj))

        for f in (train, test):
            f["proj_shipped"] = ship_icpt + ship_slope * f["_base"] + wpr._CALIB_ADJ_SLOPE * f["adj_capped"]
            f["proj_joint"] = j_a + j_bbase * f["_base"] + j_badj * f["adj_capped"]

        mae_s, n_s, fa_s, fi_s, strike_s, wins_s, ntop_s, scored_s = score(train, test, "proj_shipped")
        mae_j, n_j, fa_j, fi_j, strike_j, wins_j, ntop_j, scored_j = score(train, test, "proj_joint")

        ship_maes.append(mae_s); joint_maes.append(mae_j)
        gap_s = (fa_s - fi_s) * 100 if n_s else float("nan")
        gap_j = (fa_j - fi_j) * 100 if n_j else float("nan")
        ship_gaps.append(gap_s); joint_gaps.append(gap_j)
        ship_strikes.append(strike_s); joint_strikes.append(strike_j)
        ship_pooled.append(scored_s); joint_pooled.append(scored_j)

        print(f"\n--- fold {i} held out (n={len(test):,}) ---")
        print(f"  joint fit: a={j_a:.4f}  b_base={j_bbase:.4f}  b_adj={j_badj:.4f}  "
              f"(shipped: base_slope~{ship_slope:.4f}, adj_slope={wpr._CALIB_ADJ_SLOPE})")
        print(f"  MAE: shipped={mae_s:.4f}  joint={mae_j:.4f}  "
              f"({'better' if mae_j < mae_s else 'worse/same'})")
        print(f"  fav-calib gap: shipped={gap_s:+.1f}pp  joint={gap_j:+.1f}pp")
        print(f"  top-1 strike: shipped={wins_s}/{ntop_s}={strike_s:.2f}%  joint={wins_j}/{ntop_j}={strike_j:.2f}%  "
              f"({'better' if strike_j > strike_s else 'worse/same'})")

    print(f"\n{'='*100}\nSummary across all {N_FOLDS} folds\n{'='*100}")
    print(f"  joint b_adj per fold: {[f'{c[2]:.4f}' for c in joint_coefs]}  (shipped: {wpr._CALIB_ADJ_SLOPE})")
    print(f"  joint b_base per fold: {[f'{c[1]:.4f}' for c in joint_coefs]}")
    print(f"  avg MAE: shipped={np.mean(ship_maes):.4f}  joint={np.mean(joint_maes):.4f}")
    print(f"  avg fav-calib gap: shipped={np.nanmean(ship_gaps):+.1f}pp  joint={np.nanmean(joint_gaps):+.1f}pp")
    print(f"  avg top-1 strike: shipped={np.mean(ship_strikes):.2f}%  joint={np.mean(joint_strikes):.2f}%")
    print(f"  joint better on MAE in every fold: {all(j < s for j, s in zip(joint_maes, ship_maes))}")
    print(f"  joint better on strike in every fold: {all(j > s for j, s in zip(joint_strikes, ship_strikes))}")

    pooled_s = pd.concat(ship_pooled, ignore_index=True)
    pooled_j = pd.concat(joint_pooled, ignore_index=True)
    print(f"\n  Summary-tab-style edge/ROI (pooled across all {N_FOLDS} held-out folds):")
    for thr in EDGE_THRESHOLDS:
        report(pooled_s[(pooled_s["edge"] >= thr) & (pooled_s["sp"] <= PRICE_CAP)], f"shipped, edge>={thr:.2f}")
        report(pooled_j[(pooled_j["edge"] >= thr) & (pooled_j["sp"] <= PRICE_CAP)], f"joint,   edge>={thr:.2f}")

    print("\nSame multiple-comparisons caveat as the other bet-selection scripts: treat any")
    print("row here as a hypothesis for a future walk-forward period, not a result to ship blindly.")


if __name__ == "__main__":
    run()
