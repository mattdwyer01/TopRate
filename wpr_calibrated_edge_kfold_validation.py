"""
wpr_calibrated_edge_kfold_validation.py - builds and leak-free validates
a proper probability calibration to replace the arbitrary softmax(beta*
proj) scaling, following wpr_real_model_calibration_diagnosis.py's
finding: the model's raw softmax probabilities are badly miscalibrated
(Brier 0.090 vs the market's 0.081 even at the best single beta, 0.15),
and the edge>=5% "bets" subset is drawn from exactly the most
overconfident part of that miscalibration (Brier 0.155) - which is why
the beta=0.3 strategy loses money by construction, not bad luck.

METHOD: two-stage calibration, K=4 CHRONOLOGICAL fold validation (never
fit and score on the same data):
  1. Raw score: model_prob = softmax(BASE_BETA * proj) per race (BASE_
     BETA=0.15, the Brier-optimal single scale parameter found by the
     diagnosis script - the exact value barely matters here since stage
     2 is a monotonic recalibration, but starting from the best single-
     parameter fit gives isotonic regression less residual work to do).
  2. Isotonic regression (sklearn, fit OUT-OF-FOLD only) mapping that
     raw model_prob -> P(actually won), the standard nonparametric fix
     for exactly the S-shaped miscalibration curve the diagnosis found
     (underconfident mid-range, overconfident at the top). Predicted on
     the held-out fold only.
  3. Renormalise the calibrated probabilities within each race (divide
     by that race's sum) to restore the sum-to-1 property isotonic
     regression breaks (it's fit pointwise, not per-race) - a standard
     practice for multi-class/multi-outcome calibration.
  4. edge = renormalised_calibrated_prob - market_prob, on the SAME
     held-out fold the isotonic curve never saw. Reports the same
     calibration table / Brier score / ROI-by-edge-bucket / ROI-by-
     price-band the diagnosis script ran, pooled across all 4 folds, so
     the before/after comparison is apples to apples.

Caches the projected population (the expensive ~15 min wpr.project_race()
pass) to disk, keyed on wpr_projection.py/wpr_form_history.csv.gz/
toprate_runners.csv mtimes, so re-runs (e.g. re-fitting with a different
BASE_BETA or fold count) are instant.

NO EM DASHES policy: hyphens only in this file.
"""
import pickle
import time
from pathlib import Path

import numpy as np
import pandas as pd
from sklearn.isotonic import IsotonicRegression

from wpr_full_history_current_model_breakdown import (
    RUNNERS_CSV, FORM_CSV, load_form_history, project_date,
)

POOL_CACHE_PATH = Path("/tmp/wpr_projected_pool_with_price_cache.pkl")
BASE_BETA = 0.15
N_FOLDS = 4
EDGE_THRESHOLD = 0.05
PRICE_CAP = 26.0
RETURN_UNITS = 4
N_CALIB_BUCKETS = 10
PRICE_BANDS = [(1.0, 3.0, "favourite <$3"), (3.0, 8.0, "mid $3-8"),
               (8.0, 26.0, "longshot $8-26")]


def build_pool():
    """Cached: race_id/date/state/quality inputs + proj + price + won for
    every runner in an eligible (>=2 priced+projected runners) race,
    across the full resulted history."""
    import wpr_projection as _wpr_mod
    keys = (Path(FORM_CSV).stat().st_mtime, Path(RUNNERS_CSV).stat().st_mtime,
            Path(_wpr_mod.__file__).stat().st_mtime)
    if POOL_CACHE_PATH.exists():
        with open(POOL_CACHE_PATH, "rb") as fh:
            cached_keys, pool = pickle.load(fh)
        if cached_keys == keys:
            print(f"Loaded cached projected pool ({len(pool):,} rows) - skipping the ~15 min projection pass.")
            return pool
        print("Pool cache is stale (a relevant file changed) - rebuilding.")

    print("Reading toprate_runners.csv...")
    runners = pd.read_csv(RUNNERS_CSV, low_memory=False,
                           dtype={"race_id": str, "horse": str, "venue": str, "state": str})
    runners["date"] = pd.to_datetime(runners["date"], errors="coerce")
    runners["resulted"] = pd.to_numeric(runners["resulted"], errors="coerce")
    runners = runners[runners["resulted"] == 1].copy()
    runners = runners.dropna(subset=["date", "race_id"])
    dates = sorted(runners["date"].dt.date.unique())
    print(f"Resulted rows: {len(runners):,} across {len(dates)} dates")

    form_by_horse, trial_by_horse = load_form_history()

    print("\nProjecting every historical day with the real (corrected) project_race()...")
    t0 = time.time()
    proj_col = pd.Series(index=runners.index, dtype=float)
    has_proj_col = pd.Series(False, index=runners.index)
    for di, d in enumerate(dates):
        day_df = runners[runners["date"].dt.date == d]
        result = project_date(day_df, pd.Timestamp(d), form_by_horse, trial_by_horse)
        for idx, r in result.items():
            has_proj_col.at[idx] = r["has_projection"]
            if r["has_projection"]:
                proj_col.at[idx] = r["projected_wpr"]
        if (di + 1) % 20 == 0 or di == len(dates) - 1:
            print(f"  ... {di+1}/{len(dates)} dates ({time.time()-t0:.0f}s elapsed)")

    runners["wprp_proj"] = proj_col
    runners["has_projection"] = has_proj_col
    print(f"Total: {int(has_proj_col.sum()):,} / {len(runners):,} runners projected in {time.time()-t0:.0f}s")

    pool = runners[runners["has_projection"]].copy()
    sp = pd.to_numeric(pool["fixed_win_price"], errors="coerce")
    sp_fallback = pd.to_numeric(pool["starting_price_sp"], errors="coerce")
    pool["price"] = sp.fillna(sp_fallback)
    pool = pool.dropna(subset=["price"])
    pool = pool[pool["price"] > 1.0]
    pool["won"] = pd.to_numeric(pool["won"], errors="coerce").fillna(0).astype(int)
    pool["proj"] = pool["wprp_proj"]
    race_sizes = pool.groupby("race_id")["proj"].transform("size")
    pool = pool[race_sizes >= 2].copy()
    pool = pool.sort_values("date").reset_index(drop=True)

    with open(POOL_CACHE_PATH, "wb") as fh:
        pickle.dump((keys, pool), fh)
    return pool


def raw_model_prob(pool, beta):
    def _probs(g):
        proj = g["proj"].to_numpy(dtype=float)
        e = np.exp(beta * (proj - proj.max()))
        return pd.Series(e / e.sum(), index=g.index)
    return pool.groupby("race_id", group_keys=False).apply(_probs)


def market_prob(pool):
    def _probs(g):
        inv = 1.0 / g["price"].to_numpy(dtype=float)
        return pd.Series(inv / inv.sum(), index=g.index)
    return pool.groupby("race_id", group_keys=False).apply(_probs)


def renormalize(pool, prob_col):
    return pool.groupby("race_id")[prob_col].transform(lambda s: s / s.sum())


def brier(prob, won):
    return float(np.mean((prob - won) ** 2))


def calibration_table(df, prob_col, label):
    print(f"\n  --- calibration: {label} ---")
    d = df.copy()
    d["bucket"] = pd.qcut(d[prob_col], N_CALIB_BUCKETS, duplicates="drop")
    g = d.groupby("bucket", observed=True).agg(
        n=("won", "size"), mean_pred=(prob_col, "mean"), actual_rate=("won", "mean"))
    print(g.to_string(formatters={"mean_pred": "{:.1%}".format, "actual_rate": "{:.1%}".format}))
    print(f"  Brier score ({label}): {brier(d[prob_col], d['won']):.4f}")


def roi_report(df, price_col, edge_col, label):
    if len(df) < 20:
        print(f"  {label}: n={len(df)} (too small)")
        return
    stake = RETURN_UNITS / df[price_col].to_numpy()
    profit = np.where(df["won"] == 1, RETURN_UNITS - stake, -stake)
    staked = stake.sum()
    roi = profit.sum() / staked * 100
    se = profit.std(ddof=1) / np.sqrt(len(profit))
    t = profit.mean() / se if se > 0 else float("nan")
    print(f"  {label:<28} n={len(df):5d}  strike={df['won'].mean()*100:5.1f}%  "
          f"ROI={roi:+7.1f}%  t={t:+.2f}")


def run():
    pool = build_pool()
    print(f"Population: {len(pool):,} runners across {pool['race_id'].nunique():,} races")

    pool["market_prob"] = market_prob(pool)
    pool["raw_model_prob"] = raw_model_prob(pool, BASE_BETA)

    # K=4 chronological folds
    n = len(pool)
    fold_edges = np.array_split(np.arange(n), N_FOLDS)
    pool["_fold"] = -1
    for i, idx in enumerate(fold_edges):
        pool.loc[pool.index[idx], "_fold"] = i

    print(f"\n{'='*100}\nFITTING ISOTONIC CALIBRATION, K={N_FOLDS} CHRONOLOGICAL FOLDS "
          f"(base beta={BASE_BETA})\n{'='*100}")
    calibrated_col = pd.Series(index=pool.index, dtype=float)
    for i in range(N_FOLDS):
        train = pool[pool["_fold"] != i]
        test_mask = pool["_fold"] == i
        iso = IsotonicRegression(out_of_bounds="clip", y_min=1e-6, y_max=1 - 1e-6)
        iso.fit(train["raw_model_prob"], train["won"])
        calibrated_col.loc[test_mask] = iso.predict(pool.loc[test_mask, "raw_model_prob"])
        print(f"  fold {i}: fit on {len(train):,} rows, calibrated {test_mask.sum():,} held-out rows")

    pool["calibrated_prob_raw"] = calibrated_col
    pool["calibrated_prob"] = renormalize(pool, "calibrated_prob_raw")
    pool["edge_calibrated"] = pool["calibrated_prob"] - pool["market_prob"]
    # for direct before/after comparison, also renormalise the raw (uncalibrated) probs
    pool["raw_model_prob_norm"] = renormalize(pool, "raw_model_prob")
    pool["edge_raw"] = pool["raw_model_prob_norm"] - pool["market_prob"]

    print(f"\n{'='*100}\nCALIBRATION: BEFORE (raw softmax, beta={BASE_BETA}) vs AFTER (isotonic, held-out)\n{'='*100}")
    calibration_table(pool, "market_prob", "market (sanity baseline)")
    calibration_table(pool, "raw_model_prob_norm", f"BEFORE: raw softmax beta={BASE_BETA}, whole population")
    calibration_table(pool, "calibrated_prob", "AFTER: isotonic-calibrated, whole population, held-out")

    bets_before = pool[(pool["edge_raw"] >= EDGE_THRESHOLD) & (pool["price"] <= PRICE_CAP)]
    bets_after = pool[(pool["edge_calibrated"] >= EDGE_THRESHOLD) & (pool["price"] <= PRICE_CAP)]
    calibration_table(bets_before, "raw_model_prob_norm", "BEFORE: raw softmax, edge>=5% BETS SUBSET")
    calibration_table(bets_after, "calibrated_prob", "AFTER: isotonic-calibrated, edge>=5% BETS SUBSET")

    print(f"\n{'='*100}\nROI: BEFORE vs AFTER, by edge-magnitude bucket (price<=${PRICE_CAP:.0f})\n{'='*100}")
    edge_bins = [(0.05, 0.10), (0.10, 0.20), (0.20, float("inf"))]
    for lo, hi in edge_bins:
        sub_before = pool[(pool["edge_raw"] >= lo) & (pool["edge_raw"] < hi) & (pool["price"] <= PRICE_CAP)]
        sub_after = pool[(pool["edge_calibrated"] >= lo) & (pool["edge_calibrated"] < hi) & (pool["price"] <= PRICE_CAP)]
        print(f"\n  edge bucket [{lo},{hi if hi != float('inf') else 'inf'}):")
        roi_report(sub_before, "price", "edge_raw", "BEFORE (raw softmax)")
        roi_report(sub_after, "price", "edge_calibrated", "AFTER (isotonic calibrated)")

    print(f"\n{'='*100}\nROI: BEFORE vs AFTER, overall edge>=5%, by price band\n{'='*100}")
    for lo, hi, label in PRICE_BANDS:
        print(f"\n  {label}:")
        roi_report(bets_before[(bets_before["price"] >= lo) & (bets_before["price"] < hi)],
                   "price", "edge_raw", "BEFORE (raw softmax)")
        roi_report(bets_after[(bets_after["price"] >= lo) & (bets_after["price"] < hi)],
                   "price", "edge_calibrated", "AFTER (isotonic calibrated)")

    print(f"\n{'='*100}\nOVERALL: BEFORE vs AFTER, edge>=5%, price<=${PRICE_CAP:.0f}\n{'='*100}")
    roi_report(bets_before, "price", "edge_raw", "BEFORE (raw softmax)")
    roi_report(bets_after, "price", "edge_calibrated", "AFTER (isotonic calibrated)")

    print("\nSame multiple-comparisons caveat as always: one backtest, not a guarantee -")
    print("but this one is a genuine leak-free K-fold test, not a single split.")


if __name__ == "__main__":
    run()
