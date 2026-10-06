"""
wpr_real_model_calibration_diagnosis.py - digs into WHY the beta=0.3,
edge>=5% strategy loses money under the real model (confirmed: -14.3%
ROI over 2026-04-26 to 2026-09-01, post dist_edge_correction/first_up_
trial_correction removal - see wpr_full_history_current_model_breakdown.py
and wpr_real_correction_revalidation.py's "neither correction" result).

HYPOTHESIS: the softmax edge computation (model_prob = exp(beta*proj)
normalised per race, edge = model_prob - market_prob, beta=0.3 chosen
via the now-discredited reconstruction backtest) may not produce
genuinely CALIBRATED probabilities from projected_wpr - if the model is
systematically OVERCONFIDENT (says 25% when the true rate is 15%), most
"positive edge" bets are fake edges from miscalibration, not real
insight, and the strategy loses by construction regardless of whether
the underlying WPR projection is individually any good at ranking
horses.

METHOD: project the full 2026-04-26 to 2026-09-01 history with
wpr.project_race() (the REAL function, corrections already removed -
see PR #165), computing model_prob for EVERY runner in every eligible
race (not just the edge>=5% subset), then:
  1. Calibration: bucket model_prob into deciles, compare mean predicted
     probability vs actual win rate per bucket - for the WHOLE
     population and separately for just the edge>=5% "bets" subset. Do
     the same for market_prob as a sanity-check baseline (a liquid
     market should be close to perfectly calibrated by construction).
  2. Best-beta-for-calibration: grid-search beta by Brier score (not
     backtest ROI) - is 0.3 even a good probability-calibration choice,
     independent of the ROI question entirely?
  3. ROI by edge-magnitude bucket (5-10%/10-20%/20%+) - does a tighter
     edge threshold find a genuinely profitable slice, even if the
     loose 5% threshold is a net loser?
  4. ROI by price band on the edge>=5% bets - checks for a favourite-
     longshot-bias explanation (the model's "value" picks systematically
     being overpriced longshots that underperform their market odds,
     a well-documented wagering-market effect).

NO EM DASHES policy: hyphens only in this file.
"""
import time

import numpy as np
import pandas as pd

from wpr_full_history_current_model_breakdown import (
    RUNNERS_CSV, load_form_history, project_date,
)

BETA = 0.30
BETA_GRID = [0.05, 0.10, 0.15, 0.20, 0.25, 0.30, 0.35, 0.40, 0.45, 0.50, 0.60, 0.80, 1.00]
EDGE_THRESHOLD = 0.05
PRICE_CAP = 26.0
RETURN_UNITS = 4
N_CALIB_BUCKETS = 10
PRICE_BANDS = [(1.0, 3.0, "favourite <$3"), (3.0, 8.0, "mid $3-8"),
               (8.0, 26.0, "longshot $8-26")]


def per_race_probs(pool, beta):
    def _probs(g):
        proj = g["proj"].to_numpy(dtype=float)
        price = g["price"].to_numpy(dtype=float)
        e = np.exp(beta * (proj - proj.max()))
        model_prob = e / e.sum()
        inv = 1.0 / price
        mkt_prob = inv / inv.sum()
        return pd.DataFrame({"model_prob": model_prob, "market_prob": mkt_prob,
                              "edge": model_prob - mkt_prob}, index=g.index)
    return pool.groupby("race_id", group_keys=False).apply(_probs)


def brier(prob, won):
    return float(np.mean((prob - won) ** 2))


def calibration_table(df, prob_col, label):
    print(f"\n  --- calibration: {label} ---")
    d = df.copy()
    d["bucket"] = pd.qcut(d[prob_col], N_CALIB_BUCKETS, duplicates="drop")
    g = d.groupby("bucket", observed=True).agg(
        n=("won", "size"), mean_pred=(prob_col, "mean"), actual_rate=("won", "mean"))
    print(g.to_string(formatters={
        "mean_pred": "{:.1%}".format, "actual_rate": "{:.1%}".format}))
    print(f"  Brier score ({label}): {brier(d[prob_col], d['won']):.4f}")


def run():
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

    print("\nProjecting every historical day (post correction-removal, corrections gone)...")
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
    # only keep races with >=2 priced/projected runners (same eligibility as the edge calc)
    race_sizes = pool.groupby("race_id")["proj"].transform("size")
    pool = pool[race_sizes >= 2].copy()
    print(f"Population for calibration: {len(pool):,} runners across {pool['race_id'].nunique():,} races")

    probs = per_race_probs(pool, BETA)
    pool = pool.join(probs)

    print(f"\n{'='*100}\nCALIBRATION AT SHIPPED BETA={BETA}\n{'='*100}")
    calibration_table(pool, "market_prob", "market (sanity baseline)")
    calibration_table(pool, "model_prob", "model, WHOLE population")
    bets = pool[(pool["edge"] >= EDGE_THRESHOLD) & (pool["price"] <= PRICE_CAP)]
    calibration_table(bets, "model_prob", "model, edge>=5% BETS SUBSET ONLY")

    print(f"\n{'='*100}\nBEST BETA BY BRIER SCORE (calibration, not backtest ROI)\n{'='*100}")
    print(f"{'beta':>6}  {'brier':>8}")
    best_beta, best_brier = None, float("inf")
    for b in BETA_GRID:
        p = per_race_probs(pool, b)
        bs = brier(p["model_prob"], pool["won"])
        print(f"{b:>6}  {bs:>8.4f}")
        if bs < best_brier:
            best_brier, best_beta = bs, b
    market_brier = brier(pool["market_prob"], pool["won"])
    print(f"  (market_prob brier for reference: {market_brier:.4f})")
    print(f"  best beta by Brier: {best_beta} ({best_brier:.4f}) vs shipped {BETA}")

    print(f"\n{'='*100}\nROI BY EDGE-MAGNITUDE BUCKET (beta={BETA}, price<=${PRICE_CAP:.0f})\n{'='*100}")
    edge_bins = [(0.05, 0.10), (0.10, 0.20), (0.20, float("inf"))]
    for lo, hi in edge_bins:
        sub = pool[(pool["edge"] >= lo) & (pool["edge"] < hi) & (pool["price"] <= PRICE_CAP)]
        if len(sub) < 20:
            print(f"  edge [{lo},{hi}): n={len(sub)} (too small)")
            continue
        stake = RETURN_UNITS / sub["price"].to_numpy()
        profit = np.where(sub["won"] == 1, RETURN_UNITS - stake, -stake)
        staked = stake.sum()
        roi = profit.sum() / staked * 100
        se = profit.std(ddof=1) / np.sqrt(len(profit))
        t = profit.mean() / se
        print(f"  edge [{lo:.2f},{hi if hi != float('inf') else 'inf':}): "
              f"n={len(sub):5d}  strike={sub['won'].mean()*100:5.1f}%  "
              f"ROI={roi:+7.1f}%  t={t:+.2f}")

    print(f"\n{'='*100}\nROI BY PRICE BAND on edge>=5% bets (beta={BETA})\n{'='*100}")
    for lo, hi, label in PRICE_BANDS:
        sub = bets[(bets["price"] >= lo) & (bets["price"] < hi)]
        if len(sub) < 20:
            print(f"  {label}: n={len(sub)} (too small)")
            continue
        stake = RETURN_UNITS / sub["price"].to_numpy()
        profit = np.where(sub["won"] == 1, RETURN_UNITS - stake, -stake)
        staked = stake.sum()
        roi = profit.sum() / staked * 100
        se = profit.std(ddof=1) / np.sqrt(len(profit))
        t = profit.mean() / se
        avg_model_p = sub["model_prob"].mean()
        avg_actual = sub["won"].mean()
        print(f"  {label:<18} n={len(sub):5d}  strike={avg_actual*100:5.1f}%  "
              f"avg_model_prob={avg_model_p*100:5.1f}%  ROI={roi:+7.1f}%  t={t:+.2f}")

    print("\nSame multiple-comparisons caveat as always: one backtest, not a guarantee.")


if __name__ == "__main__":
    run()
