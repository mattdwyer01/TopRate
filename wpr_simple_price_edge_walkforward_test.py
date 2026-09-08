"""wpr_simple_price_edge_walkforward_test.py - test wpr_price alone as the
overlay signal (user request, Sep 2026): "Edge should be as simple as wpr
price lower than sp / fixed price" - compare the model's own fair price
(wpr_price/blend_price, the exact number already shown on the dashboard, a
softmax over the WHOLE scored field) directly against the market's raw
price. Per explicit follow-up instruction, this no longer computes or
reports the old model_prob/market_prob DIFFERENCE ("edge") at all - wpr_
price is now the only overlay signal tested.

WHY THIS IS WORTH TESTING
  A probability-POINT difference is not scale consistent across the price
  range: going from an implied 50% to 60% win chance is a modest price
  move ($2.00 -> $1.67), while going from 5% to 15% implies the market is
  wildly mispricing a longshot ($20 -> $6.67) - a far bigger ask. A PRICE-
  RATIO (market_price / wpr_price - 1, the textbook definition of betting
  edge) does not have this problem: a 20% overlay means the same thing
  whether the fair price is $3 or $10. This is also simply what a user
  visually does when comparing WPR's own displayed price to the market's.

FIXED BETA, NOT AUTO-FIT (follow-up instruction: "test both 0.15 & 0.3")
  The first version of this test auto-refit beta via Brier-minimising
  grid search per fold, which consistently landed on beta=0.15 and
  produced badly negative results at every threshold. That beta was
  chosen to minimise PROBABILITY CALIBRATION error (Brier score), not to
  make wpr_price a useful comparison point - a flatter (lower) beta makes
  blend_price cluster closer to a uniform "1/field_size" reference, which
  degenerates the price-ratio signal into "everything except the
  favourite", the classic favourite-longshot-bias loser. Testing the two
  actual live candidate values (0.15 = this model's own calibrated value,
  0.3 = the deliberately sharper value shipped since Sep 4 2026, see
  wpr_projection.get_price_beta()) directly checks whether a SHARPER,
  more discriminating beta fixes that degeneracy.

Reports, per fold AND pooled, ROI/strike/t-stat for price_edge_pct =
sp/blend_price - 1 at a grid of overlay-percentage thresholds, for BOTH
beta=0.15 and beta=0.3 side by side (same held-out bets, same wprp_proj -
beta only changes the price/edge conversion, never the projection itself).

USAGE
  python wpr_simple_price_edge_walkforward_test.py

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np
import pandas as pd

from wpr_walkforward_shipped_roi_test import build_frame, score_shipped_fold, FOLD_MONTHS

PRICE_EDGE_THRESHOLDS = [0.0, 0.05, 0.10, 0.15, 0.20, 0.30, 0.50, 0.75, 1.00]
BETAS_TO_TEST = [0.15, 0.3]


def blend_price_per_race(df, beta):
    """wpr_price/blend_price: softmax(beta) over wprp_proj across the WHOLE
    field present per race_id in df (matches project_race's own price
    formula and compute_edge_scores' blend_price)."""
    out = np.full(len(df), np.nan)
    proj = df["wprp_proj"].to_numpy(dtype=float)
    for rid, idx in df.groupby("race_id").indices.items():
        idx = np.asarray(idx)
        pv = proj[idx]
        e = np.exp(beta * (pv - pv.max()))
        prob = e / e.sum()
        out[idx] = np.minimum(1.0 / prob, 999.0)
    return out


def roi_stats(sub):
    n = len(sub)
    if n < 20:
        return {"n": n, "strike": None, "roi": None, "t": None}
    profit = np.where(sub["won"] == 1, sub["sp"] - 1, -1.0)
    se = profit.std(ddof=1) / np.sqrt(n)
    t = float(profit.mean() / se) if se > 0 else float("nan")
    return {"n": n, "strike": round(float(sub["won"].mean() * 100), 2),
            "roi": round(float(profit.sum() / n * 100), 2), "t": round(t, 2)}


def print_stats_row(label, stats):
    print(f"  {label:<28} n={stats['n']:>6}  strike={str(stats['strike']):>7}%  "
          f"ROI={str(stats['roi']):>8}%  t={str(stats['t']):>7}")


def run():
    full = build_frame()

    fold_bets = []
    for month in FOLD_MONTHS:
        fold_start = pd.Timestamp(month + "-01")
        fold_end = fold_start + pd.offsets.MonthBegin(1)
        fit_data = full[full["date"] < fold_start]
        held_out = full[(full["date"] >= fold_start) & (full["date"] < fold_end)]
        print(f"\n{'#'*78}\nFold {month}: fit={len(fit_data):,} (< {fold_start.date()}), "
              f"held_out={len(held_out):,} races={held_out['race_id'].nunique()}")
        if len(fit_data) < 2000 or len(held_out) < 50:
            print("  skipped (insufficient data)")
            continue

        # score_shipped_fold's internally-fit beta is irrelevant here - wprp_proj
        # (the projection itself) never depends on beta, only the price/edge
        # conversion downstream of it does, which this script recomputes at
        # FIXED beta values instead of trusting any auto-fit.
        bets = score_shipped_fold(fit_data, held_out)

        for beta in BETAS_TO_TEST:
            bets[f"blend_price_b{beta}"] = blend_price_per_race(bets, beta)
            bets[f"price_edge_pct_b{beta}"] = bets["sp"] / bets[f"blend_price_b{beta}"] - 1.0
            print(f"\n  --- wpr price edge (sp/blend_price - 1), beta={beta} ---")
            for thr in PRICE_EDGE_THRESHOLDS:
                print_stats_row(f"price_edge>={thr:.2f}", roi_stats(bets[bets[f"price_edge_pct_b{beta}"] >= thr]))

        fold_bets.append(bets)

    pooled = pd.concat(fold_bets, ignore_index=True)
    print(f"\n{'='*78}\nPOOLED ACROSS ALL FOLDS ({len(pooled):,} held-out bets)\n{'='*78}")
    for beta in BETAS_TO_TEST:
        print(f"--- wpr price edge (sp/blend_price - 1), beta={beta} ---")
        for thr in PRICE_EDGE_THRESHOLDS:
            print_stats_row(f"price_edge>={thr:.2f}", roi_stats(pooled[pooled[f"price_edge_pct_b{beta}"] >= thr]))


if __name__ == "__main__":
    run()
