"""wpr_simple_price_edge_walkforward_test.py - test a simpler edge
definition (user request, Sep 2026): "Edge should be as simple as wpr
price lower than sp / fixed price" - i.e. compare the model's own fair
price (wpr_price/blend_price, the exact number already shown on the
dashboard, a softmax over the WHOLE scored field) directly against the
market's raw price, instead of the current compute_edge_scores() approach
of computing model_prob/market_prob as separately-renormalised
probabilities over just the priced-and-scored subset and taking their
DIFFERENCE.

WHY THIS IS WORTH TESTING
  A probability-POINT difference (the current "edge") is not scale
  consistent across the price range: going from an implied 50% to 60% win
  chance (edge=0.10) is a modest price move ($2.00 -> $1.67), while going
  from 5% to 15% (also edge=0.10) implies the market is wildly mispricing
  a longshot ($20 -> $6.67) - a far bigger ask. So the SAME edge>=0.10
  threshold demands very different degrees of "the market is wrong"
  depending on where in the price range a runner sits, which can shift
  the composition of flagged bets across time/venues in ways that make a
  fixed probability-difference threshold behave inconsistently. A PRICE-
  RATIO edge (market_price / model_price - 1, i.e. genuine expected-value
  overlay percentage - the textbook definition of betting edge) does not
  have this problem: a 20% overlay means the same thing whether the fair
  price is $3 or $10.

  This is also simply what a user visually does when comparing WPR's own
  displayed price to the market's price - this test ties the edge metric
  to that exact same number (blend_price / wpr_price) rather than a
  separately-computed, differently-normalised probability pair.

ALSO RETESTS BETA (separate ask, same message): rather than trust the
single 70/30-split calibrate_price_beta.py result (which predates this
session's trained-model/no-slope architecture change), this uses the
SAME walk-forward expanding-window discipline as wpr_walkforward_shipped_
roi_test.py - beta is re-selected via Brier-minimising grid search on
each fold's strictly-prior fit data, never carried forward from config.

Reports, per fold AND pooled, ROI/strike/t-stat for:
  (a) the OLD edge (model_prob - market_prob >= 0.10), for direct
      before/after comparison against the exact same held-out bets, and
  (b) the NEW simple price-ratio edge (market_price/blend_price - 1) at a
      grid of overlay-percentage thresholds.

USAGE
  python wpr_simple_price_edge_walkforward_test.py

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np
import pandas as pd

from wpr_walkforward_shipped_roi_test import build_frame, score_shipped_fold, FOLD_MONTHS, _fit_beta
from wpr_bet_selection_leakfree_eval import _edge_from_score

PRICE_EDGE_THRESHOLDS = [0.0, 0.05, 0.10, 0.15, 0.20, 0.30, 0.50, 0.75, 1.00]
PROB_EDGE_THRESHOLD = 0.10  # the OLD metric's threshold, for reference


def blend_price_per_race(df, beta):
    """wpr_price/blend_price: softmax(beta) over wprp_proj across the WHOLE
    field present per race_id in df (matches project_race's own price
    formula and compute_edge_scores' blend_price - not the priced-only
    subset used by the OLD model_prob/market_prob edge)."""
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

        beta = _fit_beta(fit_data)
        print(f"  walk-forward re-fit beta = {beta}")

        bets = score_shipped_fold(fit_data, held_out)  # has wprp_proj, edge_wpr (OLD), sp, won
        bets["blend_price"] = blend_price_per_race(bets, beta)
        bets["price_edge_pct"] = bets["sp"] / bets["blend_price"] - 1.0

        print(f"\n  --- OLD edge (model_prob - market_prob) ---")
        print_stats_row(f"edge>={PROB_EDGE_THRESHOLD:.2f}", roi_stats(bets[bets["edge_wpr"] >= PROB_EDGE_THRESHOLD]))

        print(f"  --- NEW simple price edge (sp/blend_price - 1) ---")
        for thr in PRICE_EDGE_THRESHOLDS:
            print_stats_row(f"price_edge>={thr:.2f}", roi_stats(bets[bets["price_edge_pct"] >= thr]))

        fold_bets.append(bets)

    pooled = pd.concat(fold_bets, ignore_index=True)
    print(f"\n{'='*78}\nPOOLED ACROSS ALL FOLDS ({len(pooled):,} held-out bets)\n{'='*78}")
    print(f"--- OLD edge (model_prob - market_prob) ---")
    print_stats_row(f"edge>={PROB_EDGE_THRESHOLD:.2f}", roi_stats(pooled[pooled["edge_wpr"] >= PROB_EDGE_THRESHOLD]))
    print(f"--- NEW simple price edge (sp/blend_price - 1) ---")
    for thr in PRICE_EDGE_THRESHOLDS:
        print_stats_row(f"price_edge>={thr:.2f}", roi_stats(pooled[pooled["price_edge_pct"] >= thr]))


if __name__ == "__main__":
    run()
