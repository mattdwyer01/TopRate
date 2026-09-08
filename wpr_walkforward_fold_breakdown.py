"""wpr_walkforward_fold_breakdown.py - per-fold (not pooled) breakdown of
wpr_walkforward_shipped_roi_test.py's SHIPPED-architecture walk-forward
result (user pushback, Sep 2026): the pooled May-Sep result showed
ROI=+20.61%, t=+2.99 at edge>=0.10, but the live overlay tracker's real
Aug9-Sep11 backfill showed -26.4% ROI over that same real period. That is
a direct contradiction, not something to explain away - this script's job
is only to find out which of two things is true:
  (1) the walk-forward test's OWN Aug/Sep fold is ALSO negative, meaning
      the pooled positive result was propped up by earlier months and the
      test is telling the truth - the edge just isn't working right now; or
  (2) walk-forward's Aug/Sep fold disagrees with the live tracker's real
      Aug/Sep result, meaning the backtest simulation and the live daily
      pipeline are silently testing two different things - a bug to find,
      not a result to trust.

Also isolates ONE concrete candidate bug: score_shipped_fold() refits beta
via grid search on each fold's expanding fit_data, but the actually
SHIPPED live system uses a FIXED beta (get_price_beta() = 0.3, carried
forward from config, never auto-re-derived on retrain - see
wpr_projection.get_price_beta()). If walk-forward's fold-chosen beta drifts
from 0.3, walk-forward has been validating a system ("recalibrate beta
every month") that was never actually shipped - a real methodology gap,
separate from whether the edge itself works. This script reports edge>=
0.10 ROI/t under BOTH the fold's own auto-fit beta AND the fixed live
beta=0.3, per fold, so that gap is visible directly instead of assumed.

USAGE
  python wpr_walkforward_fold_breakdown.py

NO EM DASHES policy: hyphens only in this file.
"""
import pandas as pd

import wpr_projection as wpr
from wpr_walkforward_shipped_roi_test import build_frame, score_shipped_fold, report_edge, FOLD_MONTHS, _fit_beta
from wpr_bet_selection_leakfree_eval import _edge_from_score


def run():
    full = build_frame()
    live_beta = wpr.get_price_beta()
    print(f"\nLIVE (actually shipped) fixed beta = {live_beta}")

    for month in FOLD_MONTHS:
        fold_start = pd.Timestamp(month + "-01")
        fold_end = fold_start + pd.offsets.MonthBegin(1)
        fit_data = full[full["date"] < fold_start]
        held_out = full[(full["date"] >= fold_start) & (full["date"] < fold_end)]
        print(f"\n{'#'*70}\nFold {month}: fit={len(fit_data):,} (< {fold_start.date()}), "
              f"held_out={len(held_out):,} races={held_out['race_id'].nunique()}")
        if len(fit_data) < 2000 or len(held_out) < 50:
            print("  skipped (insufficient data)")
            continue

        chosen_beta = _fit_beta(fit_data)
        print(f"  fold-auto-fit beta = {chosen_beta}   (live fixed beta = {live_beta})")

        bets = score_shipped_fold(fit_data, held_out)  # uses fold-auto-fit beta internally
        report_edge(bets, f"Fold {month}: fold-auto-fit beta={chosen_beta}")

        # same held_out wprp_proj, rescored with the FIXED live beta instead
        bets["score_wpr_fixed"] = live_beta * bets["wprp_proj"]
        bets["edge_wpr_fixed"] = _edge_from_score(bets, "score_wpr_fixed")
        bets_fixed = bets.drop(columns=["edge_wpr"]).rename(columns={"edge_wpr_fixed": "edge_wpr"})
        report_edge(bets_fixed, f"Fold {month}: FIXED live beta={live_beta}")


if __name__ == "__main__":
    run()
