"""wpr_backfill_edge_scores.py - one-off backfill (Sep 2026): recompute
compute_edge_score() for every date currently in toprate_runners.csv's
display window, mirroring wpr_backfill_projections.py exactly (same window,
same per-date loop, same save_runners() at the end) but for wprp_edge/
wprp_blend_* instead of wprp_proj.

WHY THIS EXISTS
  wpr_backfill_projections.py (run earlier this session, twice, to reflect
  the trained-model/no-slope architecture and then the per-race demeaning
  bug fix) only ever called compute_wpr_projection() per date - it never
  called compute_edge_score(), which needs wprp_proj as an input and was
  therefore left stale: wprp_edge/wprp_blend_prob/wprp_blend_rank/
  wprp_blend_price for every backfilled historical date still reflect
  whatever wprp_proj USED TO BE before each backfill, not the corrected
  value. Confirmed directly: Lindermann's wprp_edge-derived model_prob
  did not match a fresh softmax over its own (corrected) wprp_proj.

  This matters now specifically because the Overlay ROI tracker
  (toprate_daily.compute_overlay_tracker) filters on wprp_edge - a user
  request to "go back and see what bets would have fallen in past days"
  needs wprp_edge to be genuinely computed under TODAY's architecture for
  that whole historical window, not a mix of old-architecture edges.

  compute_edge_score() is cheap per date (a softmax + edge computation
  over already-computed wprp_proj, no per-horse model calls) - much
  faster than the full projection backfill.

USAGE
  python wpr_backfill_edge_scores.py
"""
import time
import pandas as pd

import toprate_daily as td

BACKFILL_DAYS_BACK = 30
BACKFILL_DAYS_FORWARD = 3


def run():
    print("Loading runners...")
    runners_df = td.load_runners()
    _parsed_date = pd.to_datetime(runners_df["date"], errors="coerce")
    today = pd.Timestamp.today().normalize()
    lo = today - pd.Timedelta(days=BACKFILL_DAYS_BACK)
    hi = today + pd.Timedelta(days=BACKFILL_DAYS_FORWARD)
    in_window = (_parsed_date >= lo) & (_parsed_date <= hi)
    dates = sorted(_parsed_date[in_window].dt.date.dropna().unique())
    print(f"Backfilling edge scores for {len(dates)} dates: {dates[0]} .. {dates[-1]} "
          f"({int(in_window.sum()):,} runners)")

    t0 = time.time()
    for i, d in enumerate(dates):
        d_str = d.strftime("%Y-%m-%d")
        print(f"  [{i+1}/{len(dates)}] {d_str} ({time.time()-t0:.0f}s elapsed)", end="\r")
        try:
            runners_df = td.compute_edge_score(runners_df, d_str)
        except Exception as e:
            print(f"\n  ERROR on {d_str}: {e} - leaving this date's rows unchanged")
    print()

    print(f"Saving {len(runners_df):,} runners back to {td.RUNNERS_CSV}...")
    td.save_runners(runners_df)
    print(f"Done in {time.time()-t0:.0f}s total. Earliest backfilled date: {dates[0]}")


if __name__ == "__main__":
    run()
