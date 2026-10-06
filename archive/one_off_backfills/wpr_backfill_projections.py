"""wpr_backfill_projections.py - one-off backfill (Sep 2026): recompute
compute_wpr_projection() for every date currently in toprate_runners.csv's
display window (the same ~30-day window toprate_data.json's RACES payload
uses, plus a couple of already-fetched upcoming days), so the live
dashboard actually reflects today's model fixes:

  - settling_estimate.py: quantile/median objective, sect_margin_to_rest,
    tactical-variance exclusion (see settling_estimate.py's own module
    docstring)
  - wpr_projection.py: the new pace_shape ADJ_TERM (median objective)
  - toprate_daily.py: the dedup fix and scratched-runner exclusion for
    settle_field (see git log around Sep 7 2026)

Normally compute_wpr_projection() only runs for "today's races" during a
full daily fetch, and past/resulted races are NEVER retroactively
recomputed (see its own docstring: "Past runners keep whatever wprp_*
values they already had") - a deliberate, sensible default so a routine
day's run doesn't silently rewrite the historical accuracy record. This
script is the explicit, one-off exception: today's fixes are real,
validated improvements (not a routine daily variation), and the user
asked to backfill everything currently displayed so the dashboard's
predicted-vs-actual accuracy stats and every runner's shown breakdown
reflect them, not a frozen pre-fix snapshot.

Loops one date at a time (mirroring the real daily pipeline's own
per-date scoping exactly - same function, same code path, just called
retroactively many times instead of once going forward) rather than
mutating compute_wpr_projection() itself. Model artifacts (wpr_projection/
settling_estimate/race_speed_estimate) are cached globally after their
first load, so only the per-date form-history CSV read + per-race
compute repeats - not a full model reload each time.
"""
import time
import pandas as pd

import toprate_daily as td

BACKFILL_DAYS_BACK = 30
BACKFILL_DAYS_FORWARD = 3


def run():
    print("Loading runners...")
    runners_df = td.load_runners()
    # Derived, transient date parse for date-selection ONLY - runners_df's
    # own "date" column is left exactly as loaded (whatever string format
    # it's already in) so save_runners() at the end doesn't silently
    # reformat every row's date, not just the ones actually recomputed.
    _parsed_date = pd.to_datetime(runners_df["date"], errors="coerce")
    today = pd.Timestamp.today().normalize()
    lo = today - pd.Timedelta(days=BACKFILL_DAYS_BACK)
    hi = today + pd.Timedelta(days=BACKFILL_DAYS_FORWARD)
    in_window = (_parsed_date >= lo) & (_parsed_date <= hi)
    dates = sorted(_parsed_date[in_window].dt.date.dropna().unique())
    print(f"Backfilling {len(dates)} dates: {dates[0]} .. {dates[-1]} "
          f"({int(in_window.sum()):,} runners)")

    t0 = time.time()
    for i, d in enumerate(dates):
        d_str = d.strftime("%Y-%m-%d")
        print(f"\n--- [{i+1}/{len(dates)}] {d_str} ({time.time()-t0:.0f}s elapsed) ---")
        try:
            runners_df = td.compute_wpr_projection(runners_df, d_str)
        except Exception as e:
            print(f"  ERROR on {d_str}: {e} - leaving this date's rows unchanged")

    print(f"\nSaving {len(runners_df):,} runners back to {td.RUNNERS_CSV}...")
    td.save_runners(runners_df)
    print(f"Done in {time.time()-t0:.0f}s total.")


if __name__ == "__main__":
    run()
