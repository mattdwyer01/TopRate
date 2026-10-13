#!/usr/bin/env python3
"""
toprate_price_refresh.py

Lightweight in-day price refresh. Re-fetches just `get_race_detail` for races
starting in the next ~LOOKAHEAD_HOURS window, updates `fixed_win_price` in
toprate_runners.csv, snapshots to price history, and rebuilds the HTML.

Designed to run on a frequent schedule (every 5 min via GitHub Actions) so
the dashboard stays current as steaming/drifting happens during the day.

Why this and not full daily run:
- Full toprate_daily.py fetches WPR chart + stats + cache + detail per race.
  That's expensive (~4 API calls per race, 50+ races/day = 200+ calls).
- This script only re-fetches detail. For a typical day with 10 races starting
  in the next 2hr window, that's just 10 API calls. Much faster, much cheaper.
- WPR/stats/ratings don't change during the day so we don't need to refetch.

What gets updated:
- fixed_win_price (in CSV)
- results for any races update_results() finds resolved (also calls
  api_race_results per un-resulted race - see toprate_daily.py). Note:
  api.toprate.au itself doesn't resolve a race's result until its WHOLE
  MEETING has finished, so this doesn't get individual mid-meeting races
  any faster than toprate.au itself has them - it only shortens the gap
  between "toprate.au has the result" and "the dashboard shows it" from
  up to ~9hr (previously only checked at the once-daily run) down to ~5min.
- price history snapshot (in toprate_price_history.csv)
- HTML rebuild (so the dashboard shows fresh prices/results)

What doesn't get updated:
- New races added to schedule (use full daily run for that)
- Anything other than fixed_win_price / results

Usage:
  python toprate_price_refresh.py [--lookahead 2.0] [--dry-run]
"""

import argparse
import sys
from datetime import datetime, timezone, timedelta
from pathlib import Path

import pandas as pd

# Reuse all the auth and API plumbing from toprate_daily
sys.path.insert(0, str(Path(__file__).parent))
import toprate_daily as td


def parse_start_time(s):
    """Parse start_time string to a UTC-aware datetime, or None on failure."""
    if not s or pd.isna(s):
        return None
    try:
        # Handle both ISO with tz and without
        dt = pd.to_datetime(s, errors="coerce")
        if pd.isna(dt):
            return None
        # Localize naive timestamps to UTC (start_time is stored as ISO UTC)
        if dt.tzinfo is None:
            dt = dt.tz_localize("UTC")
        return dt.to_pydatetime()
    except Exception:
        return None


def find_upcoming_races(runners_df, lookahead_hours=2.0):
    """
    Return a list of race_ids that:
    - Are not yet resulted
    - Start in the next N hours (or have already started but in last 30 min)
    - Have at least one runner with a fixed_win_price already

    The "last 30 min" window catches in-progress and just-finished races where
    final prices may still be updating before official results come through.
    """
    if runners_df is None or runners_df.empty:
        return []

    now = datetime.now(timezone.utc)
    cutoff_future = now + timedelta(hours=lookahead_hours)
    cutoff_past = now - timedelta(minutes=30)

    pending = runners_df[runners_df.get("resulted") != 1].copy()
    if pending.empty:
        return []

    # Parse start_time for each race
    race_times = pending.groupby("race_id")["start_time"].first().to_dict()

    upcoming = []
    for race_id, st_str in race_times.items():
        dt = parse_start_time(st_str)
        if dt is None:
            continue
        if cutoff_past <= dt <= cutoff_future:
            upcoming.append(str(race_id))

    return upcoming


def refresh_race_prices(jwt, race_id):
    """
    Re-fetch race detail for one race. Returns (price_updates, scratched_ids):
    price_updates is run_id -> fixed_win_price for still-running runners;
    scratched_ids is the set of run_ids the source now reports isScratched.

    This is the pipeline's only ONGOING scratch check - toprate_daily.py's
    own isScratched filter only ever runs once, at a runner's first capture
    (days before the race, typically). A runner accepted then scratched
    later just kept looking like a normal live runner through every
    subsequent daily fetch until this - refresh_race_prices already
    re-fetches race detail for every upcoming race every 5 min, so it's the
    natural place to catch a late scratch too.

    Returns ({}, set()) on any error so the caller can skip gracefully.
    """
    try:
        detail = td.api_race_detail(jwt, race_id) or []
    except Exception as e:
        print(f"  Race {race_id}: fetch failed ({e})")
        return {}, set()
    price_updates = {}
    scratched_ids = set()
    for d in detail:
        rid = d.get("runId")
        if rid is None:
            continue
        if d.get("isScratched"):
            scratched_ids.add(str(rid))
            continue
        fxp = d.get("fixedWinPrice")
        if fxp is not None:
            try:
                fxp_f = float(fxp)
                if fxp_f > 1:
                    price_updates[str(rid)] = fxp_f
            except (TypeError, ValueError):
                continue
    return price_updates, scratched_ids


def main():
    ap = argparse.ArgumentParser(description="Refresh live prices for upcoming races")
    ap.add_argument("--lookahead", type=float, default=2.0,
                    help="Hours ahead to refresh (default: 2.0)")
    ap.add_argument("--dry-run", action="store_true",
                    help="Print what would update but don't write CSV/HTML")
    ap.add_argument("--no-rebuild", action="store_true",
                    help="Skip HTML rebuild (just update CSV)")
    args = ap.parse_args()

    print(f"=== TopRate price refresh @ {datetime.now(timezone.utc).isoformat()}Z ===")
    print(f"Lookahead window: {args.lookahead}hr from now")

    # Load existing runners CSV
    if not td.RUNNERS_CSV.exists():
        print(f"No runners CSV at {td.RUNNERS_CSV} - run full daily fetch first")
        return 1
    runners_df = pd.read_csv(
        td.RUNNERS_CSV,
        dtype={"run_id": str, "race_id": str},
    )
    print(f"Loaded {len(runners_df)} runners from CSV")
    if "scratched" not in runners_df.columns:
        runners_df["scratched"] = 0

    # Login once, used for both results and price calls below
    jwt = td.login()

    # ── Results ──
    # Results used to come ONLY from the once-daily full run (toprate_daily.py's
    # main(), scheduled slots roughly 9am/9:30/11:30/12/12:30 and an 11pm sweep -
    # see daily.yml) - so a race that finished at, say, 2pm sat unresulted on the
    # dashboard for up to ~9 hours even though nothing else was blocking it.
    # update_results() is already per-race (fetches get_race_results for each
    # un-resulted race individually, gated only on that race's own start_time +
    # 5 min buffer, not on the whole meeting finishing - see toprate_daily.py) so
    # there's no reason it can't run here too. stale_days=2 keeps it cheap: it
    # still catches yesterday's late-settling atw/comments, but skips sweeping
    # every historical never-resulted row (e.g. an old abandoned meeting) on
    # every single 5-minute tick.
    resulted_before = int((runners_df.get("resulted") == 1).sum())
    runners_df = td.update_results(jwt, runners_df, fetch_workers=4, stale_days=2)
    resulted_after = int((runners_df.get("resulted") == 1).sum())
    results_changed = resulted_after > resulted_before
    if results_changed:
        print(f"Results: {resulted_after - resulted_before} newly resulted runners")

    # ── Prices ──
    # Find races to refresh
    upcoming = find_upcoming_races(runners_df, args.lookahead)
    all_updates = {}  # run_id -> new_fxp
    all_scratched = set()
    if not upcoming:
        print("No upcoming races in price-lookahead window")
    else:
        print(f"Refreshing {len(upcoming)} races: {upcoming[:5]}{'...' if len(upcoming) > 5 else ''}")
        for race_id in upcoming:
            updates, scratched_ids = refresh_race_prices(jwt, race_id)
            all_updates.update(updates)
            all_scratched.update(scratched_ids)
        if not all_updates and not all_scratched:
            print("No price updates found")

    # Apply updates to runners_df
    n_changed = 0
    for run_id, new_price in all_updates.items():
        mask = runners_df["run_id"] == run_id
        if not mask.any():
            continue
        old_price = runners_df.loc[mask, "fixed_win_price"].iloc[0]
        if pd.isna(old_price) or abs(float(old_price) - new_price) > 0.001:
            n_changed += 1
        runners_df.loc[mask, "fixed_win_price"] = new_price

    if n_changed or all_updates:
        print(f"Changed {n_changed} prices ({len(all_updates) - n_changed} unchanged)")

    # Apply newly-detected scratchings - the pipeline's only ongoing recheck
    # of isScratched (toprate_daily.py's own check only runs once, at first
    # capture - see refresh_race_prices()'s docstring).
    n_scratched = 0
    if all_scratched:
        already = set(runners_df.loc[runners_df["scratched"].fillna(0).astype(int) == 1, "run_id"])
        newly = all_scratched - already
        if newly:
            mask = runners_df["run_id"].isin(newly)
            runners_df.loc[mask, "scratched"] = 1
            n_scratched = int(mask.sum())
            preview = sorted(newly)[:5]
            print(f"Newly scratched: {n_scratched} runner(s) ({preview}{'...' if len(newly) > 5 else ''})")

    if not results_changed and not n_changed and not n_scratched:
        print("Nothing changed - skipping write/rebuild")
        return 0

    if args.dry_run:
        print("DRY RUN - not writing")
        return 0

    # Write CSV
    runners_df.to_csv(td.RUNNERS_CSV, index=False)
    print(f"Wrote {td.RUNNERS_CSV}")

    # Snapshot prices to history
    td.snapshot_prices(runners_df)

    # Rebuild HTML so the dashboard shows fresh prices
    if not args.no_rebuild:
        try:
            # The Edge/Volume model rule (compute_model_picks) was removed in
            # the WPR-only refactor. The main daily flow now rebuilds with an
            # empty pick list; the dashboard presents WPR rankings and bet
            # selection is manual. Match that here - calling the deleted
            # compute_model_picks would crash the refresh.
            td.rebuild_html(runners_df, model_pick_rows=[])
        except Exception as e:
            print(f"HTML rebuild failed: {e}")
            return 1

    return 0


if __name__ == "__main__":
    sys.exit(main())
