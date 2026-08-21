"""One-time backfill: find calendar dates in the last N days that have ZERO
rows in toprate_runners.csv at all, and fetch them before they age out of
TopRate's ~30-day detailed-data window.

WHY
  toprate.au only serves detailed race data (results, form, get_race_detail,
  etc.) for roughly the last 30 days. Any date entirely missing from
  toprate_runners.csv - a day the daily pipeline didn't run, or failed on -
  is gone for good once it falls out of that window. This finds and fetches
  those gaps now while they're still reachable.

  Different problem from backfill_pfm_score.py: that one re-fetches ONE
  field (pfm_score/pfm_score_rank) for races we already have a base record
  of. This script is for days we have NO record of at all - it has to
  re-run the full daily fetch (calendar -> races -> runners -> results ->
  WPR projection etc.) since there's no existing run_id to attach a field
  to. It does this by shelling out to toprate_daily.py --date <date> for
  each missing date, one at a time - reusing the exact same fetch path the
  real daily run uses, rather than a second, less-tested implementation of
  the same logic. Runs sequentially (not parallel) so each date's write to
  toprate_runners.csv completes before the next date reads it.

  --no-html and no --publish are passed to each date's run - HTML/data.json
  regeneration and git push are skipped per-date; do one normal deploy
  after the whole backfill finishes, the same way you'd deploy any other
  day's changes.

UNVERIFIED: whether TopRate's calendar API (get_calendar_upcoming) returns
data for a date in the past at all, despite the name suggesting "upcoming
only". This script finds out empirically on the very first missing date -
if it comes back with 0 new rows, that is a strong signal the date is not
reachable this way, and the run should be stopped rather than ground
through the rest of the window for nothing.

USAGE
  python backfill_missing_days.py              # report only, fetches nothing
  python backfill_missing_days.py --days 45    # different window
  python backfill_missing_days.py --write      # actually run the backfill

SAFE
  - Report-only by default - lists the missing dates and exits.
  - --write invokes the same toprate_daily.py path used every day; no new
    write logic here to get wrong.
  - Each date is independent - if one date fails or is unreachable, the
    rest still run (unless the early-bail check fires - see below).

NO EM DASHES policy: hyphens only in this file.
"""
import argparse
import subprocess
import sys
import time
from datetime import date, timedelta

import pandas as pd

import toprate_daily as td


def find_missing_dates(days):
    df = pd.read_csv(td.RUNNERS_CSV, dtype={"run_id": str, "race_id": str},
                     low_memory=False)
    existing = set(df["date"].astype(str).str[:10].unique())
    today = date.today()
    # Yesterday back through `days` days ago - today is handled by the
    # normal daily run and usually incomplete (races still to jump).
    window = [(today - timedelta(days=i)).isoformat() for i in range(1, days + 1)]
    missing = [d for d in window if d not in existing]
    return sorted(missing), len(window)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--days", type=int, default=30,
                    help="how many days back to check (default 30)")
    ap.add_argument("--write", action="store_true",
                    help="actually fetch the missing dates (default: report only)")
    args = ap.parse_args()

    missing, window_size = find_missing_dates(args.days)
    print(f"Checked the last {window_size} days: {len(missing)} have zero "
          f"rows in {td.RUNNERS_CSV}")
    if not missing:
        print("Nothing to backfill.")
        return
    for d in missing:
        print(f"  missing: {d}")

    if not args.write:
        print("\nReport only - nothing fetched. Re-run with --write to backfill.")
        return

    print(f"\nFetching {len(missing)} missing date(s), one at a time. "
          f"Each is a full daily run (~3-5 min) - this will take a while.")
    t0 = time.time()
    results = []
    for i, d in enumerate(missing, 1):
        before = pd.read_csv(td.RUNNERS_CSV, dtype={"run_id": str},
                             usecols=["run_id", "date"], low_memory=False)
        before_n = (before["date"].astype(str).str[:10] == d).sum()

        print(f"\n{'=' * 70}\n[{i}/{len(missing)}] {d} "
              f"({time.time()-t0:.0f}s elapsed)\n{'=' * 70}")
        proc = subprocess.run(
            [sys.executable, "toprate_daily.py", "--date", d, "--no-html"],
            cwd=str(td.RUNNERS_CSV.parent))

        after = pd.read_csv(td.RUNNERS_CSV, dtype={"run_id": str},
                            usecols=["run_id", "date"], low_memory=False)
        after_n = (after["date"].astype(str).str[:10] == d).sum()
        gained = after_n - before_n
        results.append((d, proc.returncode, gained))
        print(f"  -> {d}: exit code {proc.returncode}, "
              f"{gained} runner rows added")

        # Bail early and loudly if the very first date came back empty -
        # likely means the calendar API does not serve past dates at all,
        # and grinding through the rest of the window would be pointless.
        if i == 1 and gained == 0:
            print("\n  First date returned 0 new rows. This may mean")
            print("  get_calendar_upcoming does not serve past dates, or")
            print("  that date genuinely had no TAB race meetings.")
            print("  Check the output above, then decide whether to")
            print("  continue with the remaining dates or stop here.")

    print(f"\n{'=' * 70}\nSUMMARY ({time.time()-t0:.0f}s total)\n{'=' * 70}")
    for d, code, gained in results:
        flag = "" if code == 0 else "  [non-zero exit code]"
        print(f"  {d}: {gained} rows{flag}")
    total_gained = sum(g for _, _, g in results)
    print(f"\n{total_gained:,} runner rows added across {len(missing)} dates.")
    print("Remember to review + commit/push toprate_runners.csv "
          "(and wpr_form_history.csv.gz if it changed) when you're done.")


if __name__ == "__main__":
    main()
