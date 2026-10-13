"""One-off repair: put back a race day's rows that a bad re-fetch deleted from toprate_runners.csv.

Usage: python restore_dropped_day.py YYYY-MM-DD GOOD_COMMIT

Takes the rows dated DATE from toprate_runners.csv as it was at GOOD_COMMIT and appends the ones whose run_id is missing from the
current file (so it is idempotent and never overwrites a row that is already there). Written 11 Oct 2026 after a manual daily run
removed all 575 pending rows of that day (see fetch_todays_races). Results the poller wrote between GOOD_COMMIT and now for that
day are re-applied by the poller's next cycles (it reads every race of the day from TAB each time); everything else of the day comes back as it was.
"""
import io
import subprocess
import sys

import pandas as pd

import toprate_daily as td


def main():
    date, sha = sys.argv[1], sys.argv[2]
    raw = subprocess.run(["git", "show", f"{sha}:toprate_runners.csv"], capture_output=True, check=True).stdout
    good = pd.read_csv(io.BytesIO(raw), low_memory=False, dtype={"run_id": str, "race_id": str})
    cur = td.load_runners()
    cur_ids = set(cur["run_id"].astype(str))
    day = good[good["date"].astype(str).str[:10] == date]
    add = day[~day["run_id"].astype(str).isin(cur_ids)]
    print(f"{date}: {len(day)} rows at {sha[:8]}, {len(day) - len(add)} already present, restoring {len(add)}")
    if add.empty:
        return
    # keep the column order and dtypes of the current file
    add = add.reindex(columns=cur.columns)
    out = pd.concat([cur, add], ignore_index=True)
    td.save_runners(out)
    print(f"saved: {len(out):,} rows ({len(cur):,} before)")


if __name__ == "__main__":
    main()
