"""fix_backfill_scrape_dates.py - one-time correction for a bug in
backfill_form_history_depth.py's first run.

BUG
  backfill_form_history_depth.py stamped every newly-added row with TODAY's
  date as scrape_date, regardless of when the underlying run happened or
  when the horse's OTHER rows were originally captured. But
  wpr_projection.py's _dedup_scrape_baseline() keeps ONLY each horse's rows
  from its single MOST RECENT scrape_date - wpr is a rebased rating, so
  mixing two different scrape baselines for the same horse would corrupt
  training (see that function's docstring for the full reasoning).

  For every horse the backfill touched, stamping the new rows "today" made
  them look like a newer, separate scrape than the horse's real (older)
  baseline. So _dedup_scrape_baseline kept ONLY the small newly-added set
  and DROPPED all of that horse's properly-captured, already-enriched
  existing rows - the opposite of what the backfill was meant to do. This
  showed up as a much worse held-out MAE after retraining (5.72 vs a prior
  baseline around 5.0-5.1) and a suspiciously large dedup drop (420,389 ->
  174,850 rows) in the retrain log.

FIX
  For every row the backfill added (present in the current file but not in
  the pre-backfill backup), reassign its scrape_date to the SAME
  scrape_date the horse's pre-existing rows already used, so old and
  newly-added rows are treated as one consistent scrape/baseline again.
  backfill_form_history_depth.py itself is already fixed for future runs
  (it now aligns new rows to the horse's existing latest scrape_date
  instead of stamping "today").

USAGE
  python fix_backfill_scrape_dates.py            # dry run, reports counts
  python fix_backfill_scrape_dates.py --write     # actually fix the file

Requires wpr_form_history.csv.gz.pre_depth_backfill (the backup
backfill_form_history_depth.py made before writing) to exist alongside the
current file - it is the only reliable "before" reference for which rows
are new.

NO EM DASHES policy: hyphens only in this file.
"""
import argparse
import shutil

import pandas as pd

import toprate_daily as td


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--write", action="store_true",
                    help="actually update wpr_form_history.csv.gz (default: "
                         "dry run)")
    args = ap.parse_args()

    backup_path = str(td.WPR_FORM_HISTORY_CSV) + ".pre_depth_backfill"
    old = pd.read_csv(backup_path, dtype={"horse_id": str}, low_memory=False)
    cur = pd.read_csv(td.WPR_FORM_HISTORY_CSV, dtype={"horse_id": str},
                      low_memory=False)
    print(f"pre-backfill backup: {len(old):,} rows")
    print(f"current file:        {len(cur):,} rows")

    old_key = set(zip(old["horse_id"].astype(str), old["date"].astype(str).str[:10]))
    # per-horse "true" latest baseline scrape_date, from the pre-backfill data
    old_latest = (old.dropna(subset=["horse_id", "scrape_date"])
                     .groupby(old["horse_id"].astype(str))["scrape_date"].max())

    cur_hid = cur["horse_id"].astype(str)
    cur_date = cur["date"].astype(str).str[:10]
    is_new = [(h, d) not in old_key for h, d in zip(cur_hid, cur_date)]
    n_new = sum(is_new)
    print(f"{n_new:,} rows are new (added by the backfill)")

    fixed = 0
    unmatched = 0
    for idx, new_flag, hid in zip(cur.index, is_new, cur_hid):
        if not new_flag:
            continue
        if hid in old_latest.index:
            cur.at[idx, "scrape_date"] = old_latest.loc[hid]
            fixed += 1
        else:
            unmatched += 1

    print(f"{fixed:,} new rows realigned to their horse's existing baseline "
          f"scrape_date")
    if unmatched:
        print(f"{unmatched:,} new rows left as-is (horse had no pre-existing "
              f"rows in the backup to align to)")

    if not args.write:
        print("\nDRY RUN - nothing written. Re-run with --write to apply.")
        return

    backup2 = str(td.WPR_FORM_HISTORY_CSV) + ".pre_scrapedate_fix"
    shutil.copy(td.WPR_FORM_HISTORY_CSV, backup2)
    print(f"Backed up (pre-fix) current file to {backup2}")
    cur.to_csv(td.WPR_FORM_HISTORY_CSV, index=False)
    print(f"Wrote {td.WPR_FORM_HISTORY_CSV}")


if __name__ == "__main__":
    main()
