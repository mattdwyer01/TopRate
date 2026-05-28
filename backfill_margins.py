"""
One-Time Backfill - margin_finish on existing resulted races
=============================================================
The runners CSV did not previously capture marginFinish from the
results feed. The form history (wpr_form_history.csv) carries
marginFinish for every horse-run, keyed by run_id - so we can
backfill the runners CSV's new margin_finish column from there.

Run ONCE after deploying the updated toprate_daily.py:
    python backfill_margins.py

The daily script handles new races from here on; this is just to
populate the existing resulted history so the margin analysis has
enough sample to read.

Backups the runners CSV before writing.
"""

import shutil
import sys
from pathlib import Path
import pandas as pd

RUNNERS_CSV = Path("toprate_runners.csv")
FORM_CSV = Path("wpr_form_history.csv")


def main():
    if not RUNNERS_CSV.exists():
        print(f"Could not find {RUNNERS_CSV}.")
        sys.exit(1)
    if not FORM_CSV.exists():
        print(f"Could not find {FORM_CSV}.")
        sys.exit(1)

    # Backup first
    backup = RUNNERS_CSV.with_suffix(".csv.before_margin_backfill")
    shutil.copy2(RUNNERS_CSV, backup)
    print(f"Backed up {RUNNERS_CSV} -> {backup}")

    runners = pd.read_csv(RUNNERS_CSV,
                          dtype={"run_id": str, "race_id": str},
                          low_memory=False)
    fh = pd.read_csv(FORM_CSV,
                     dtype={"run_id": str, "race_id": str},
                     low_memory=False)

    print(f"Runners rows: {len(runners):,}")
    print(f"Form-history rows: {len(fh):,}")

    if "margin_finish" not in runners.columns:
        runners["margin_finish"] = pd.NA
        print("Added new column 'margin_finish' to runners.")

    if "marginFinish" not in fh.columns:
        print("Form history does NOT have a 'marginFinish' column - "
              "nothing to backfill from. Exiting safely.")
        sys.exit(0)

    # Build a run_id -> margin lookup. Dedupe just in case (keep last).
    fh_slim = fh[["run_id", "marginFinish"]].dropna(subset=["run_id"])
    fh_slim = fh_slim.drop_duplicates(subset=["run_id"], keep="last")
    margin_by_runid = dict(zip(fh_slim["run_id"].astype(str),
                                fh_slim["marginFinish"]))
    print(f"Form-history run_ids with margin: {len(margin_by_runid):,}")

    # Apply - only overwrite where margin_finish is currently NaN/missing.
    # Honest behaviour: never clobber a value that was captured by the
    # updated daily script.
    n_filled = 0
    n_already = 0
    n_no_match = 0
    for idx in runners.index:
        run_id = str(runners.at[idx, "run_id"])
        existing = runners.at[idx, "margin_finish"]
        try:
            already_set = pd.notna(existing)
        except Exception:
            already_set = False
        if already_set:
            n_already += 1
            continue
        m = margin_by_runid.get(run_id)
        if m is not None and pd.notna(m):
            runners.at[idx, "margin_finish"] = m
            n_filled += 1
        else:
            n_no_match += 1

    print(f"Filled:    {n_filled:,}")
    print(f"Already set (skipped): {n_already:,}")
    print(f"No match in form history: {n_no_match:,}")

    runners.to_csv(RUNNERS_CSV, index=False)
    print(f"Wrote {RUNNERS_CSV}.")
    print()
    print("Sanity check after backfill:")
    nonnull = runners["margin_finish"].notna().sum()
    print(f"  rows with margin_finish set: {nonnull:,}")


if __name__ == "__main__":
    main()
