"""backfill_form_history_depth.py - one-time backfill: re-fetch the rich
per-runner __data.json for run_ids already in wpr_form_history.csv.gz and
add rows for any (horse_id, date) the rich fetch has but the thin
get_race_wpr_chart feed never captured.

WHY
  wpr_form_history.csv.gz rows were, until this session, created ONLY from
  the thin get_race_wpr_chart feed's per-runner 'form' array. The richer
  __data.json runner-page endpoint frequently returns a DEEPER history for
  the same horse (probe: 25 past runs vs 8 captured, for one horse) but was
  only ever used to enrich columns on rows that already existed - never to
  add the missing rows. toprate_daily.py's _enrich_form_history_rich() now
  does this going forward (see that function). This script does the same
  retroactively, for every run_id already sitting in the history file, so
  existing horses' incomplete records get filled in, not just future ones.

USAGE
  python backfill_form_history_depth.py                # last 30 days, dry run
  python backfill_form_history_depth.py --days 90       # wider window
  python backfill_form_history_depth.py --all           # every run_id in the file
  python backfill_form_history_depth.py --write         # actually write

SAFE
  - Dry run by default.
  - Only ADDS rows for (horse_id, date) pairs not already present anywhere
    in the file - never touches or overwrites an existing row.
  - Backs up wpr_form_history.csv.gz before writing.
  - Bails loudly if the first 10 run_ids all come back empty/failed (a sign
    the API no longer serves those particular runner pages, not a bug worth
    grinding through the rest of the window for).

NO EM DASHES policy: hyphens only in this file.
"""
import argparse
import shutil
import time
from concurrent.futures import ThreadPoolExecutor, as_completed

import pandas as pd

import toprate_daily as td
import toprate_json_capture as cap


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--days", type=int, default=30,
                    help="only re-fetch run_ids last scraped within this many "
                         "days (default 30, ignored if --all)")
    ap.add_argument("--all", action="store_true",
                    help="re-fetch every run_id in the file, not just recent "
                         "ones (slow - the API may not serve very old runner "
                         "pages at all, so most will just come back EMPTY)")
    ap.add_argument("--write", action="store_true",
                    help="actually update wpr_form_history.csv.gz (default: "
                         "dry run)")
    args = ap.parse_args()

    df = pd.read_csv(td.WPR_FORM_HISTORY_CSV,
                     dtype={"run_id": str, "horse_id": str}, low_memory=False)
    print(f"Loaded {len(df):,} rows, {df['run_id'].nunique():,} distinct run_ids")

    if args.all:
        candidates = df["run_id"].dropna().unique().tolist()
    else:
        parsed = pd.to_datetime(df["scrape_date"], errors="coerce")
        cutoff = pd.Timestamp.now().normalize() - pd.Timedelta(days=args.days)
        candidates = df.loc[parsed >= cutoff, "run_id"].dropna().unique().tolist()
    print(f"{len(candidates):,} run_ids to re-fetch "
          f"({'all' if args.all else f'last {args.days} days'})")
    if not candidates:
        print("Nothing to backfill.")
        return

    # Existing (horse_id, date) keys across the WHOLE file - a new row is
    # only added if genuinely missing, regardless of the --days window.
    existing_keys = set(zip(df["horse_id"].astype(str),
                             df["date"].astype(str).str[:10]))
    name_by_rid = (df.dropna(subset=["horse"])
                     .drop_duplicates("run_id")
                     .set_index("run_id")["horse"].to_dict())
    # Each horse's OWN latest existing scrape_date - new rows must join that
    # same baseline group, not get stamped with today's date. wpr is a
    # rebased rating (see wpr_projection._dedup_scrape_baseline): training
    # keeps ONLY a horse's single most-recent scrape_date and drops the
    # rest. Stamping every backfilled row with "today" would make it look
    # like a newer, separate scrape than the horse's real baseline, so that
    # dedup step would keep only the tiny newly-added set and drop all of
    # the horse's properly-captured existing rows - the opposite of the
    # point of this script.
    latest_scrape_by_hid = (df.dropna(subset=["horse_id", "scrape_date"])
                               .groupby(df["horse_id"].astype(str))["scrape_date"]
                               .max().to_dict())
    today_str = pd.Timestamp.now().normalize().strftime("%Y-%m-%d")

    print("Logging in ...")
    td.login()

    def _one(rid):
        try:
            return rid, cap.fetch_runner(rid)
        except Exception:
            return rid, (None, [])

    rich = {}
    n_ok = n_empty = n_fail = 0
    t0 = time.time()
    done = 0
    stopped_early = False
    with ThreadPoolExecutor(max_workers=td.DEFAULT_FETCH_WORKERS) as pool:
        futures = {pool.submit(_one, rid): rid for rid in candidates}
        for fut in as_completed(futures):
            done += 1
            if done % 200 == 0:
                print(f"  ... {done}/{len(candidates)} ({time.time()-t0:.0f}s, "
                      f"{len(rich):,} run keys collected so far, "
                      f"ok {n_ok}, empty {n_empty}, fail {n_fail})")
            rid, (horse_id, runs) = fut.result()
            if horse_id == "EMPTY":
                n_empty += 1
            elif horse_id is None:
                n_fail += 1
            else:
                n_ok += 1
                for run in runs:
                    d = str(run.get("date", ""))[:10]
                    if d:
                        rich[(str(horse_id), d)] = (rid, run.get("fields", {}))

            if done == 10 and n_ok == 0:
                print("\n  ALL of the first 10 run_ids returned empty/failed.")
                print("  Likely the API no longer serves these runner pages.")
                print("  Stopping early rather than burning the rest of the "
                      f"{len(candidates):,}-id window.")
                stopped_early = True
                break

    print(f"\nFetched {n_ok:,} runner pages ok, {n_empty:,} empty, "
          f"{n_fail:,} failed ({time.time()-t0:.0f}s)"
          f"{' (stopped early)' if stopped_early else ''}")

    new_rows = []
    for (hid, d), (rid, fields) in rich.items():
        if (hid, d) in existing_keys:
            continue
        row = {
            "run_id": rid,
            "horse_id": hid,
            "horse": name_by_rid.get(rid),
            "scrape_date": latest_scrape_by_hid.get(hid, today_str),
            "date": d,
        }
        for col in cap.ALL_COLS:
            row[col] = fields.get(col)
        new_rows.append(row)

    print(f"{len(new_rows):,} new rows found (runs the thin feed never captured)")
    if not new_rows:
        print("Nothing to add. Exiting without writing.")
        return

    if not args.write:
        print("\nDRY RUN - nothing written. Re-run with --write to apply.")
        sample_cols = [c for c in ("horse", "date", "track", "wpr")
                       if c in pd.DataFrame(new_rows).columns]
        print(pd.DataFrame(new_rows[:10])[sample_cols].to_string(index=False))
        return

    backup = str(td.WPR_FORM_HISTORY_CSV) + ".pre_depth_backfill"
    shutil.copy(td.WPR_FORM_HISTORY_CSV, backup)
    print(f"Backed up to {backup}")

    combined = pd.concat([df, pd.DataFrame(new_rows)], ignore_index=True)
    combined.to_csv(td.WPR_FORM_HISTORY_CSV, index=False)
    print(f"Wrote {td.WPR_FORM_HISTORY_CSV} - {len(combined):,} total rows "
          f"(+{len(new_rows):,})")


if __name__ == "__main__":
    main()
