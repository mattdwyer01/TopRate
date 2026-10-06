"""
backfill_runner_history.py
----------------------------
Backfill price_opening/price_mid/is_letup/is_spell/blinkers_on/
time_last600m/race_name/gear_changes (and every other HORSE_COLS/
RUN_COLS/EXTRA_COLS field) into EXISTING rows of race_results_*.csv.gz,
via toprate.au's per-runner /runners/{run_id}/__data.json endpoint
(the SAME endpoint toprate_json_capture.py already uses for the daily
pipeline and wpr_form_history.csv.gz).

WHY THIS EXISTS
  backfill_race_results.py's meetings/{id}/history bulk endpoint does
  NOT carry isLetup/isSpell/blinkersOn/timeLast600m/priceOpening/
  priceMid at all (confirmed via --scan-keys, Sep 2026, see chat: 0%
  key presence across 623 real runners at every level). The per-runner
  endpoint DOES carry all of them - confirmed live (Sep 2026, see chat)
  that one fetch's "form" array is the horse's FULL CAREER history (one
  real case: 31 entries spanning its 2023-06-05 debut to its latest
  2026-09-26 start, not a capped recent window), with priceOpening=31,
  raceName, isLetup/isSpell/blinkersOn/timeLast600m/gearChanges all
  present on every entry. So ONE fetch per horse (not per run, not per
  meeting) can retroactively fill these fields for every race that
  horse has ever run, confirmed in race_results_*.csv.gz.

  Scoped to ~1 request per unique horse_id on file (97,747 as of Sep
  2026 - see chat), not 1 request per runner-row (1.3M+) - using any one
  of that horse's own known run_ids (the most recent one on file) is
  enough, since the form array it returns covers that horse's whole
  career regardless of which run_id you ask for.

  A horse that stopped racing long enough ago may no longer have a
  servable page at all (fetch_runner returns ('EMPTY', [], ...) in that
  case per toprate_json_capture.py's own contract) - this is expected
  for some fraction of older/retired horses, not a bug. Run a small
  --limit test first and read the empty/ok counts before committing to
  --all, same as every other backfill script in this project.

OUTPUT
  Fills BLANK cells only, in the EXISTING rows of race_results_*.csv.gz
  (one file per year, see backfill_race_results.py's own OUTPUTS
  docstring for why). Never creates new rows, never overwrites a value
  that's already there - same safety contract as
  backfill_bulk_meeting_fields.py's merge_into_history(), adapted here
  for a (horse_id, date) key split across MULTIPLE year files instead
  of one single CSV.

THREE MODES (same split as every other backfill script here)
  Combined (default, local): fetch AND merge in one process.
  --fetch-only OUT.json: fetch phase only, writes {horse_id|date: {col: val}}.
  --merge-only IN.json [--commit]: merge phase only, no network calls.

SAFETY
  - Dry-run by default. Pass --commit to actually write a CSV.
  - Only fills cells that are currently NaN/empty, in any of the
    race_results_YYYY.csv.gz files, never overwrites, never creates rows.
  - Checkpoints horse_ids ONLY after a successful --commit merge (never
    at fetch time) - same incident/fix this project already documented
    for backfill_race_results.py's own checkpoint (a pushed checkpoint
    entry must always mean its data is durably on disk).

USAGE (local, combined mode)
  python backfill_runner_history.py --limit 20              # dry-run test
  python backfill_runner_history.py --limit 20 --commit
  python backfill_runner_history.py --since 2026-01-01 --commit
  python backfill_runner_history.py --all --commit           # everything (hours)

USAGE (split mode, what the GitHub Action uses)
  python backfill_runner_history.py --fetch-only out.json --since 2026-01-01
  python backfill_runner_history.py --merge-only out.json --commit

NO EM DASHES policy: hyphens only in this file.
"""

import argparse
import glob
import json
import re
import shutil
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime
from pathlib import Path

import pandas as pd

import toprate_json_capture as cap

CHECKPOINT_FILE = Path(__file__).parent / "backfill_runner_history.checkpoint"
DEFAULT_WORKERS = 8

# Columns this script is allowed to fill. Deliberately excludes identity/
# structural columns (race_id, meeting_id, horse_id, horse, run_id, date,
# field_size, rail_position) - those are never blank-fillable targets,
# they're the join key or already reliably populated from the bulk
# endpoint backfill_race_results.py uses. SECT_MAP's sectional columns are
# included since they're ALSO sparse on rows the bulk endpoint couldn't
# fill (same reasoning as backfill_bulk_meeting_fields.py's own
# FILLABLE_COLS).
FILLABLE_COLS = (list(cap.SECT_MAP.values())
                  + list(cap.HORSE_COLS.values())
                  + list(cap.RUN_COLS.values())
                  + ["weight_handicap", "race_class", "is_letup", "is_spell",
                     "blinkers_on", "gear_changes", "comments_steward",
                     "comments_video", "time_last600m", "jockey", "trainer",
                     "is_jumpout"])


def _year_files():
    """All race_results_YYYY.csv.gz paths on disk, sorted by year."""
    paths = sorted(Path(__file__).parent.glob("race_results_*.csv.gz"))
    return [p for p in paths if re.fullmatch(r"race_results_\d{4}\.csv\.gz", p.name)]


def _select_horse_run_ids(args):
    """Scan every race_results_YYYY.csv.gz for (horse_id -> most recent
    known run_id on file), optionally filtered by --since on the row's
    own date, minus already-checkpointed horse_ids. Using the MOST
    RECENT run_id for each horse, since the per-runner endpoint's "form"
    array has been confirmed (see chat) to return that horse's full
    career regardless of which of its own run_ids you ask for - the
    latest one is the best bet for still being servable."""
    frames = []
    for path in _year_files():
        df = pd.read_csv(path, usecols=["horse_id", "run_id", "date"],
                          dtype={"horse_id": str, "run_id": str}, low_memory=False)
        frames.append(df)
    if not frames:
        return [], set()
    all_rows = pd.concat(frames, ignore_index=True)
    all_rows = all_rows.dropna(subset=["horse_id", "run_id"])
    if args.since:
        all_rows = all_rows[all_rows["date"].astype(str) >= args.since]
    all_rows = all_rows.sort_values("date", ascending=False)
    latest = all_rows.drop_duplicates(subset=["horse_id"], keep="first")

    checkpoint = set()
    if CHECKPOINT_FILE.exists():
        checkpoint = set(CHECKPOINT_FILE.read_text().split())
        print(f"  Resuming: {len(checkpoint):,} horses already fetched per checkpoint")
    latest = latest[~latest["horse_id"].isin(checkpoint)]

    pairs = list(zip(latest["horse_id"], latest["run_id"]))
    if args.limit:
        pairs = pairs[:args.limit]
    return pairs, checkpoint


def run_fetch_phase(pairs, workers):
    """Fetch every (horse_id, run_id) pair. Returns (results,
    attempted_horse_ids) where results is {"horse_id|date": {col: val}}
    (restricted to FILLABLE_COLS) and attempted_horse_ids is EVERY
    horse_id actually attempted, served or not - a horse that comes back
    'EMPTY' (retired/outside window) still belongs in the checkpoint, so
    a later run doesn't keep re-requesting a page that will never serve
    data (see module SAFETY docstring: checkpoint means "already tried",
    not "got data"). A hard FAILURE is deliberately left OUT of
    attempted_horse_ids, so a transient error gets retried next run
    rather than being permanently given up on."""
    n_ok = n_empty = n_fail = 0
    t0 = time.time()
    results = {}
    attempted = set()

    def _one(pair):
        hid, rid = pair
        try:
            return hid, cap.fetch_runner(rid)
        except Exception:
            return hid, (None, [], None, None)

    with ThreadPoolExecutor(max_workers=workers) as pool:
        futures = [pool.submit(_one, p) for p in pairs]
        done = 0
        for fut in as_completed(futures):
            done += 1
            if done % 200 == 0:
                elapsed = time.time() - t0
                rate = done / elapsed if elapsed else 0
                eta = (len(pairs) - done) / rate if rate else float("nan")
                print(f"  ... {done}/{len(pairs)} horses "
                      f"({elapsed:.0f}s, {len(results):,} run-dates collected, ETA {eta:.0f}s)")
            hid, (returned_hid, runs, _gc_today, _today_stats) = fut.result()
            if returned_hid == "EMPTY":
                n_empty += 1
                attempted.add(hid)
                continue
            if returned_hid is None:
                n_fail += 1
                continue
            n_ok += 1
            use_hid = str(returned_hid) if returned_hid is not None else hid
            attempted.add(use_hid)
            for run in runs:
                d = run.get("date")
                fields = run.get("fields", {})
                if not d:
                    continue
                restricted = {k: v for k, v in fields.items() if k in FILLABLE_COLS}
                results[f"{use_hid}|{d[:10]}"] = restricted

    print(f"\nFetch done in {time.time()-t0:.0f}s.")
    print(f"  horses: {n_ok:,} served, {n_empty:,} not served (retired/outside window), {n_fail:,} failed")
    print(f"  {len(results):,} distinct horse|date run-entries collected")
    return results, attempted


def fill_blanks(fields_by_key, commit, backup=True):
    """For every race_results_YYYY.csv.gz, fill currently-blank
    FILLABLE_COLS cells from fields_by_key (keyed "horse_id|date"), in
    place. Never creates rows, never overwrites a non-null value.
    Returns (n_rows_touched, n_cells_filled) across all years."""
    total_rows_touched = 0
    total_cells_filled = 0
    total_skipped = 0
    skipped_examples = []

    for path in _year_files():
        print(f"Loading {path.name} for merge ...")
        df = pd.read_csv(path, dtype={"race_id": str, "horse_id": str, "meeting_id": str},
                          low_memory=False)
        print(f"  {len(df):,} rows")

        for col in FILLABLE_COLS:
            if col not in df.columns:
                df[col] = None

        dates = df["date"].astype(str).str[:10]
        idx_by_key = {}
        for idx, hid, d in zip(df.index, df["horse_id"].astype(str), dates):
            idx_by_key.setdefault(f"{hid}|{d}", []).append(idx)

        rows_touched = 0
        cells_filled = 0
        any_change = False
        for key, fields in fields_by_key.items():
            rows = idx_by_key.get(key)
            if not rows:
                continue
            for idx in rows:
                touched_this_row = False
                for col, v in fields.items():
                    if v is None or col not in FILLABLE_COLS:
                        continue
                    if not pd.isna(df.at[idx, col]):
                        continue
                    try:
                        df.at[idx, col] = v
                        cells_filled += 1
                        touched_this_row = True
                        any_change = True
                    except (TypeError, ValueError) as e:
                        total_skipped += 1
                        if len(skipped_examples) < 10:
                            skipped_examples.append(f"{col}={v!r} ({e})")
                if touched_this_row:
                    rows_touched += 1

        print(f"  {path.name}: {rows_touched:,} rows touched, {cells_filled:,} cells filled")
        total_rows_touched += rows_touched
        total_cells_filled += cells_filled

        if not commit or not any_change:
            continue

        if backup:
            bkp = f"{path}.pre_runner_backfill_{datetime.now():%Y%m%d_%H%M%S}"
            shutil.copy(path, bkp)
            print(f"  backed up existing file to {bkp}")
        df.to_csv(path, index=False)
        print(f"  wrote {path}")

    print(f"\n{total_rows_touched:,} rows touched, {total_cells_filled:,} cells filled total")
    if total_skipped:
        print(f"  {total_skipped:,} cells SKIPPED (bad value for dtype), examples:")
        for ex in skipped_examples:
            print(f"    {ex}")
    if not commit and total_cells_filled:
        print("DRY RUN - nothing written. Pass --commit to save for real.")
    return total_rows_touched, total_cells_filled


def write_checkpoint(horse_ids):
    """Union horse_ids into CHECKPOINT_FILE on disk. Call this ONLY after
    fill_blanks has successfully written the corresponding rows - never
    before, never speculatively (same contract as every other backfill
    script's checkpoint here)."""
    if not horse_ids:
        return
    existing = set()
    if CHECKPOINT_FILE.exists():
        existing = set(CHECKPOINT_FILE.read_text().split())
    combined = existing | {str(h) for h in horse_ids}
    CHECKPOINT_FILE.write_text("\n".join(sorted(combined)))
    print(f"  checkpoint: {len(combined) - len(existing):,} new horse_ids added "
          f"({len(combined):,} total)")


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                  formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--limit", type=int, default=None,
                     help="Only fetch the first N horses (most recently active first)")
    ap.add_argument("--since", default=None,
                     help="Only consider horses with a race on/after this date (YYYY-MM-DD) "
                          "when picking which run_id to fetch for them")
    ap.add_argument("--all", action="store_true",
                     help="Process every horse on file (tens of thousands of calls - hours)")
    ap.add_argument("--commit", action="store_true",
                     help="Actually write the CSVs (default: dry-run, nothing saved)")
    ap.add_argument("--workers", type=int, default=DEFAULT_WORKERS)
    ap.add_argument("--fetch-only", metavar="OUT.json", default=None,
                     help="Fetch phase only: write results here, never touch the CSVs")
    ap.add_argument("--merge-only", metavar="IN.json", default=None,
                     help="Merge phase only: read results from here, no network calls")
    args = ap.parse_args()

    if args.merge_only:
        with open(args.merge_only) as f:
            payload = json.load(f)
        fields_by_key = payload["fields_by_key"]
        attempted = payload.get("attempted_horse_ids", [])
        print(f"Loaded {len(fields_by_key):,} horse|date entries "
              f"({len(attempted):,} attempted horses) from {args.merge_only}")
        fill_blanks(fields_by_key, commit=args.commit, backup=True)
        if args.commit:
            write_checkpoint(attempted)
        return

    if not (args.limit or args.since or args.all):
        sys.exit("Refusing to run with no scope: pass --limit N, --since DATE, "
                  "or --all explicitly. See the module docstring for examples.")

    pairs, checkpoint = _select_horse_run_ids(args)
    print(f"  {len(pairs):,} horses to fetch")
    if not pairs:
        print("Nothing to do.")
        return

    fields_by_key, attempted = run_fetch_phase(pairs, args.workers)

    if args.fetch_only:
        with open(args.fetch_only, "w") as f:
            json.dump({"fields_by_key": fields_by_key,
                       "attempted_horse_ids": sorted(attempted)}, f)
        print(f"Wrote {len(fields_by_key):,} horse|date entries "
              f"({len(attempted):,} attempted horses) to {args.fetch_only}")
        return

    # Combined mode: merge immediately using this same process's fetch
    # results. Fine for a local manual run; the split mode above is what
    # the GitHub Action uses, same reasoning as every other backfill
    # script in this project.
    fill_blanks(fields_by_key, commit=args.commit)
    if args.commit:
        write_checkpoint(attempted)


if __name__ == "__main__":
    main()
