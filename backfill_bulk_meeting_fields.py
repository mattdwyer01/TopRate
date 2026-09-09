"""
backfill_bulk_meeting_fields.py
---------------------------------
Backfill the age/sex/pedigree/claim/race-condition fields (added to
toprate_json_capture.py, Sep 2026) into EXISTING rows of
wpr_form_history.csv.gz, using the meetings/{id}/history bulk endpoint
confirmed live (see chat) instead of the per-runner endpoint.

WHY THIS EXISTS
  toprate_json_capture.py's extraction only fires going forward, through
  _enrich_form_history_rich() during the normal daily/price-refresh run.
  Every row already in wpr_form_history.csv.gz (324,026 rows, back to
  2016) has the new columns blank. meetings/{id}/history returns a
  whole finalized meeting's results (sectionals, race shape, pedigree,
  claims, positions/margins) for every runner in one call, keyed by
  runId, which already exists as run_id on every row - so this is a
  pure enrichment of rows that already exist, not a new ingestion path,
  and it needs about 20,648 calls (one per meeting already on file)
  instead of one per runner.

SAFETY
  - Dry-run by default. Pass --commit to actually write the CSV.
  - Only fills cells that are currently NaN/empty. Never overwrites a
    value that's already there, in any column, old or new.
  - Never creates new rows and never touches the dedup key or any
    column this script doesn't own.
  - Backs up the CSV (timestamped) before any write.
  - Checkpoints successfully-merged meeting_ids to a local file so a
    long run can be interrupted and resumed without refetching. Only
    written when --commit is set, so a dry run never poisons resume
    state for a later real run. A meeting whose result isn't finalized
    yet is NOT checkpointed, so it gets retried on the next run rather
    than silently skipped forever.

USAGE
  python backfill_bulk_meeting_fields.py --limit 20              # dry-run test
  python backfill_bulk_meeting_fields.py --limit 20 --commit      # write a small batch
  python backfill_bulk_meeting_fields.py --since 2025-01-01 --commit
  python backfill_bulk_meeting_fields.py --all --commit           # everything (hours)

  Start small. One of --limit / --since / --all is required so a bare
  invocation can't accidentally kick off a multi-hour run.

NO EM DASHES policy: hyphens only in this file.
"""

import argparse
import shutil
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime
from pathlib import Path

import pandas as pd

import toprate_json_capture as cap

CHECKPOINT_FILE = Path(__file__).parent / "backfill_bulk_meeting_fields.checkpoint"
DEFAULT_WORKERS = 8

# The columns this script is allowed to touch: the new horse/run fields
# plus sectionals, since those are ALSO sparse on rows captured same-day
# before TopRate's wprStatus flipped Preliminary -> Final (confirmed in
# chat). Deliberately NOT the broader cap.ALL_COLS - CORE_COLS fields
# like position/margin curves are already well populated on old
# (long-finalized) rows via the thin feed, so touching them adds risk
# for no real gain.
FILLABLE_COLS = (list(cap.SECT_MAP.values())
                  + list(cap.HORSE_COLS.values())
                  + list(cap.RUN_COLS.values()))


def _build_url(meeting_id):
    return f"{cap.WEB_BASE}/meetings/{meeting_id}/history/__data.json"


def fetch_meeting_result(meeting_id):
    """Fetch meetings/{id}/history and return (meetingResult dict, deref)
    or (None, None) if the meeting isn't finalized yet, wasn't found, or
    a hard failure occurred. Reuses the same auth/redirect/login-bounce
    handling already established for this route in
    toprate_page_discovery.py."""
    url = _build_url(meeting_id)
    for attempt in range(1, cap.MAX_RETRIES + 1):
        headers, cookies = cap._auth_bits()
        try:
            resp = cap.requests.get(url, headers=headers, cookies=cookies,
                                     verify=cap.VERIFY_SSL, timeout=cap.TIMEOUT,
                                     allow_redirects=False)
        except cap.requests.RequestException:
            time.sleep(2 * attempt)
            continue
        if resp.status_code in (301, 302, 303, 307, 308, 401):
            import toprate_daily as td
            td._SESSION_OBJ = None
            time.sleep(2 * attempt)
            continue
        if resp.status_code == 404:
            return None, None
        if resp.status_code != 200:
            time.sleep(2 * attempt)
            continue
        try:
            payload = resp.json()
        except ValueError:
            time.sleep(2 * attempt)
            continue
        if isinstance(payload, dict) and payload.get("type") == "redirect":
            loc = payload.get("location") or ""
            redir = loc if loc.startswith("http") else f"{cap.WEB_BASE}{loc}"
            if "__data.json" not in redir:
                redir = redir.rstrip("/") + "/__data.json"
            try:
                resp2 = cap.requests.get(redir, headers=headers, cookies=cookies,
                                          verify=cap.VERIFY_SSL, timeout=cap.TIMEOUT,
                                          allow_redirects=False)
                payload = resp2.json()
            except (cap.requests.RequestException, ValueError):
                time.sleep(2 * attempt)
                continue
        if cap._is_login_bounce(payload):
            import toprate_daily as td
            td._SESSION_OBJ = None
            time.sleep(2 * attempt)
            continue

        nodes = payload.get("nodes") if isinstance(payload, dict) else None
        if not isinstance(nodes, list):
            return None, None
        for n in nodes:
            if not (isinstance(n, dict) and isinstance(n.get("data"), list)):
                continue
            data = n["data"]
            root = data[0] if data else None
            if not isinstance(root, dict) or "meetingResult" not in root:
                continue

            def deref(p, _data=data):
                return _data[p] if isinstance(p, int) else p

            mr = deref(root.get("meetingResult"))
            return (mr if isinstance(mr, dict) else None), deref
        return None, None
    # Retries exhausted without ever getting a usable response (network
    # errors, non-200s, bad JSON) - a genuine failure, distinct from a
    # clean response whose meetingResult is legitimately null (not
    # finalized yet / not found, handled by the returns above).
    return "ERROR", None


def extract_meeting_fields(meeting_result, deref):
    """Return {run_id (str): {col: value}} for every runner in this
    finalized meeting, restricted to FILLABLE_COLS. Runner-level values
    win; race-level ones (e.g. weightRestriction, venue) are the
    fallback for keys that live on the race rather than the runner."""
    out = {}
    races = deref(meeting_result.get("races"))
    if not isinstance(races, list):
        return out
    src_map = {**cap.HORSE_COLS, **cap.RUN_COLS}
    for rp in races:
        race = deref(rp)
        if not isinstance(race, dict):
            continue
        runners = deref(race.get("runners"))
        if not isinstance(runners, list):
            continue
        for rup in runners:
            runner = deref(rup)
            if not isinstance(runner, dict):
                continue
            run_id = deref(runner.get("runId"))
            if run_id is None:
                continue
            fields = {}
            sr = deref(runner.get("sectionalRating"))
            if isinstance(sr, dict):
                for src_key, col in cap.SECT_MAP.items():
                    v = deref(sr.get(src_key))
                    fields[col] = v if isinstance(v, (int, float)) else None
            for src_key, col in src_map.items():
                v = runner.get(src_key)
                if v is None:
                    v = race.get(src_key)
                fields[col] = cap._scalar(deref(v))
            out[str(run_id)] = fields
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                  formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--limit", type=int, default=None,
                     help="Only process the first N meetings (most recent first)")
    ap.add_argument("--since", default=None,
                     help="Only meetings on/after this date (YYYY-MM-DD)")
    ap.add_argument("--all", action="store_true",
                     help="Process every meeting on file (hours, ~20,648 calls)")
    ap.add_argument("--commit", action="store_true",
                     help="Actually write the CSV (default: dry-run, nothing saved)")
    ap.add_argument("--workers", type=int, default=DEFAULT_WORKERS)
    args = ap.parse_args()

    if not (args.limit or args.since or args.all):
        sys.exit("Refusing to run with no scope: pass --limit N, --since DATE, "
                  "or --all explicitly. See the module docstring for examples.")

    import toprate_daily as td
    fh_path = td.WPR_FORM_HISTORY_CSV
    print(f"Loading {fh_path} ...")
    fh = pd.read_csv(fh_path, dtype={"run_id": str, "horse_id": str}, low_memory=False)
    print(f"  {len(fh):,} rows")

    for col in FILLABLE_COLS:
        if col not in fh.columns:
            fh[col] = None

    meetings = fh.loc[fh["meeting_id"].notna(), ["meeting_id", "date"]].drop_duplicates()
    meetings["meeting_id"] = meetings["meeting_id"].astype(float).astype(int).astype(str)
    if args.since:
        meetings = meetings[meetings["date"] >= args.since]
    meetings = meetings.sort_values("date", ascending=False)
    meeting_ids = meetings["meeting_id"].tolist()

    checkpoint = set()
    if CHECKPOINT_FILE.exists():
        checkpoint = set(CHECKPOINT_FILE.read_text().split())
        print(f"  Resuming: {len(checkpoint):,} meetings already done per checkpoint")
    meeting_ids = [m for m in meeting_ids if m not in checkpoint]

    if args.limit:
        meeting_ids = meeting_ids[:args.limit]
    print(f"  {len(meeting_ids):,} meetings to fetch "
          f"({'DRY RUN, nothing will be saved' if not args.commit else 'WILL WRITE on completion'})")
    if not meeting_ids:
        print("Nothing to do.")
        return

    idx_by_run_id = {}
    for idx, rid in fh["run_id"].astype(str).items():
        idx_by_run_id.setdefault(rid, []).append(idx)

    n_meetings_ok = n_meetings_empty = n_meetings_fail = 0
    n_rows_touched = 0
    n_cells_filled = 0
    t0 = time.time()

    def _one(mid):
        try:
            return mid, fetch_meeting_result(mid)
        except Exception:
            return mid, ("ERROR", None)

    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        futures = [pool.submit(_one, mid) for mid in meeting_ids]
        done = 0
        for fut in as_completed(futures):
            done += 1
            if done % 200 == 0:
                elapsed = time.time() - t0
                rate = done / elapsed if elapsed else 0
                eta = (len(meeting_ids) - done) / rate if rate else float("nan")
                print(f"  ... {done}/{len(meeting_ids)} meetings "
                      f"({elapsed:.0f}s, {n_rows_touched:,} rows touched, "
                      f"ETA {eta:.0f}s)")
            mid, (mr, deref) = fut.result()
            if mr == "ERROR":
                n_meetings_fail += 1
                continue  # genuine failure - not checkpointed, retried next run
            if mr is None:
                n_meetings_empty += 1
                continue  # not finalized / not found - also retried next run
            fields_by_run = extract_meeting_fields(mr, deref)
            if not fields_by_run:
                n_meetings_empty += 1
                continue
            n_meetings_ok += 1
            for rid, fields in fields_by_run.items():
                rows = idx_by_run_id.get(rid)
                if not rows:
                    continue  # this run isn't in our existing history - never create rows
                for idx in rows:
                    touched_this_row = False
                    for col, v in fields.items():
                        if v is None:
                            continue
                        if pd.isna(fh.at[idx, col]):
                            fh.at[idx, col] = v
                            n_cells_filled += 1
                            touched_this_row = True
                    if touched_this_row:
                        n_rows_touched += 1
            if args.commit:
                checkpoint.add(mid)
                CHECKPOINT_FILE.write_text("\n".join(sorted(checkpoint)))

    print(f"\nDone in {time.time()-t0:.0f}s.")
    print(f"  meetings: {n_meetings_ok:,} merged, {n_meetings_empty:,} not finalized/empty, "
          f"{n_meetings_fail:,} failed")
    print(f"  {n_rows_touched:,} existing rows had at least one cell filled")
    print(f"  {n_cells_filled:,} individual cells filled")

    if not args.commit:
        print("\nDRY RUN - nothing written. Re-run with --commit to save for real.")
        return

    backup = f"{fh_path}.pre_bulk_backfill_{datetime.now():%Y%m%d_%H%M%S}"
    shutil.copy(fh_path, backup)
    print(f"Backed up existing file to {backup}")
    fh.to_csv(fh_path, index=False)
    print(f"Wrote {fh_path}")


if __name__ == "__main__":
    main()
