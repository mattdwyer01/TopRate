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

THREE MODES
  Combined (default, for a local interactive run): fetch AND merge in
  one process, exactly like the first version of this script. Fine
  locally where you can see the whole run and nothing else is racing
  you to write the same file.

  --fetch-only OUT.json: fetch phase ONLY. Writes {run_id: {col: val}}
  for every runner found to OUT.json. Never reads, merges, or writes
  wpr_form_history.csv.gz at all.

  --merge-only IN.json [--commit]: merge phase ONLY. Loads the CURRENT
  wpr_form_history.csv.gz fresh (no network calls) and IN.json, fills
  empty cells, writes if --commit.

  Split mode exists because this file is also touched by price_refresh.yml
  every 5 minutes. A long fetch phase (minutes to hours) means the CSV
  checked out at job start is stale by the time a combined run would
  write it - pushing that stale-derived version, then resolving the
  inevitable git conflict with the standard "-X theirs" used elsewhere
  in this repo's Actions, would silently DISCARD the whole backfill (see
  CLAUDE.md's own incident writeup for exactly this failure mode on this
  exact file). The correct order, also per CLAUDE.md, is: take theirs
  for the conflicted file, then re-run the recompute on top of that
  fresher base - never push a snapshot of a base that's gone stale. The
  merge phase is cheap and side-effect-free enough to safely repeat
  against a freshly re-pulled file inside a retry loop (see
  .github/workflows/backfill_bulk_meeting_fields.yml); the fetch
  phase's expensive network results, cached in the JSON, never need
  refetching just because the CSV moved under it.

SAFETY (applies to the merge step in every mode)
  - Dry-run by default. Pass --commit to actually write the CSV.
  - Only fills cells that are currently NaN/empty. Never overwrites a
    value that's already there, in any column, old or new.
  - Never creates new rows and never touches the dedup key or any
    column this script doesn't own.
  - Local combined/--merge-only runs back up the CSV (timestamped)
    before writing. (The GitHub Action doesn't need this - git history
    is the backup there.)
  - The fetch step checkpoints successfully-fetched meeting_ids to a
    local file so a long run can be interrupted and resumed without
    refetching. A meeting whose result isn't finalized yet is NOT
    checkpointed, so it gets retried on a later run rather than
    silently skipped forever.

USAGE (local, combined mode)
  python backfill_bulk_meeting_fields.py --limit 20              # dry-run test
  python backfill_bulk_meeting_fields.py --limit 20 --commit      # write a small batch
  python backfill_bulk_meeting_fields.py --since 2025-01-01 --commit
  python backfill_bulk_meeting_fields.py --all --commit           # everything (hours)

USAGE (split mode, what the GitHub Action uses)
  python backfill_bulk_meeting_fields.py --fetch-only out.json --since 2025-01-01
  python backfill_bulk_meeting_fields.py --merge-only out.json --commit

  One of --limit / --since / --all is required in every fetch-capable
  mode so a bare invocation can't accidentally kick off a multi-hour run.

NO EM DASHES policy: hyphens only in this file.
"""

import argparse
import json
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
# for no real gain. Two explicit CORE_COLS exceptions (Sep 2026):
# wprStatus (confirmed present at race level - the ledger's own
# training-data-staging decision needs this field to exist anywhere at
# all) and blackType (Group/Listed grading - sparse by nature, only set
# on actual stakes races, confirmed working via a real --limit 10 run:
# 7/589 rows filled - see cap.CORE_COLS' own comment).
FILLABLE_COLS = (list(cap.SECT_MAP.values())
                  + list(cap.HORSE_COLS.values())
                  + list(cap.RUN_COLS.values())
                  + ["wprStatus", "blackType"])


def _build_url(meeting_id):
    return f"{cap.WEB_BASE}/meetings/{meeting_id}/history/__data.json"


def fetch_meeting_result(meeting_id):
    """Fetch meetings/{id}/history and return (meetingResult dict, deref)
    or (None, None) if the meeting isn't finalized yet, wasn't found, or
    ("ERROR", None) if a hard failure occurred after retries. Reuses the
    same auth/redirect/login-bounce handling already established for
    this route in toprate_page_discovery.py."""
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
    """Return {"horse_id|date": {col: value}} for every runner in this
    finalized meeting, restricted to FILLABLE_COLS.

    Keyed by (horse_id, date), NOT run_id. Confirmed by direct check
    against the real file (see chat): run_id in wpr_form_history.csv.gz
    identifies the runner-PAGE scrape that produced a whole batch of
    past-run rows, not any single row - one run_id spans up to a dozen+
    different dates for one horse. (horse_id, date) is the join key
    _enrich_form_history_rich already uses elsewhere in this exact
    codebase, for the same documented reason: "a horse races at most
    once a day". Using run_id here would have silently written one
    meeting's per-run fields (weight_restriction, sectionals, etc) onto
    several unrelated rows for other dates.

    Runner-level values win; race-level ones (e.g. weightRestriction,
    venue) are the fallback for keys that live on the race rather than
    the runner. The string key (not a tuple) is so this dict survives a
    plain json.dump/load round trip between the fetch and merge phases."""
    out = {}
    meeting_date = deref(meeting_result.get("date"))
    races = deref(meeting_result.get("races"))
    if not isinstance(races, list) or not meeting_date:
        return out
    meeting_date = str(meeting_date)[:10]
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
            horse_id = deref(runner.get("horseId"))
            if horse_id is None:
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
            # wprStatus/blackType - raw-key-is-column-name (CORE_COLS
            # convention), not part of src_map's HORSE_COLS/RUN_COLS
            # mapping. Same runner-then-race fallback.
            for key in ("wprStatus", "blackType"):
                v = runner.get(key)
                if v is None:
                    v = race.get(key)
                fields[key] = cap._scalar(deref(v))
            out[f"{horse_id}|{meeting_date}"] = fields
    return out


def _load_history_for_scoping():
    """Read wpr_form_history.csv.gz just far enough to list candidate
    meeting_ids (used by both the fetch phase and combined mode)."""
    import toprate_daily as td
    fh_path = td.WPR_FORM_HISTORY_CSV
    print(f"Loading {fh_path} for meeting scoping ...")
    fh = pd.read_csv(fh_path, usecols=["run_id", "meeting_id", "date"],
                      dtype={"run_id": str}, low_memory=False)
    print(f"  {len(fh):,} rows")
    return fh_path, fh


def _select_meeting_ids(fh, args):
    meetings = fh.loc[fh["meeting_id"].notna(), ["meeting_id", "date"]].drop_duplicates()
    meetings["meeting_id"] = meetings["meeting_id"].astype(float).astype(int).astype(str)
    if args.since:
        meetings = meetings[meetings["date"] >= args.since]
    meetings = meetings.sort_values("date", ascending=False)
    meeting_ids = meetings["meeting_id"].tolist()

    checkpoint = set()
    if CHECKPOINT_FILE.exists():
        checkpoint = set(CHECKPOINT_FILE.read_text().split())
        print(f"  Resuming: {len(checkpoint):,} meetings already fetched per checkpoint")
    meeting_ids = [m for m in meeting_ids if m not in checkpoint]

    if args.limit:
        meeting_ids = meeting_ids[:args.limit]
    return meeting_ids, checkpoint


def run_fetch_phase(meeting_ids, workers, checkpoint, checkpoint_as_you_go=True):
    """Fetch every meeting_id and return {"horse_id|date": {col: val}}
    merged across all of them. Checkpoints each meeting as soon as it's
    successfully fetched (default on - the fetch-only mode always wants
    this so a later run can resume; combined mode also wants it since a
    dry run there no longer implies "don't remember what was fetched",
    only "don't implies write the CSV")."""
    n_ok = n_empty = n_fail = 0
    t0 = time.time()
    results = {}

    def _one(mid):
        try:
            return mid, fetch_meeting_result(mid)
        except Exception:
            return mid, ("ERROR", None)

    with ThreadPoolExecutor(max_workers=workers) as pool:
        futures = [pool.submit(_one, mid) for mid in meeting_ids]
        done = 0
        for fut in as_completed(futures):
            done += 1
            if done % 200 == 0:
                elapsed = time.time() - t0
                rate = done / elapsed if elapsed else 0
                eta = (len(meeting_ids) - done) / rate if rate else float("nan")
                print(f"  ... {done}/{len(meeting_ids)} meetings "
                      f"({elapsed:.0f}s, {len(results):,} runs collected, ETA {eta:.0f}s)")
            mid, (mr, deref) = fut.result()
            if mr == "ERROR":
                n_fail += 1
                continue
            if mr is None:
                n_empty += 1
                continue
            fields_by_run = extract_meeting_fields(mr, deref)
            if not fields_by_run:
                n_empty += 1
                continue
            n_ok += 1
            results.update(fields_by_run)
            if checkpoint_as_you_go:
                checkpoint.add(mid)
                CHECKPOINT_FILE.write_text("\n".join(sorted(checkpoint)))

    print(f"\nFetch done in {time.time()-t0:.0f}s.")
    print(f"  meetings: {n_ok:,} merged, {n_empty:,} not finalized/empty, {n_fail:,} failed")
    print(f"  {len(results):,} runs collected")
    return results


def merge_into_history(fields_by_key, commit, backup=True):
    """Load wpr_form_history.csv.gz FRESH (no caching across calls -
    this is the whole point, see module docstring), fill empty cells
    from fields_by_key keyed by "horse_id|date" (see
    extract_meeting_fields' docstring for why NOT run_id), write if
    commit. Returns (n_rows_touched, n_cells_filled)."""
    import toprate_daily as td
    fh_path = td.WPR_FORM_HISTORY_CSV
    print(f"Loading {fh_path} for merge ...")
    fh = pd.read_csv(fh_path, dtype={"run_id": str, "horse_id": str}, low_memory=False)
    print(f"  {len(fh):,} rows")

    for col in FILLABLE_COLS:
        if col not in fh.columns:
            fh[col] = None

    idx_by_key = {}
    dates = fh["date"].astype(str).str[:10]
    for idx, hid, d in zip(fh.index, fh["horse_id"].astype(str), dates):
        idx_by_key.setdefault(f"{hid}|{d}", []).append(idx)

    n_rows_touched = 0
    n_cells_filled = 0
    n_cells_skipped = 0
    skipped_examples = []
    for key, fields in fields_by_key.items():
        rows = idx_by_key.get(key)
        if not rows:
            continue  # this (horse_id, date) isn't in our existing history - never create rows
        for idx in rows:
            touched_this_row = False
            for col, v in fields.items():
                if v is None:
                    continue
                if not pd.isna(fh.at[idx, col]):
                    continue
                # Defensive: cap._scalar already normalises the known bad
                # value (a literal "NaN" string from the API) that crashed
                # a 1.3M-row run at scale before this was found - but a
                # single unanticipated value here must never sink an
                # 18-minute fetch again. Skip and count instead of raising.
                try:
                    fh.at[idx, col] = v
                    n_cells_filled += 1
                    touched_this_row = True
                except (TypeError, ValueError) as e:
                    n_cells_skipped += 1
                    if len(skipped_examples) < 10:
                        skipped_examples.append(f"{col}={v!r} ({e})")
            if touched_this_row:
                n_rows_touched += 1

    print(f"  {n_rows_touched:,} existing rows had at least one cell filled")
    if n_cells_skipped:
        print(f"  {n_cells_skipped:,} cells SKIPPED (bad value for the column's dtype), examples:")
        for ex in skipped_examples:
            print(f"    {ex}")
    print(f"  {n_cells_filled:,} individual cells filled")

    if not commit:
        print("DRY RUN - nothing written. Pass --commit to save for real.")
        return n_rows_touched, n_cells_filled

    if backup:
        bkp = f"{fh_path}.pre_bulk_backfill_{datetime.now():%Y%m%d_%H%M%S}"
        shutil.copy(fh_path, bkp)
        print(f"Backed up existing file to {bkp}")
    fh.to_csv(fh_path, index=False)
    print(f"Wrote {fh_path}")
    return n_rows_touched, n_cells_filled


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
    ap.add_argument("--fetch-only", metavar="OUT.json", default=None,
                     help="Fetch phase only: write results here, never touch the CSV")
    ap.add_argument("--merge-only", metavar="IN.json", default=None,
                     help="Merge phase only: read results from here, load the CSV fresh, "
                          "no network calls")
    args = ap.parse_args()

    if args.merge_only:
        with open(args.merge_only) as f:
            fields_by_run = json.load(f)
        print(f"Loaded {len(fields_by_run):,} runs from {args.merge_only}")
        merge_into_history(fields_by_run, commit=args.commit, backup=True)
        return

    if not (args.limit or args.since or args.all):
        sys.exit("Refusing to run with no scope: pass --limit N, --since DATE, "
                  "or --all explicitly. See the module docstring for examples.")

    _, fh = _load_history_for_scoping()
    meeting_ids, checkpoint = _select_meeting_ids(fh, args)
    print(f"  {len(meeting_ids):,} meetings to fetch")
    if not meeting_ids:
        print("Nothing to do.")
        return

    fields_by_run = run_fetch_phase(meeting_ids, args.workers, checkpoint)

    if args.fetch_only:
        with open(args.fetch_only, "w") as f:
            json.dump(fields_by_run, f)
        print(f"Wrote {len(fields_by_run):,} runs to {args.fetch_only}")
        return

    # Combined mode: merge immediately using the same process's fetch
    # results. Fine for a local manual run; the split mode above is what
    # the GitHub Action uses instead, precisely to avoid this window
    # between a long fetch and the eventual write going stale.
    merge_into_history(fields_by_run, commit=args.commit)


if __name__ == "__main__":
    main()
