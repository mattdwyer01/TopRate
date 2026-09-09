"""
backfill_race_results.py
--------------------------
Builds race_results.csv.gz: one row per runner per race, for EVERY
runner toprate.au's meetings/{id}/history bulk endpoint returns for a
finalized meeting, not just runners that already have a row in
wpr_form_history.csv.gz (see backfill_bulk_meeting_fields.py for that,
narrower, job).

WHY THIS EXISTS (as a separate file/script from backfill_bulk_meeting_fields.py)
  wpr_form_history.csv.gz only has a row for a runner if that horse was
  ITSELF later independently scraped via its own /runners/{id} page - so
  a race's other runners (rivals never independently captured) are
  simply missing. Confirmed by direct check against the real file (Sep
  2026): median runners-per-race_id is 2 (mean 3.3), far too sparse for
  cross-sectional work (track bias by rail/going, contested-pace
  reconstruction, "percentage of opposition beaten", margin-spread-as-
  race-strength), which needs most/all of a race's actual field, not
  whoever happened to also get independently captured.

  This script re-fetches the SAME meetings/{id}/history endpoint already
  proven live in backfill_bulk_meeting_fields.py, but keeps EVERY runner
  of EVERY race (not just ones matching an existing (horse_id, date) row
  in wpr_form_history.csv.gz) and additionally captures rail_position,
  which lives at the MEETING level and was never extracted anywhere
  before (confirmed absent from all 88 columns of wpr_form_history.csv.gz,
  Sep 2026 - see chat).

  Kept as its own file/script/checkpoint rather than folded into
  backfill_bulk_meeting_fields.py, which already completed a real
  20,648-meeting production run merging into wpr_form_history.csv.gz -
  safer not to touch a script that's already proven correct at scale for
  a different job. A small amount of fetch/auth boilerplate is
  deliberately duplicated rather than shared.

OUTPUTS
  race_results.csv.gz - one row per runner per race. Columns: race_id,
  meeting_id, date, rail_position, horse_id, horse, run_id, plus every
  field toprate_json_capture.py already knows the raw API key names for
  (CORE_COLS, SECT_MAP, HORSE_COLS, RUN_COLS, and the same per-runner
  extras EXTRA_COLS covers) - reused directly so this file's columns
  match wpr_form_history.csv.gz's naming instead of drifting into a
  parallel scheme.

  track_conditions_history.csv - a second, much smaller output from the
  SAME fetch pass: meetingHistory.tracks[].history[], TopRate's own
  compiled per-track rail/going timeline, independent of whether we have
  runner data for that particular meeting. Columns: track, date,
  rail_position, going_changes (raw JSON list string - schema not fully
  characterized yet, see --diagnose-one).

VERIFY BEFORE TRUSTING
  This script's field-name assumptions for the runner/race dicts (which
  key holds the horse's name, the exact rail-position/meetingHistory key
  names) come from an earlier live page dump made in this working
  session, not from a fresh check run by THIS script. This project has
  already hit several real bugs from trusting an assumption instead of
  checking (a run_id join-key bug, an exception-conflation bug - see
  backfill_bulk_meeting_fields.py's own history). Run
  `--diagnose-one MEETING_ID` first and read its output before trusting
  any real --limit/--since/--all run. It needs network + auth, so run it
  via the GitHub Action (see backfill_race_results.yml's diagnose input),
  same as everywhere else in this project that needs live credentials.

SAFETY
  - Dry-run by default. Pass --commit to actually write a CSV.
  - Never overwrites an existing (race_id, horse_id) row, only appends
    genuinely new ones - this file only grows, it is never corrected in
    place by this script.
  - Same fetch/merge split as backfill_bulk_meeting_fields.py, for the
    same reason: race_results.csv.gz isn't touched by anything else (so
    conflicts are far less likely than on wpr_form_history.csv.gz), but
    keeping the expensive network phase decoupled from the write phase
    is still the safer default given how long --all can run.
  - The fetch step checkpoints successfully-FETCHED meeting_ids (own
    checkpoint file, separate from backfill_bulk_meeting_fields.py's) so
    a long run can resume. A meeting whose result isn't finalized yet is
    NOT checkpointed, so it is retried on a later run.

USAGE (local, combined mode)
  python backfill_race_results.py --diagnose-one 144208
  python backfill_race_results.py --limit 20              # dry-run test
  python backfill_race_results.py --limit 20 --commit
  python backfill_race_results.py --since 2025-01-01 --commit
  python backfill_race_results.py --all --commit           # everything (hours)

USAGE (split mode, what the GitHub Action uses)
  python backfill_race_results.py --fetch-only out.json --since 2025-01-01
  python backfill_race_results.py --merge-only out.json --commit

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

CHECKPOINT_FILE = Path(__file__).parent / "backfill_race_results.checkpoint"
RACE_RESULTS_CSV = Path(__file__).parent / "race_results.csv.gz"
TRACK_HISTORY_CSV = Path(__file__).parent / "track_conditions_history.csv"
DEFAULT_WORKERS = 8

# CORE_COLS entries are raw API key names that are ALSO the column name
# (see toprate_json_capture.py: the thin feed and rich feed share these
# names already, so no src->col mapping is needed). Runner-level value
# wins; race-level is the fallback, since some of these (track, going,
# distance, raceNumber) plausibly live on the race dict rather than each
# runner's own dict on this bulk endpoint - unconfirmed either way until
# --diagnose-one is actually run, hence the fallback covers both shapes.
_CORE_KEYS = cap.CORE_COLS

# Per-runner extras EXTRA_COLS covers, expressed as {raw_key: col} since
# (unlike CORE_COLS) the raw API key and column name differ for these.
_EXTRA_RUNNER_KEYS = {
    "starters":        "field_size",
    "class":           "race_class",
    "isLetup":         "is_letup",
    "isSpell":         "is_spell",
    "blinkersOn":      "blinkers_on",
    "gearChanges":     "gear_changes",
    "commentsSteward": "comments_steward",
    "commentsVideo":   "comments_video",
    "timeLast600m":    "time_last600m",
    "jockey":          "jockey",
    "trainer":         "trainer",
    "isJumpout":       "is_jumpout",
}

# Horse- and run-level fields toprate_json_capture.py already extracts
# from the per-runner endpoint; reused here with the same runner-then-
# race fallback backfill_bulk_meeting_fields.py already established for
# these exact same source keys on this exact same bulk endpoint.
_FALLBACK_KEYS = {**cap.HORSE_COLS, **cap.RUN_COLS}


def _build_url(meeting_id):
    return f"{cap.WEB_BASE}/meetings/{meeting_id}/history/__data.json"


def fetch_meeting_full(meeting_id):
    """Fetch meetings/{id}/history and return (meeting_result,
    meeting_history, deref). meeting_result/meeting_history are None if
    the meeting isn't finalized yet or wasn't found; ("ERROR", None,
    None) on a hard failure after retries. Mirrors
    backfill_bulk_meeting_fields.fetch_meeting_result's auth/redirect/
    login-bounce handling exactly (same endpoint, same session), but
    also derefs meetingHistory from the same root node, which that
    function discards since its own job never needed it."""
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
            return None, None, None
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
            return None, None, None
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
            mh = deref(root.get("meetingHistory"))
            return (mr if isinstance(mr, dict) else None,
                    mh if isinstance(mh, dict) else None,
                    deref)
        return None, None, None
    # Retries exhausted without ever getting a usable response - a
    # genuine failure, distinct from a clean response whose
    # meetingResult is legitimately null (handled by the returns above).
    return "ERROR", None, None


def _runner_or_race(runner, race, key):
    v = runner.get(key)
    if v is None:
        v = race.get(key)
    return v


def extract_race_results(meeting_result, deref):
    """Return a list of row dicts, one per runner per race, for EVERY
    runner in this finalized meeting (see module docstring - this is
    the whole point, unlike backfill_bulk_meeting_fields.py's narrower
    job of only filling blanks on rows that already exist). rail_position
    is read once at the MEETING level and stamped onto every row from
    that meeting, since it applies to every race run that day."""
    rows = []
    meeting_date = deref(meeting_result.get("date"))
    meeting_id = cap._scalar(deref(meeting_result.get("meetingId")
                                    or meeting_result.get("id")))
    rail_position = cap._scalar(deref(meeting_result.get("railPosition")))
    races = deref(meeting_result.get("races"))
    if not isinstance(races, list) or not meeting_date:
        return rows
    meeting_date = str(meeting_date)[:10]

    for rp in races:
        race = deref(rp)
        if not isinstance(race, dict):
            continue
        race_id = cap._scalar(deref(race.get("raceId") or race.get("id")))
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
            row = {
                "race_id": race_id,
                "meeting_id": meeting_id,
                "date": meeting_date,
                "rail_position": rail_position,
                "horse_id": horse_id,
                "horse": cap._scalar(deref(runner.get("horse")
                                            or runner.get("horseName"))),
                "run_id": cap._scalar(deref(runner.get("runId"))),
            }
            sr = deref(runner.get("sectionalRating"))
            if isinstance(sr, dict):
                for src_key, col in cap.SECT_MAP.items():
                    v = deref(sr.get(src_key))
                    row[col] = v if isinstance(v, (int, float)) else None
            for key in _CORE_KEYS:
                row[key] = cap._scalar(deref(_runner_or_race(runner, race, key)))
            for src_key, col in _EXTRA_RUNNER_KEYS.items():
                row[col] = cap._scalar(deref(_runner_or_race(runner, race, src_key)))
            for src_key, col in _FALLBACK_KEYS.items():
                row[col] = cap._scalar(deref(_runner_or_race(runner, race, src_key)))
            rows.append(row)
    return rows


def extract_track_history(meeting_history, deref):
    """Return a list of {track, date, rail_position, going_changes} rows
    from meetingHistory.tracks[].history[] - TopRate's own compiled
    per-track rail/going timeline, independent of runner data. Cheap:
    no extra network cost, it's a small array already in the same
    payload extract_race_results reads. going_changes is stored as a
    raw JSON string; its own schema isn't characterized yet, see
    --diagnose-one."""
    rows = []
    if not isinstance(meeting_history, dict):
        return rows
    tracks = deref(meeting_history.get("tracks"))
    if not isinstance(tracks, list):
        return rows
    for tp in tracks:
        track = deref(tp)
        if not isinstance(track, dict):
            continue
        track_name = cap._scalar(deref(track.get("track") or track.get("name")))
        history = deref(track.get("history"))
        if not isinstance(history, list):
            continue
        for hp in history:
            h = deref(hp)
            if not isinstance(h, dict):
                continue
            date = deref(h.get("date"))
            rail = cap._scalar(deref(h.get("railPosition")))
            gc = deref(h.get("goingChanges"))
            going_changes = (json.dumps([cap._scalar(deref(x)) for x in gc])
                              if isinstance(gc, list) else None)
            rows.append({
                "track": track_name,
                "date": str(date)[:10] if date else None,
                "rail_position": rail,
                "going_changes": going_changes,
            })
    return rows


def diagnose_one(meeting_id):
    """Print the raw shape this script's field-name assumptions rely on,
    for one meeting, without writing anything. Run this via the Action
    (needs live credentials) before trusting any real fetch/merge."""
    print(f"Fetching meeting {meeting_id} for a raw schema dump ...\n")
    mr, mh, deref = fetch_meeting_full(meeting_id)
    if mr == "ERROR":
        sys.exit("Hard failure - see messages above.")
    if mr is None:
        sys.exit("meetingResult is null - not finalized yet, or meeting_id "
                  "not found. Try a different/older meeting_id.")

    print("=" * 70)
    print("meetingResult top-level keys:", list(mr.keys()))
    print("=" * 70)
    print("date:", mr.get("date"))
    print("railPosition:", mr.get("railPosition"), " <-- confirm this is the right key")
    print("meetingId/id:", mr.get("meetingId"), mr.get("id"))

    races = deref(mr.get("races"))
    if isinstance(races, list) and races:
        race = deref(races[0])
        print()
        print("race[0] keys:", list(race.keys()) if isinstance(race, dict) else race)
        if isinstance(race, dict):
            print("race[0].raceId/id:", race.get("raceId"), race.get("id"))
            runners = deref(race.get("runners"))
            if isinstance(runners, list) and runners:
                runner = deref(runners[0])
                print()
                print("race[0].runners[0] keys:",
                      list(runner.keys()) if isinstance(runner, dict) else runner)
                if isinstance(runner, dict):
                    print("  horseId:", runner.get("horseId"))
                    print("  horse/horseName:", runner.get("horse"), runner.get("horseName"))
                    print("  runId:", runner.get("runId"))
                    for k in ("weatherCondition", "weather", "trackWeather",
                              "temperature", "wind", "rainfall"):
                        if k in runner:
                            print(f"  {k} (weather candidate found on runner):", runner.get(k))
                for k in ("weatherCondition", "weather", "trackWeather",
                          "temperature", "wind", "rainfall"):
                    if k in race:
                        print(f"race[0].{k} (weather candidate found on race):", race.get(k))
    for k in ("weatherCondition", "weather", "trackWeather", "temperature"):
        if k in mr:
            print(f"meetingResult.{k} (weather candidate found on meeting):", mr.get(k))

    print()
    print("=" * 70)
    print("meetingHistory:", "present" if isinstance(mh, dict) else "ABSENT/None")
    print("=" * 70)
    if isinstance(mh, dict):
        print("meetingHistory top-level keys:", list(mh.keys()))
        tracks = deref(mh.get("tracks"))
        if isinstance(tracks, list) and tracks:
            print(f"  {len(tracks)} track(s)")
            t0 = deref(tracks[0])
            print("  tracks[0] keys:", list(t0.keys()) if isinstance(t0, dict) else t0)
            if isinstance(t0, dict):
                hist = deref(t0.get("history"))
                if isinstance(hist, list) and hist:
                    print(f"  tracks[0].history: {len(hist)} entries")
                    print("  tracks[0].history[0]:", deref(hist[0]))


def _select_meeting_ids(args):
    """Same scoping source as backfill_bulk_meeting_fields.py (every
    meeting_id/date pair on file), but this script's OWN checkpoint -
    deliberately independent, this is a different job writing a
    different file."""
    import backfill_bulk_meeting_fields as bbmf
    _, fh = bbmf._load_history_for_scoping()
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
    """Fetch every meeting_id and return (race_rows, track_rows).
    Checkpoints each meeting as soon as it's successfully fetched, same
    pattern as backfill_bulk_meeting_fields.py."""
    n_ok = n_empty = n_fail = 0
    t0 = time.time()
    race_rows = []
    track_rows = []

    def _one(mid):
        try:
            return mid, fetch_meeting_full(mid)
        except Exception:
            return mid, ("ERROR", None, None)

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
                      f"({elapsed:.0f}s, {len(race_rows):,} race rows collected, ETA {eta:.0f}s)")
            mid, (mr, mh, deref) = fut.result()
            if mr == "ERROR":
                n_fail += 1
                continue
            if mr is None:
                n_empty += 1
                continue
            rr = extract_race_results(mr, deref)
            tr = extract_track_history(mh, deref) if mh is not None else []
            if not rr:
                n_empty += 1
                continue
            n_ok += 1
            race_rows.extend(rr)
            track_rows.extend(tr)
            if checkpoint_as_you_go:
                checkpoint.add(mid)
                CHECKPOINT_FILE.write_text("\n".join(sorted(checkpoint)))

    print(f"\nFetch done in {time.time()-t0:.0f}s.")
    print(f"  meetings: {n_ok:,} merged, {n_empty:,} not finalized/empty, {n_fail:,} failed")
    print(f"  {len(race_rows):,} race-result rows, {len(track_rows):,} track-history rows collected")
    return race_rows, track_rows


def merge_race_results(race_rows, commit, backup=True):
    """Append genuinely new (race_id, horse_id) rows to race_results.csv.gz.
    Never overwrites an existing row - this file only grows."""
    if RACE_RESULTS_CSV.exists():
        existing = pd.read_csv(RACE_RESULTS_CSV, low_memory=False,
                                dtype={"race_id": str, "horse_id": str, "meeting_id": str})
        print(f"  existing race_results.csv.gz: {len(existing):,} rows")
    else:
        existing = pd.DataFrame()
        print("  no existing race_results.csv.gz - will create one")

    new = pd.DataFrame(race_rows)
    if new.empty:
        print("  no race-result rows to merge")
        return 0
    new["race_id"] = new["race_id"].astype(str)
    new["horse_id"] = new["horse_id"].astype(str)

    if not existing.empty:
        existing_keys = set(zip(existing["race_id"].astype(str), existing["horse_id"].astype(str)))
        before = len(new)
        new = new[~new.apply(lambda r: (r["race_id"], r["horse_id"]) in existing_keys, axis=1)]
        print(f"  {before - len(new):,} rows already present, skipped")

    print(f"  {len(new):,} genuinely new rows")
    if new.empty:
        return 0

    if not commit:
        print("DRY RUN - nothing written. Pass --commit to save for real.")
        return len(new)

    if backup and RACE_RESULTS_CSV.exists():
        bkp = f"{RACE_RESULTS_CSV}.pre_merge_{datetime.now():%Y%m%d_%H%M%S}"
        shutil.copy(RACE_RESULTS_CSV, bkp)
        print(f"  backed up existing file to {bkp}")

    combined = pd.concat([existing, new], ignore_index=True) if not existing.empty else new
    combined.to_csv(RACE_RESULTS_CSV, index=False)
    print(f"  wrote {RACE_RESULTS_CSV} ({len(combined):,} total rows)")
    return len(new)


def merge_track_history(track_rows, commit, backup=True):
    """Append genuinely new (track, date) rows to track_conditions_history.csv."""
    if TRACK_HISTORY_CSV.exists():
        existing = pd.read_csv(TRACK_HISTORY_CSV, low_memory=False)
        print(f"  existing track_conditions_history.csv: {len(existing):,} rows")
    else:
        existing = pd.DataFrame()
        print("  no existing track_conditions_history.csv - will create one")

    new = pd.DataFrame(track_rows)
    if new.empty:
        print("  no track-history rows to merge")
        return 0

    if not existing.empty:
        existing_keys = set(zip(existing["track"].astype(str), existing["date"].astype(str)))
        before = len(new)
        new = new[~new.apply(lambda r: (str(r["track"]), str(r["date"])) in existing_keys, axis=1)]
        print(f"  {before - len(new):,} rows already present, skipped")

    print(f"  {len(new):,} genuinely new rows")
    if new.empty:
        return 0

    if not commit:
        print("DRY RUN - nothing written. Pass --commit to save for real.")
        return len(new)

    if backup and TRACK_HISTORY_CSV.exists():
        bkp = f"{TRACK_HISTORY_CSV}.pre_merge_{datetime.now():%Y%m%d_%H%M%S}"
        shutil.copy(TRACK_HISTORY_CSV, bkp)
        print(f"  backed up existing file to {bkp}")

    combined = pd.concat([existing, new], ignore_index=True) if not existing.empty else new
    combined.to_csv(TRACK_HISTORY_CSV, index=False)
    print(f"  wrote {TRACK_HISTORY_CSV} ({len(combined):,} total rows)")
    return len(new)


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                  formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--diagnose-one", metavar="MEETING_ID", default=None,
                     help="Print the raw schema for one meeting and exit. "
                          "Run this first (see module docstring).")
    ap.add_argument("--limit", type=int, default=None,
                     help="Only process the first N meetings (most recent first)")
    ap.add_argument("--since", default=None,
                     help="Only meetings on/after this date (YYYY-MM-DD)")
    ap.add_argument("--all", action="store_true",
                     help="Process every meeting on file (hours, ~20,000+ calls)")
    ap.add_argument("--commit", action="store_true",
                     help="Actually write the CSVs (default: dry-run, nothing saved)")
    ap.add_argument("--workers", type=int, default=DEFAULT_WORKERS)
    ap.add_argument("--fetch-only", metavar="OUT.json", default=None,
                     help="Fetch phase only: write results here, never touch the CSVs")
    ap.add_argument("--merge-only", metavar="IN.json", default=None,
                     help="Merge phase only: read results from here, no network calls")
    args = ap.parse_args()

    if args.diagnose_one:
        diagnose_one(args.diagnose_one)
        return

    if args.merge_only:
        with open(args.merge_only) as f:
            payload = json.load(f)
        race_rows = payload.get("race_rows", [])
        track_rows = payload.get("track_rows", [])
        print(f"Loaded {len(race_rows):,} race rows, {len(track_rows):,} track rows "
              f"from {args.merge_only}")
        merge_race_results(race_rows, commit=args.commit, backup=True)
        merge_track_history(track_rows, commit=args.commit, backup=True)
        return

    if not (args.limit or args.since or args.all):
        sys.exit("Refusing to run with no scope: pass --limit N, --since DATE, "
                  "or --all explicitly. See the module docstring for examples.")

    meeting_ids, checkpoint = _select_meeting_ids(args)
    print(f"  {len(meeting_ids):,} meetings to fetch")
    if not meeting_ids:
        print("Nothing to do.")
        return

    race_rows, track_rows = run_fetch_phase(meeting_ids, args.workers, checkpoint)

    if args.fetch_only:
        with open(args.fetch_only, "w") as f:
            json.dump({"race_rows": race_rows, "track_rows": track_rows}, f)
        print(f"Wrote {len(race_rows):,} race rows, {len(track_rows):,} track rows "
              f"to {args.fetch_only}")
        return

    # Combined mode: merge immediately using this same process's fetch
    # results. Fine for a local manual run; the split mode above is what
    # the GitHub Action uses, same reasoning as backfill_bulk_meeting_fields.py.
    merge_race_results(race_rows, commit=args.commit)
    merge_track_history(track_rows, commit=args.commit)


if __name__ == "__main__":
    main()
