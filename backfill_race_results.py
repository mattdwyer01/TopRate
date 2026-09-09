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
  race_results_YYYY.csv.gz (one file per year, split on the row's own
  "date") - one row per runner per race. Columns: race_id, meeting_id,
  date, rail_position, horse_id, horse, run_id, plus every field
  toprate_json_capture.py already knows the raw API key names for
  (CORE_COLS, SECT_MAP, HORSE_COLS, RUN_COLS, and the same per-runner
  extras EXTRA_COLS covers) - reused directly so this file's columns
  match wpr_form_history.csv.gz's naming instead of drifting into a
  parallel scheme.

  Split by year (not one file) because a real --all run (Sep 2026, see
  chat) produced 1,344,089 rows that compressed to 160MB - over
  GitHub's 100MB hard file limit, and the push was rejected outright
  (GH001). At ~124 bytes/row compressed (matching wpr_form_history.csv.gz's
  own per-row density - this isn't unusually bloated, it's simply ~4x
  the ROWS of that file, since it keeps every runner in every race, not
  just independently-scraped horses), one file per year lands around
  15-20MB each given the actual per-year meeting count on file, with
  large headroom before any single year could approach the limit again.

  track_codes.csv - a second, tiny output from the SAME fetch pass:
  meetingResult.tracks[], which turned out (via --diagnose-one, Sep
  2026) to be just a flat {track, trackId, trackCode} identifier for
  the meeting's own track, NOT the richer per-track rail/going timeline
  originally hoped for (an earlier live page dump this session, on a
  different route, suggested a "meetingHistory.tracks[].history[]" with
  127-230 dated entries per track - that shape does not exist on THIS
  endpoint's meetingResult node; may live in a different SvelteKit node
  of the same response, not pursued further since it turned out to be
  unnecessary - track bias by rail/going is already fully answerable
  from race_results.csv.gz itself: group by (track, going, rail_position)
  across every race this script backfills, per the ledger's own "track
  bias is a lookup against similar past meetings" framing). Kept anyway
  as a cheap track-name/id/code reference table, deduped by track name.

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
    genuinely new ones - these files only grow, never corrected in
    place by this script.
  - Same fetch/merge split as backfill_bulk_meeting_fields.py, for the
    same reason: race_results_*.csv.gz isn't touched by anything else
    (so conflicts are far less likely than on wpr_form_history.csv.gz),
    but keeping the expensive network phase decoupled from the write
    phase is still the safer default given how long --all can run.
  - The checkpoint is written ONLY after a successful --commit merge
    (never during fetch). Originally checkpointed as-you-fetched instead
    (matching backfill_bulk_meeting_fields.py's own documented,
    deliberately-left-unfixed gap) - that cost a real incident here (Sep
    2026, see chat): the 100MB-limit push failure above left 19,295
    successfully-FETCHED meetings marked "done" in a pushed checkpoint
    even though their data never reached any CSV, and the fetch JSON
    only ever existed on the ephemeral Action runner - permanently lost,
    not recoverable. Fixed properly this time rather than re-documented
    as a known gap: checkpoint_meeting_ids()/write_checkpoint() run
    after merge_race_results succeeds, using the meeting_ids actually
    present in the merged rows, and are committed+pushed in the SAME
    git operation as the CSVs (see backfill_race_results.yml) - so a
    checkpoint entry existing always means its data is durably on disk
    in git, never just fetched-but-not-yet-saved.

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
TRACK_CODES_CSV = Path(__file__).parent / "track_codes.csv"
DEFAULT_WORKERS = 8


def _race_results_path(year):
    """race_results_YYYY.csv.gz for the given year (int or str). See
    module OUTPUTS docstring for why this is split by year rather than
    one file."""
    return Path(__file__).parent / f"race_results_{year}.csv.gz"


def _fetch_sibling_path(base_path, key):
    """<base>.<key>.json next to base_path (e.g. base "out.json", key
    "2019" or "track" -> "out.2019.json"). Used to split the fetch
    phase's output into one file per year (see main()'s --fetch-only/
    --merge-only handling for why: a single JSON holding all ~1.3M rows
    at once made --merge-only's json.load() + pd.DataFrame() peak
    memory large enough to risk OOM on a standard GitHub Actions
    runner - confirmed as the likely cause of an unusually slow/possibly
    stalled real --all run, Sep 2026, see chat)."""
    base = Path(base_path)
    stem = base.name[:-len(base.suffix)] if base.suffix else base.name
    return base.parent / f"{stem}.{key}{base.suffix}"

# CORE_COLS entries are raw API key names that are ALSO the column name on
# the per-runner __data.json endpoint. Confirmed via --diagnose-one (Sep
# 2026, see chat) that this bulk endpoint does NOT share that naming for
# every field: race[0] carries "number"/"name", not "raceNumber"/
# "raceName", and there is no "trackCode" key at all (a "trackId" exists
# instead, a different concept - not mapped here rather than guess wrong).
# Left as cap.CORE_COLS anyway (not worth a parallel constant for two
# misses) - raceNumber/race_name just come back None from this path,
# same as any other field genuinely absent from a given payload. Runner-
# level value wins; race level, then meeting level, are the fallback
# (see _lookup) - going/track/trackGrading/distance/weightRestriction/
# jockeyRestriction/positionSettled/wpr/weightCarried/barrier/margins/
# positions/raceShape*/priceStarting are all confirmed present at
# runner-and/or-race level by that same diagnose run.
_CORE_KEYS = cap.CORE_COLS

# Per-runner extras EXTRA_COLS covers, expressed as {raw_key: col} since
# (unlike CORE_COLS) the raw API key and column name differ for these.
# "starters" (intended for field_size) confirmed ABSENT anywhere on this
# endpoint by --diagnose-one - field_size is instead computed directly as
# len(runners) in extract_race_results, not looked up here.
_EXTRA_RUNNER_KEYS = {
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
    deref). meeting_result is None if the meeting isn't finalized yet or
    wasn't found; ("ERROR", None) on a hard failure after retries.
    Mirrors backfill_bulk_meeting_fields.fetch_meeting_result's auth/
    redirect/login-bounce handling exactly (same endpoint, same
    session). Originally also derefed a separate "meetingHistory" node
    for the per-track rail/going timeline - removed once --diagnose-one
    (Sep 2026, see chat) showed that wrapper doesn't exist on this
    endpoint; "tracks" sits directly on meeting_result itself, read from
    there by extract_track_codes."""
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
    # Retries exhausted without ever getting a usable response - a
    # genuine failure, distinct from a clean response whose
    # meetingResult is legitimately null (handled by the returns above).
    return "ERROR", None


def _lookup(runner, race, meeting_result, key):
    """Runner value wins; race is the fallback; meeting_result is the
    fallback after that. Confirmed necessary, not just defensive: venue
    lives ONLY on meetingResult (absent from both race and runner) per
    --diagnose-one (Sep 2026, see chat) - a 2-level fallback would have
    silently dropped it on every row."""
    v = runner.get(key)
    if v is None:
        v = race.get(key)
    if v is None:
        v = meeting_result.get(key)
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
        # field_size: no "starters" (or any other) key carries this on
        # this bulk endpoint, confirmed by --diagnose-one (Sep 2026) -
        # computed directly from the runner list actually returned, once
        # per race, rather than looked up.
        field_size = len(runners)
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
                "field_size": field_size,
            }
            sr = deref(runner.get("sectionalRating"))
            if isinstance(sr, dict):
                for src_key, col in cap.SECT_MAP.items():
                    v = deref(sr.get(src_key))
                    row[col] = v if isinstance(v, (int, float)) else None
            for key in _CORE_KEYS:
                row[key] = cap._scalar(deref(_lookup(runner, race, meeting_result, key)))
            for src_key, col in _EXTRA_RUNNER_KEYS.items():
                row[col] = cap._scalar(deref(_lookup(runner, race, meeting_result, src_key)))
            for src_key, col in _FALLBACK_KEYS.items():
                row[col] = cap._scalar(deref(_lookup(runner, race, meeting_result, src_key)))
            rows.append(row)
    return rows


def extract_track_codes(meeting_result, deref):
    """Return a list of {track, track_id, track_code} rows from
    meetingResult.tracks[]. Originally hoped this held a per-track rail/
    going timeline (see module OUTPUTS docstring for why that turned out
    to be wrong) - confirmed by --diagnose-one (Sep 2026, see chat) to
    just be a flat identifier: meetingResult.tracks[0] = {'track':
    'Hawkesbury', 'trackId': 246, 'trackCode': 'HAWKE'}, no 'history'
    key at all. Kept as a cheap track-name/id/code reference table
    rather than dropped entirely - it's free, already in the same
    payload extract_race_results reads."""
    rows = []
    if not isinstance(meeting_result, dict):
        return rows
    tracks = deref(meeting_result.get("tracks"))
    if not isinstance(tracks, list):
        return rows
    for tp in tracks:
        track = deref(tp)
        if not isinstance(track, dict):
            continue
        rows.append({
            "track": cap._scalar(deref(track.get("track"))),
            "track_id": cap._scalar(deref(track.get("trackId"))),
            "track_code": cap._scalar(deref(track.get("trackCode"))),
        })
    return rows


def diagnose_one(meeting_id):
    """Print the raw shape this script's field-name assumptions rely on,
    for one meeting, without writing anything. Run this via the Action
    (needs live credentials) before trusting any real fetch/merge."""
    print(f"Fetching meeting {meeting_id} for a raw schema dump ...\n")
    mr, deref = fetch_meeting_full(meeting_id)
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
                    print("  horseId:", deref(runner.get("horseId")))
                    print("  horse/horseName:", deref(runner.get("horse")),
                          deref(runner.get("horseName")))
                    print("  runId:", deref(runner.get("runId")))
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
    print("meetingResult.tracks:")
    print("=" * 70)
    tracks = deref(mr.get("tracks"))
    if not isinstance(tracks, list) or not tracks:
        print("  ABSENT/empty - meetingResult has no usable 'tracks' key")
    else:
        print(f"  {len(tracks)} track(s)")
        t0 = deref(tracks[0])
        print("  tracks[0] keys:", list(t0.keys()) if isinstance(t0, dict) else t0)
        if isinstance(t0, dict):
            print("  tracks[0] (deref'd, non-list/dict fields):",
                  {k: deref(v) for k, v in t0.items()
                   if not isinstance(deref(v), (list, dict))})
            hist = deref(t0.get("history"))
            if isinstance(hist, list) and hist:
                print(f"  tracks[0].history: {len(hist)} entries")
                h0 = deref(hist[0])
                print("  tracks[0].history[0] keys:",
                      list(h0.keys()) if isinstance(h0, dict) else h0)
                if isinstance(h0, dict):
                    print("  tracks[0].history[0] (deref'd, non-list/dict fields):",
                          {k: deref(v) for k, v in h0.items()
                           if not isinstance(deref(v), (list, dict))})
                    for k, v in h0.items():
                        rv = deref(v)
                        if isinstance(rv, list):
                            print(f"  tracks[0].history[0].{k}: list, {len(rv)} items, "
                                  f"first: {deref(rv[0]) if rv else None}")
            else:
                print("  tracks[0] has no usable 'history' list")


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


def run_fetch_phase(meeting_ids, workers):
    """Fetch every meeting_id and return (race_rows, track_rows). Does
    NOT touch the checkpoint - checkpointing happens only after a
    successful merge (see write_checkpoint), not here. See the module
    SAFETY docstring for why (a real incident, Sep 2026)."""
    n_ok = n_empty = n_fail = 0
    t0 = time.time()
    race_rows = []
    track_rows = []

    def _one(mid):
        try:
            return mid, fetch_meeting_full(mid)
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
                      f"({elapsed:.0f}s, {len(race_rows):,} race rows collected, ETA {eta:.0f}s)")
            mid, (mr, deref) = fut.result()
            if mr == "ERROR":
                n_fail += 1
                continue
            if mr is None:
                n_empty += 1
                continue
            rr = extract_race_results(mr, deref)
            tr = extract_track_codes(mr, deref)
            if not rr:
                n_empty += 1
                continue
            n_ok += 1
            race_rows.extend(rr)
            track_rows.extend(tr)

    print(f"\nFetch done in {time.time()-t0:.0f}s.")
    print(f"  meetings: {n_ok:,} merged, {n_empty:,} not finalized/empty, {n_fail:,} failed")
    print(f"  {len(race_rows):,} race-result rows, {len(track_rows):,} track-history rows collected")
    return race_rows, track_rows


def checkpoint_meeting_ids(race_rows):
    """The set of meeting_ids actually represented in race_rows, as
    strings - used to checkpoint only AFTER those rows are confirmed
    merged, never at fetch time (see module SAFETY docstring)."""
    return {str(r["meeting_id"]) for r in race_rows if r.get("meeting_id") is not None}


def write_checkpoint(meeting_ids):
    """Union meeting_ids into CHECKPOINT_FILE on disk. Call this ONLY
    after merge_race_results has successfully written the corresponding
    rows - never before, never speculatively."""
    if not meeting_ids:
        return
    existing = set()
    if CHECKPOINT_FILE.exists():
        existing = set(CHECKPOINT_FILE.read_text().split())
    combined = existing | {str(m) for m in meeting_ids}
    CHECKPOINT_FILE.write_text("\n".join(sorted(combined)))
    print(f"  checkpoint: {len(combined) - len(existing):,} new meeting_ids added "
          f"({len(combined):,} total)")


def merge_race_results(race_rows, commit, backup=True):
    """Append genuinely new (race_id, horse_id) rows to
    race_results_YYYY.csv.gz, one file per year (parsed from each row's
    own "date" - see module OUTPUTS docstring for why split by year).
    Never overwrites an existing row - these files only grow. Returns
    total new rows written across all years."""
    new_all = pd.DataFrame(race_rows)
    if new_all.empty:
        print("  no race-result rows to merge")
        return 0
    new_all["race_id"] = new_all["race_id"].astype(str)
    new_all["horse_id"] = new_all["horse_id"].astype(str)
    new_all["year"] = new_all["date"].astype(str).str[:4]

    total_new = 0
    for year, new in new_all.groupby("year"):
        new = new.drop(columns=["year"])
        path = _race_results_path(year)
        if path.exists():
            existing = pd.read_csv(path, low_memory=False,
                                    dtype={"race_id": str, "horse_id": str, "meeting_id": str})
            print(f"  existing {path.name}: {len(existing):,} rows")
        else:
            existing = pd.DataFrame()
            print(f"  no existing {path.name} - will create one")

        if not existing.empty:
            existing_keys = set(zip(existing["race_id"].astype(str), existing["horse_id"].astype(str)))
            before = len(new)
            new = new[~new.apply(lambda r: (r["race_id"], r["horse_id"]) in existing_keys, axis=1)]
            print(f"  {year}: {before - len(new):,} rows already present, skipped")

        print(f"  {year}: {len(new):,} genuinely new rows")
        if new.empty:
            continue
        total_new += len(new)

        if not commit:
            continue

        if backup and path.exists():
            bkp = f"{path}.pre_merge_{datetime.now():%Y%m%d_%H%M%S}"
            shutil.copy(path, bkp)
            print(f"  backed up existing file to {bkp}")

        combined = pd.concat([existing, new], ignore_index=True) if not existing.empty else new
        combined.to_csv(path, index=False)
        print(f"  wrote {path} ({len(combined):,} total rows)")

    if not commit and total_new:
        print("DRY RUN - nothing written. Pass --commit to save for real.")
    return total_new


def merge_track_codes(track_rows, commit, backup=True):
    """Append genuinely new track rows to track_codes.csv, deduped by
    track name (a track's id/code is static, unlike a rail/going
    timeline - one row per distinct track is all this file ever needs)."""
    if TRACK_CODES_CSV.exists():
        existing = pd.read_csv(TRACK_CODES_CSV, low_memory=False)
        print(f"  existing track_codes.csv: {len(existing):,} rows")
    else:
        existing = pd.DataFrame()
        print("  no existing track_codes.csv - will create one")

    new = pd.DataFrame(track_rows)
    if new.empty:
        print("  no track rows to merge")
        return 0
    new = new.drop_duplicates(subset=["track"])

    if not existing.empty:
        existing_keys = set(existing["track"].astype(str))
        before = len(new)
        new = new[~new["track"].astype(str).isin(existing_keys)]
        print(f"  {before - len(new):,} rows already present, skipped")

    print(f"  {len(new):,} genuinely new rows")
    if new.empty:
        return 0

    if not commit:
        print("DRY RUN - nothing written. Pass --commit to save for real.")
        return len(new)

    if backup and TRACK_CODES_CSV.exists():
        bkp = f"{TRACK_CODES_CSV}.pre_merge_{datetime.now():%Y%m%d_%H%M%S}"
        shutil.copy(TRACK_CODES_CSV, bkp)
        print(f"  backed up existing file to {bkp}")

    combined = pd.concat([existing, new], ignore_index=True) if not existing.empty else new
    combined.to_csv(TRACK_CODES_CSV, index=False)
    print(f"  wrote {TRACK_CODES_CSV} ({len(combined):,} total rows)")
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
        year_files = sorted(Path(args.merge_only).parent.glob(
            f"{_fetch_sibling_path(args.merge_only, '*').name}"))
        # The glob above also matches the "track" sibling - split it out.
        track_file = _fetch_sibling_path(args.merge_only, "track")
        year_files = [p for p in year_files if p != track_file]
        if not year_files:
            sys.exit(f"No per-year sibling files found next to {args.merge_only} "
                      "(expected e.g. <stem>.2024.json) - was this fetched with "
                      "the current --fetch-only, which writes one file per year?")

        all_meeting_ids = set()
        total_race_rows = 0
        for yf in year_files:
            with open(yf) as f:
                race_rows = json.load(f).get("race_rows", [])
            total_race_rows += len(race_rows)
            print(f"Loaded {len(race_rows):,} race rows from {yf.name}")
            merge_race_results(race_rows, commit=args.commit, backup=True)
            if args.commit:
                all_meeting_ids |= checkpoint_meeting_ids(race_rows)
            del race_rows  # free this year's rows before loading the next

        track_rows = []
        if track_file.exists():
            with open(track_file) as f:
                track_rows = json.load(f).get("track_rows", [])
        print(f"Loaded {len(track_rows):,} track rows from {track_file.name}")
        merge_track_codes(track_rows, commit=args.commit, backup=True)

        print(f"Merge done: {total_race_rows:,} race rows across {len(year_files)} year file(s)")
        if args.commit:
            write_checkpoint(all_meeting_ids)
        return

    if not (args.limit or args.since or args.all):
        sys.exit("Refusing to run with no scope: pass --limit N, --since DATE, "
                  "or --all explicitly. See the module docstring for examples.")

    meeting_ids, checkpoint = _select_meeting_ids(args)
    print(f"  {len(meeting_ids):,} meetings to fetch")
    if not meeting_ids:
        print("Nothing to do.")
        return

    race_rows, track_rows = run_fetch_phase(meeting_ids, args.workers)

    if args.fetch_only:
        by_year = {}
        for r in race_rows:
            by_year.setdefault(str(r["date"])[:4], []).append(r)
        for year, rows in sorted(by_year.items()):
            yf = _fetch_sibling_path(args.fetch_only, year)
            with open(yf, "w") as f:
                json.dump({"race_rows": rows}, f)
            print(f"  wrote {len(rows):,} race rows to {yf.name}")
        track_file = _fetch_sibling_path(args.fetch_only, "track")
        with open(track_file, "w") as f:
            json.dump({"track_rows": track_rows}, f)
        print(f"Wrote {len(race_rows):,} race rows across {len(by_year)} year file(s), "
              f"{len(track_rows):,} track rows to {track_file.name}")
        return

    # Combined mode: merge immediately using this same process's fetch
    # results. Fine for a local manual run; the split mode above is what
    # the GitHub Action uses, same reasoning as backfill_bulk_meeting_fields.py.
    merge_race_results(race_rows, commit=args.commit)
    merge_track_codes(track_rows, commit=args.commit)
    if args.commit:
        write_checkpoint(checkpoint_meeting_ids(race_rows))


if __name__ == "__main__":
    main()
