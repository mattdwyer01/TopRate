"""
puntingform_ingest.py - Daily Punting Form Pro ingest, calibrated to actual API.

Pulls meetings, fields (runners), and ratings from the PF API into local CSVs
that sit alongside (NOT merged with) the TopRate database. Once we have ~7
days of data, run a correlation analysis to see whether PF AI Rank,
trainer/jockey A2E, or sectionals add independent signal value.

Schedule: run once per day after toprate_daily.py.

Usage:
    python puntingform_ingest.py                # today
    python puntingform_ingest.py --date 2026-05-10
    python puntingform_ingest.py --backfill 7   # last 7 days

API key: env var PUNTINGFORM_API_KEY or pf_api.key file.

Calibrated to actual PF v2 API response shape (verified 2026-05-10).
"""

from __future__ import annotations
import argparse
import csv
import json
import os
import sys
import time
from datetime import datetime, timedelta
from pathlib import Path
from typing import Any
import requests

API_BASE_FORM    = "https://api.puntingform.com.au/v2/form"
API_BASE_RATINGS = "https://api.puntingform.com.au/v2/Ratings"
API_BASE = API_BASE_FORM  # back-compat default for /form/ endpoints
SCRIPT_DIR = Path(__file__).parent
PF_DATA_DIR = SCRIPT_DIR / "puntingform_data"
PF_DATA_DIR.mkdir(exist_ok=True)
RAW_DIR = PF_DATA_DIR / "raw"
RAW_DIR.mkdir(exist_ok=True)

MEETINGS_CSV   = PF_DATA_DIR / "pf_meetings.csv"
RUNNERS_CSV    = PF_DATA_DIR / "pf_runners.csv"
RATINGS_CSV    = PF_DATA_DIR / "pf_ratings.csv"
SECTIONALS_CSV = PF_DATA_DIR / "pf_sectionals.csv"

REQUEST_DELAY_SEC = 1.2  # PF docs require 1s minimum between calls
TAB_PRIZE_MIN = 20000     # match TopRate filter for non-TAB bush meetings

# Tier-gated endpoints. Pro subscribers get MeetingRatings but NOT MeetingSectionals
# (which is Modeller tier only - returns 403 "You do not have access to this API").
# Set True if you upgrade or if PF changes the tier gating.
PULL_SECTIONALS = False


def get_api_key() -> str:
    key = os.environ.get("PUNTINGFORM_API_KEY")
    if key:
        return key.strip()
    key_file = SCRIPT_DIR / "pf_api.key"
    if key_file.exists():
        return key_file.read_text().strip()
    print("ERROR: No Punting Form API key found.")
    print("  Set PUNTINGFORM_API_KEY environment variable, or")
    print(f"  Create file {key_file} containing your key on one line.")
    sys.exit(1)


def pf_get(endpoint: str, params: dict[str, Any]) -> Any:
    """GET endpoint, unwrap payLoad envelope, return data or None.

    `endpoint` can be a short name (resolved against API_BASE_FORM) or a full URL.
    """
    full = dict(params)
    full["apiKey"] = get_api_key()
    url = endpoint if endpoint.startswith("http") else f"{API_BASE_FORM}/{endpoint}"
    try:
        r = requests.get(url, params=full,
                         headers={"accept": "application/json"}, timeout=30)
        if r.status_code != 200:
            print(f"  {url} -> {r.status_code}: {r.text[:200]}")
            return None
        data = r.json()
        if isinstance(data, dict) and "payLoad" in data:
            if data.get("error") or data.get("errors"):
                print(f"  {url} API error: {data.get('error')} {data.get('errors')}")
                return None
            return data["payLoad"]
        return data
    except (requests.RequestException, ValueError) as e:
        print(f"  {url} request error: {e}")
        return None
    finally:
        time.sleep(REQUEST_DELAY_SEC)


def append_rows(path: Path, rows: list[dict], key_cols: list[str]) -> int:
    """Append rows to CSV, dedup by key_cols. Re-writes file to handle column drift."""
    if not rows:
        return 0
    existing_rows: list[dict] = []
    existing_keys: set[tuple] = set()
    if path.exists():
        with path.open("r", newline="", encoding="utf-8") as f:
            for row in csv.DictReader(f):
                existing_rows.append(row)
                existing_keys.add(tuple(str(row.get(k, "")) for k in key_cols))
    new_rows = [r for r in rows
                if tuple(str(r.get(k, "")) for k in key_cols) not in existing_keys]
    if not new_rows:
        return 0
    # Build column union with sensible ordering: existing first, then new fields
    all_fields: list[str] = []
    seen: set[str] = set()
    if existing_rows:
        for c in existing_rows[0].keys():
            if c not in seen:
                all_fields.append(c)
                seen.add(c)
    for row in new_rows:
        for c in row.keys():
            if c not in seen:
                all_fields.append(c)
                seen.add(c)
    with path.open("w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=all_fields, extrasaction="ignore")
        w.writeheader()
        for row in existing_rows:
            w.writerow(row)
        for row in new_rows:
            w.writerow(row)
    return len(new_rows)


def flatten_runner(runner: dict, race: dict, meeting: dict, date_iso: str) -> dict:
    """Pull useful fields from a deeply nested PF runner object into a flat row.

    PF returns ~30 nested objects per runner (going records, group records,
    A2E performance, etc). We flatten the high-value ones; rest are in raw JSON.
    """
    track = meeting.get("track") or {}
    trainer = runner.get("trainer") or {}
    jockey = runner.get("jockey") or {}

    def a2e(key: str) -> dict:
        d = runner.get(key) or {}
        return {
            f"{key}_a2e":     d.get("a2E"),
            f"{key}_pot":     d.get("poT"),
            f"{key}_sr":      d.get("strikeRate"),
            f"{key}_wins":    d.get("wins"),
            f"{key}_runners": d.get("runners"),
        }

    def rec(key: str, prefix: str) -> dict:
        d = runner.get(key) or {}
        return {
            f"{prefix}_starts":  d.get("starts"),
            f"{prefix}_firsts":  d.get("firsts"),
            f"{prefix}_seconds": d.get("seconds"),
            f"{prefix}_thirds":  d.get("thirds"),
        }

    row = {
        # Match keys (top of file order to make the CSV readable)
        "_pf_date":         date_iso,
        "_pf_meeting_id":   meeting.get("meetingId"),
        "_pf_venue":        track.get("name"),
        "_pf_state":        track.get("state"),
        "_pf_surface":      track.get("surface"),
        "race_id":          race.get("raceId"),
        "race_number":      race.get("number"),
        "race_name":        race.get("name"),
        "race_distance":    race.get("distance"),
        "race_class":       race.get("raceClass"),
        "race_prize":       race.get("prizeMoney"),
        "race_start_time":  race.get("startTime"),
        # Runner core
        "runner_id":        runner.get("runnerId"),
        "horse":            runner.get("name"),
        "tab_no":           runner.get("tabNo"),
        "barrier":          runner.get("barrier"),
        "weight":           runner.get("weight"),
        "weight_total":     runner.get("weightTotal"),
        "handicap":         runner.get("handicap"),
        "age":              runner.get("age"),
        "sex":              runner.get("sex"),
        "country":          runner.get("country"),
        "trainer_id":       trainer.get("trainerId"),
        "trainer":          trainer.get("fullName"),
        "trainer_loc":      trainer.get("location"),
        "jockey_id":        jockey.get("jockeyId"),
        "jockey":           jockey.get("fullName"),
        "jockey_claim":     jockey.get("claim"),
        "jockey_apprentice": jockey.get("isApprentice"),
        "price_sp":         runner.get("priceSP"),
        "last10":           runner.get("last10"),
        "win_pct":          runner.get("winPct"),
        "place_pct":        runner.get("placePct"),
        "career_starts":    runner.get("careerStarts"),
        "career_wins":      runner.get("careerWins"),
        "prize_money_total": runner.get("prizeMoney"),
        "emergency":        runner.get("emergencyIndicator"),
        "gear_changes":     runner.get("gearChanges"),
        "prep_runs":        runner.get("prepRuns"),
        "form_id":          runner.get("formId"),
    }
    row.update(rec("trackRecord", "track_rec"))
    row.update(rec("distanceRecord", "dist_rec"))
    row.update(rec("trackDistRecord", "trackdist_rec"))
    row.update(rec("goodRecord", "good_rec"))
    row.update(rec("softRecord", "soft_rec"))
    row.update(rec("heavyRecord", "heavy_rec"))
    row.update(rec("firstUpRecord", "first_up"))
    row.update(rec("secondUpRecord", "second_up"))
    # A2E - the highest-value PF signal (independent of TR/CS)
    row.update(a2e("trainerA2E_Career"))
    row.update(a2e("jockeyA2E_Career"))
    row.update(a2e("trainerJockeyA2E_Career"))
    row.update(a2e("trainerA2E_Last100"))
    row.update(a2e("jockeyA2E_Last100"))
    row.update(a2e("trainerJockeyA2E_Last100"))
    return row


def process_date(date_iso: str) -> None:
    """Pull all PF data for one date."""
    print(f"\n=== Processing {date_iso} ===")

    meetings = pf_get("meetingslist",
                      {"meetingDate": date_iso, "includeBarrierTrials": "false"})
    if not meetings:
        print(f"  No meetings returned for {date_iso}")
        return

    # Save raw on first run for debugging
    (RAW_DIR / f"meetings_{date_iso}.json").write_text(json.dumps(meetings, indent=2))

    # Filter to TAB meetings - PF gives us tabMeeting flag directly!
    # Previously also filtered out isJumps meetings, but PF flags a meeting
    # as isJumps even when only SOME races are jumps - losing flat races
    # on mixed cards (e.g. Warrnambool). User now flags jumps races
    # manually at bet placement.
    tab_meetings = [m for m in meetings
                    if isinstance(m, dict)
                    and m.get("tabMeeting") is True
                    and not m.get("isBarrierTrial")]
    print(f"  {len(meetings)} total meetings, {len(tab_meetings)} TAB meetings (filtered out non-TAB, trials)")

    # Save meeting metadata
    meeting_rows = []
    for m in tab_meetings:
        track = m.get("track") or {}
        meeting_rows.append({
            "date":              date_iso,
            "meeting_id":        m.get("meetingId"),
            "venue":             track.get("name"),
            "track_id":          track.get("trackId"),
            "state":             track.get("state"),
            "country":           track.get("country"),
            "abbrev":            track.get("abbrev"),
            "surface":           track.get("surface"),
            "rail_position":     m.get("railPosition"),
            "stage":             m.get("stage"),
            "tab_meeting":       m.get("tabMeeting"),
            "expected_condition": m.get("expectedCondition"),
            "form_updated":      m.get("formUpdated"),
            "ratings_updated":   m.get("ratingsUpdated"),
            "has_sectionals":    m.get("hasSectionals"),
        })
    n = append_rows(MEETINGS_CSV, meeting_rows, ["date", "meeting_id"])
    print(f"  +{n} meetings -> {MEETINGS_CSV.name}")

    # For each TAB meeting, pull fields, ratings, sectionals
    runner_rows = []
    ratings_rows = []
    sectionals_rows = []

    for m in tab_meetings:
        meeting_id = m.get("meetingId")
        venue = (m.get("track") or {}).get("name")
        if not meeting_id:
            continue

        # Fields - returns single meeting object with nested races[].runners[]
        fields_data = pf_get("fields", {"meetingId": meeting_id, "raceNumber": 0})
        if fields_data:
            races = fields_data.get("races") or []
            n_runners_pulled = 0
            n_races_kept = 0
            for race in races:
                # TopRate parity prize money filter (some TAB meetings have $5k bush races)
                prize = 0
                try:
                    prize = int(race.get("prizeMoney") or 0)
                except (TypeError, ValueError):
                    prize = 0
                if prize and prize < TAB_PRIZE_MIN:
                    continue
                n_races_kept += 1
                for runner in (race.get("runners") or []):
                    runner_rows.append(flatten_runner(runner, race, m, date_iso))
                    n_runners_pulled += 1
            print(f"  {venue}: {n_runners_pulled} runners across {n_races_kept} races")

        # Ratings - PF AI Price/Rank/Score, plus class/time/sectional ranks.
        # Endpoint group is /v2/Ratings/ (capital R), separate from /v2/form/.
        # Returns a flat list with one row per runner. Rich signals available:
        #   pfaiRank, pfaiPrice, pfaiScore        - the headline AI rating
        #   weightClassRank, timeAdjustedWeightClassRank - class-based
        #   timeRank, last600/400/200TimeRank     - sectional time rankings
        #   predictedSettlePostion, runStyle      - pace / position predictions
        #   classChange, isReliable               - quality flags
        ratings_data = pf_get(f"{API_BASE_RATINGS}/MeetingRatings",
                              {"meetingId": meeting_id, "raceNumber": 0})
        if ratings_data:
            (RAW_DIR / f"ratings_{date_iso}_{meeting_id}.json").write_text(
                json.dumps(ratings_data, indent=2))
            if isinstance(ratings_data, list):
                for item in ratings_data:
                    if not isinstance(item, dict):
                        continue
                    # Strip whitespace from runStyle which is right-padded ("bm        ")
                    rs = item.get("runStyle")
                    if isinstance(rs, str):
                        item["runStyle"] = rs.strip()
                    flat = {**item,
                            "_pf_date": date_iso,
                            "_pf_meeting_id": meeting_id,
                            "_pf_venue": venue}
                    ratings_rows.append(flat)
            elif isinstance(ratings_data, dict):
                # Defensive - shouldn't hit this for MeetingRatings but keep fallback
                races = ratings_data.get("races") or []
                if races:
                    for race in races:
                        for runner in (race.get("runners") or []):
                            if isinstance(runner, dict):
                                flat = {**runner,
                                        "_pf_date": date_iso,
                                        "_pf_meeting_id": meeting_id,
                                        "_pf_venue": venue,
                                        "_pf_race_id": race.get("raceId"),
                                        "_pf_race_number": race.get("number")}
                                ratings_rows.append(flat)

        # Sectionals - REQUIRES MODELLER TIER. Pro returns 403 "You do not have
        # access to this API". Code retained for if subscription is upgraded.
        if PULL_SECTIONALS:
            sec_data = pf_get(f"{API_BASE_RATINGS}/MeetingSectionals",
                              {"meetingId": meeting_id, "raceNumber": 0})
            if sec_data:
                (RAW_DIR / f"sectionals_{date_iso}_{meeting_id}.json").write_text(
                    json.dumps(sec_data, indent=2))
                if isinstance(sec_data, list):
                    for item in sec_data:
                        if isinstance(item, dict):
                            flat = {**item,
                                    "_pf_date": date_iso,
                                    "_pf_meeting_id": meeting_id}
                            sectionals_rows.append(flat)
                elif isinstance(sec_data, dict):
                    races = sec_data.get("races") or []
                    for race in races:
                        for runner in (race.get("runners") or []):
                            if isinstance(runner, dict):
                                flat = {**runner,
                                        "_pf_date": date_iso,
                                        "_pf_meeting_id": meeting_id,
                                        "_pf_race_id": race.get("raceId")}
                                sectionals_rows.append(flat)

    print()
    if runner_rows:
        n = append_rows(RUNNERS_CSV, runner_rows,
                        ["_pf_date", "_pf_meeting_id", "race_id", "runner_id"])
        msg = f"+{n} new" if n > 0 else f"already up to date ({len(runner_rows)} rows seen)"
        print(f"  Runners:    {msg} -> {RUNNERS_CSV.name}")
    if ratings_rows:
        n = append_rows(RATINGS_CSV, ratings_rows,
                        ["_pf_date", "_pf_meeting_id", "raceId", "runnerId"])
        msg = f"+{n} new" if n > 0 else f"already up to date ({len(ratings_rows)} rows seen)"
        print(f"  Ratings:    {msg} -> {RATINGS_CSV.name}")
    if sectionals_rows:
        keys = ["_pf_date", "_pf_meeting_id"]
        sample = sectionals_rows[0]
        for c in ("runnerId", "RunnerId", "runner_id"):
            if c in sample:
                keys.append(c)
                break
        n = append_rows(SECTIONALS_CSV, sectionals_rows, keys)
        msg = f"+{n} new" if n > 0 else f"already up to date ({len(sectionals_rows)} rows seen)"
        print(f"  Sectionals: {msg} -> {SECTIONALS_CSV.name}")


def main():
    p = argparse.ArgumentParser(description="Punting Form daily ingest")
    p.add_argument("--date", help="Date YYYY-MM-DD (default: today)")
    p.add_argument("--backfill", type=int, help="Pull last N days")
    args = p.parse_args()

    if args.backfill:
        today = datetime.now().date()
        for offset in range(args.backfill - 1, -1, -1):
            d = (today - timedelta(days=offset)).strftime("%Y-%m-%d")
            process_date(d)
    elif args.date:
        process_date(args.date)
    else:
        process_date(datetime.now().strftime("%Y-%m-%d"))


if __name__ == "__main__":
    main()
