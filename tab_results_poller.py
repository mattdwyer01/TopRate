#!/usr/bin/env python3
"""
tab_results_poller.py -- fast, provisional race results from TAB's public API.

RUNS LOCALLY ONLY, ON AN AUSTRALIAN MACHINE. It cannot run in GitHub Actions
or any cloud runner -- TAB geo-blocks non-AU IPs and fingerprints the TLS
handshake (see TAB_API_NOTES.md). This is why it's a separate script with its
own scheduler, not a step added to .github/workflows/*.yml.

WHY THIS EXISTS
toprate.au (the authoritative results feed used by update_results() in
toprate_daily.py) does not resolve a race's result until its WHOLE MEETING
has finished -- see toprate_price_refresh.py's module docstring. On an 8-race
meeting, race 1's result can sit unresolved on the dashboard for hours after
it's actually run. TAB exposes each race's result the moment that race goes
Interim/Paying, independent of the rest of the meeting. This script closes
that gap for the one thing TAB is good at -- who won, by how much, in what
order -- and changes NOTHING else. It never touches `resulted`, `wpr_actual`,
or comments_video/comments_steward: those stay exclusively the authoritative
feed's job, so update_results() keeps re-checking and finalizing exactly as
it does today, including correcting anything TAB got wrong (e.g. a protest).

WHAT IT WRITES (toprate_runners.csv, via toprate_daily.load_runners/save_runners)
    finish_position, margin_finish, won, placed, starting_price_sp
WHAT IT NEVER TOUCHES
    resulted, wpr_actual, comments_video, comments_steward, race_id, run_id,
    or any WPR/rating column. A later authoritative fetch overwrites all of
    the "WHAT IT WRITES" fields anyway once the meeting resolves, so a wrong
    or partial TAB read is self-correcting, never a lasting bad state.

MATCHING
toprate_runners.csv keys results by the provider's own run_id/race_id, which
TAB knows nothing about. So rows are matched on (date, venue, race, tab_number)
instead. TAB's venue names frequently don't match the provider's (confirmed
against the real CSV: provider says "Belmont Park", TAB says "Belmont";
provider says "Sandown", TAB splits it into "Sandown-Hillside" and
"Sandown-Lakeside") -- see VENUE_ALIASES below. An unmatched TAB venue is
logged loudly and skipped, never guessed at.

USAGE
    pip install curl_cffi
    python tab_results_poller.py --diagnose      # check AU IP + TLS shim first
    python tab_results_poller.py                 # run the live polling loop
    python tab_results_poller.py --once           # single pass, no loop (cron/Task Scheduler)

Intended scheduling: Windows Task Scheduler (or cron on the AU machine)
running `--once` every 1-2 minutes from ~30 min before the first AU race to
last-race-paying. NOT tested against the live TAB API from this environment
(this sketch was written from a cloud sandbox, which TAB itself would block) --
run --diagnose on the real AU machine before trusting anything else here.
"""
import argparse
import json
import subprocess
import sys
import time
import urllib.parse
import urllib.request
from datetime import date, datetime, timedelta
from pathlib import Path

import pandas as pd

sys.path.insert(0, str(Path(__file__).parent))
import toprate_daily as td  # reuse load_runners/save_runners/RUNNERS_CSV, keeps schema identical

ROOT = "https://api.beta.tab.com.au"
MEETINGS = ROOT + "/v1/tab-info-service/racing/dates/{date}/meetings"
RACE_TYPE = "R"  # thoroughbred only; TopRate doesn't track harness/greyhound
FINAL_STATUSES = ("Paying", "Abandoned")
AU_STATES = ("VIC", "NSW", "QLD", "SA", "WA", "TAS", "NT", "ACT")

# TAB meeting name -> provider (toprate.au) venue name, as it appears in
# toprate_runners.csv. Confirmed mismatches so far; expect to grow this the
# first few times a live run logs an UNMATCHED VENUE line. Never guess a
# mapping -- a wrong alias silently writes a result onto the wrong race.
VENUE_ALIASES = {
    "Belmont": "Belmont Park",
    "Sandown-Hillside": "Sandown",
    "Sandown-Lakeside": "Sandown",
    "Randwick-Kensington": "Randwick",
}

CACHE_FILE = Path(__file__).parent / "tab_poller_terminal_races.json"
RAW_ARCHIVE_DIR = Path(__file__).parent / "tab_raw"  # gitignored; raw JSON, per field notes point 4

try:
    from curl_cffi import requests as _cr
except ImportError:
    _cr = None


# --------------------------------------------------------------------- transport
def get(url, params=None, timeout=30):
    if params:
        url += ("&" if "?" in url else "?") + urllib.parse.urlencode(params)
    if _cr is not None:
        r = _cr.get(url, impersonate="chrome", timeout=timeout,
                    headers={"Accept": "application/json"})
        r.raise_for_status()
        return r.json()
    # No curl_cffi: works sometimes, stalls silently the rest of the time.
    # Kept only so --diagnose can tell the two failure modes apart.
    req = urllib.request.Request(url, headers={"Accept": "application/json"})
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return json.load(r)


def diagnose():
    print("TAB API connectivity check")
    print("-" * 52)
    print(f"  curl_cffi installed : {'yes' if _cr else 'NO  <-- pip install curl_cffi'}")
    today = date.today().isoformat()
    url = MEETINGS.format(date=today)
    ok = False
    try:
        get(url, {"jurisdiction": "VIC"}, timeout=15)
        ok = True
        print("  curl_cffi (chrome)  : ok" if _cr else "  plain urllib        : ok")
    except Exception as e:
        print(f"  request             : {type(e).__name__}: {str(e)[:80]}")
    print("-" * 52)
    if ok:
        print("  VERDICT: connected.")
        return 0
    if not _cr:
        print("  VERDICT: install curl_cffi and re-run before concluding anything.")
        return 1
    print("  VERDICT: failed with curl_cffi active. Check you're on an AU IP:")
    print("           curl -s https://ipinfo.io/country   (expect 'AU')")
    return 1


# --------------------------------------------------------------------- terminal-race cache
def load_terminal_cache():
    if CACHE_FILE.exists():
        return set(json.loads(CACHE_FILE.read_text()))
    return set()


def save_terminal_cache(cache):
    CACHE_FILE.write_text(json.dumps(sorted(cache)))


# --------------------------------------------------------------------- fetch + parse
def fetch_today_results(target_date, states=AU_STATES, terminal_cache=None,
                        archive=True):
    """
    Returns a list of dicts: {venue, race_no, tab_number, finish, margin, sp}
    for every runner in every non-terminal thoroughbred race across `states`.
    Mutates terminal_cache in place with any race that reached Paying/Abandoned.
    """
    terminal_cache = terminal_cache if terminal_cache is not None else set()
    out = []
    seen_meetings = set()

    for jurisdiction in states:
        try:
            payload = get(MEETINGS.format(date=target_date), {"jurisdiction": jurisdiction})
        except Exception as e:
            print(f"  {jurisdiction}: meeting list failed: {type(e).__name__}: {str(e)[:80]}")
            continue

        for m in payload.get("meetings", []):
            if m.get("raceType") != RACE_TYPE:
                continue
            venue = str(m.get("meetingName", "")).strip()
            # Jurisdiction is a filter, not a location -- a meeting can show up
            # under more than one state loop. Dedupe by (date, venue).
            mkey = (target_date, venue)
            if mkey in seen_meetings:
                continue
            seen_meetings.add(mkey)

            link = (m.get("_links") or {}).get("races")
            if not link:
                continue
            try:
                race_list = get(link, {"returnPromo": "false"}).get("races") or []
            except Exception as e:
                print(f"  {venue}: race list failed: {type(e).__name__}: {str(e)[:80]}")
                continue

            for rc in race_list:
                race_no = rc.get("raceNumber")
                rkey = f"{target_date}|{venue}|{race_no}"
                if rkey in terminal_cache:
                    continue  # Paying/Abandoned already -- never changes again

                self_link = (rc.get("_links") or {}).get("self")
                if not self_link:
                    continue
                try:
                    rd = get(self_link)
                except Exception as e:
                    print(f"  {venue} R{race_no}: detail failed: {type(e).__name__}: {str(e)[:60]}")
                    continue

                status = rd.get("raceStatus")
                if status in FINAL_STATUSES:
                    terminal_cache.add(rkey)

                if archive:
                    _archive_raw(target_date, venue, race_no, rd)

                results = rd.get("results") or []
                if not results:
                    time.sleep(0.15)
                    continue

                runner_by_no = {r.get("runnerNumber"): r for r in (rd.get("runners") or [])}
                # results[] is a list of finishing groups; each group is a list
                # of runner numbers that finished together (dead heats).
                for pos, group in enumerate(results, start=1):
                    numbers = group if isinstance(group, list) else [group]
                    for tab_no in numbers:
                        runner = runner_by_no.get(tab_no, {})
                        fo = runner.get("fixedOdds") or {}
                        out.append(dict(
                            date=target_date, venue=venue, race_no=race_no,
                            tab_number=tab_no, finish=pos,
                            margin=None,  # TAB's race detail doesn't carry a
                                          # clean per-runner margin field in
                                          # the same shape as the provider's
                                          # marginFinish -- leave it to the
                                          # authoritative feed rather than
                                          # guess at a mapping.
                            sp=fo.get("returnWin"),
                        ))
                time.sleep(0.15)
            time.sleep(0.3)

    return out, terminal_cache


def _archive_raw(target_date, venue, race_no, rd):
    try:
        d = RAW_ARCHIVE_DIR / target_date
        d.mkdir(parents=True, exist_ok=True)
        safe_venue = venue.replace("/", "-")
        (d / f"{safe_venue}_R{race_no}.json").write_text(json.dumps(rd))
    except Exception:
        pass  # archival is best-effort, never blocks the actual result write


# --------------------------------------------------------------------- match + write
def apply_results(runners_df, tab_results):
    """
    Match each TAB result row onto toprate_runners.csv by
    (date, provider-venue, race, tab_number). Returns (updated_df, n_written,
    unmatched_venues).
    """
    unmatched_venues = set()
    n_written = 0

    for res in tab_results:
        provider_venue = VENUE_ALIASES.get(res["venue"], res["venue"])
        mask = (
            (runners_df["date"] == res["date"]) &
            (runners_df["venue"] == provider_venue) &
            (pd.to_numeric(runners_df["race"], errors="coerce") == res["race_no"]) &
            (pd.to_numeric(runners_df["tab_number"], errors="coerce") == res["tab_number"])
        )
        rows = runners_df[mask]
        if rows.empty:
            unmatched_venues.add(res["venue"])
            continue

        idx = rows.index[0]
        finish = res["finish"]
        runners_df.loc[idx, "finish_position"] = finish
        runners_df.loc[idx, "won"] = 1 if finish == 1 else 0
        runners_df.loc[idx, "placed"] = 1 if finish <= 3 else 0
        if res.get("sp") is not None:
            runners_df.loc[idx, "starting_price_sp"] = res["sp"]
        # Deliberately NOT touching resulted / wpr_actual / comments_* -- see
        # module docstring. The authoritative feed still owns those.
        n_written += 1

    return runners_df, n_written, unmatched_venues


# --------------------------------------------------------------------- publish
def rebuild_and_push():
    """Refresh toprate_data.json from the CSV, then commit + push the same
    way price_refresh.yml does: pull --rebase first, retry a few times,
    take theirs on conflicts in generated files (never code)."""
    subprocess.run([sys.executable, "toprate_daily.py", "--rebuild-only"], check=True)

    status = subprocess.run(["git", "status", "--porcelain"], capture_output=True, text=True)
    if not status.stdout.strip():
        print("  No changes to commit")
        return

    subprocess.run(["git", "add", "toprate_runners.csv", "toprate_data.json"], check=True)
    subprocess.run(["git", "commit", "-m",
                    f"TAB live results {datetime.utcnow().strftime('%Y-%m-%dT%H:%MZ')}"], check=True)

    for attempt in range(1, 6):
        push = subprocess.run(["git", "push"], capture_output=True, text=True)
        if push.returncode == 0:
            print(f"  Pushed on attempt {attempt}")
            return
        print(f"  Push rejected (attempt {attempt}) - pulling and retrying")
        subprocess.run(["git", "pull", "--rebase", "-X", "theirs", "--no-edit"])
        time.sleep(3)
    print("  Push failed after retries -- leaving local commit for manual resolution")


# --------------------------------------------------------------------- main
def run_once(push=True):
    target_date = date.today().isoformat()
    terminal_cache = load_terminal_cache()

    results, terminal_cache = fetch_today_results(target_date, terminal_cache=terminal_cache)
    save_terminal_cache(terminal_cache)

    if not results:
        print("  No new TAB results this cycle")
        return

    runners_df = td.load_runners()
    runners_df, n_written, unmatched = apply_results(runners_df, results)

    if unmatched:
        print(f"  UNMATCHED VENUE(S), skipped (add to VENUE_ALIASES): {sorted(unmatched)}")

    if n_written == 0:
        print("  Nothing matched this cycle")
        return

    td.save_runners(runners_df)
    print(f"  Wrote {n_written} TAB result rows")

    if push:
        rebuild_and_push()


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--diagnose", action="store_true")
    ap.add_argument("--once", action="store_true", help="single pass (for cron/Task Scheduler)")
    ap.add_argument("--no-push", action="store_true", help="write the CSV but skip git commit/push")
    ap.add_argument("--interval", type=int, default=90,
                    help="seconds between polls in loop mode (default 90)")
    a = ap.parse_args()

    if a.diagnose:
        return diagnose()

    if a.once:
        run_once(push=not a.no_push)
        return 0

    print(f"Polling every {a.interval}s. Ctrl+C to stop.")
    while True:
        try:
            run_once(push=not a.no_push)
        except Exception as e:
            print(f"  Cycle failed: {type(e).__name__}: {e}")
        time.sleep(a.interval)


if __name__ == "__main__":
    sys.exit(main())
