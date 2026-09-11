#!/usr/bin/env python3
"""
tab_results_poller.py -- fast, provisional race results, track condition/
rail updates, and live fixed prices, from TAB's public API.

MUST RUN FROM A REAL AUSTRALIAN IP -- TAB geo-blocks and TLS-fingerprints
everything else, VPS/cloud included in general (confirmed against GitHub-
hosted runners specifically), though a Vultr AU datacenter instance has been
confirmed working in practice, contrary to the general rule. Runs today as a
GitHub Actions self-hosted runner (see .github/workflows/tab_results.yml)
registered from such a machine -- not a step on a normal hosted runner.

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
    finish_position, won, placed, interim_resulted (per runner, from race
    results -- interim_resulted flips the dashboard's race-level "done"
    display flag right away, see apply_results())
    going, track_grading, rail_position (per meeting, from trackCondition/
    railPosition -- applied to every runner at that venue+date, since
    conditions are a whole-card property, not a per-race one). A real going
    change also triggers a WPR ratings recompute, scoped to just that
    meeting (see run_once()/compute_wpr_projection's target_venues param).
    fixed_win_price, scratched (per runner, from a race's own fixedOdds --
    see fetch_today_results' `prices` docstring and apply_prices()). A
    SECOND, independent source alongside toprate_price_refresh.py's
    existing 5-min refresh, not a replacement of it.
WHAT IT NEVER TOUCHES
    resulted, wpr_actual, comments_video, comments_steward, race_id, run_id,
    or any WPR/rating column except via the scoped recompute above. A later
    authoritative fetch overwrites the result fields anyway once the
    meeting resolves, so a wrong or partial TAB read there is
    self-correcting, never a lasting bad state.

MATCHING
toprate_runners.csv keys results by the provider's own run_id/race_id, which
TAB knows nothing about. So rows are matched on (date, venue, race, tab_number)
instead, case-insensitively -- TAB returns AU venue names in ALL CAPS
("GRAFTON", "TATURA") while the provider CSV uses Title Case ("Grafton"),
confirmed against a real payload. TAB's venue names also frequently don't
match the provider's beyond casing (provider says "Belmont Park", TAB says
"BELMONT"; provider says "Sandown", TAB splits it into "SANDOWN-HILLSIDE" and
"SANDOWN-LAKESIDE") -- see VENUE_ALIASES below (keys upper-cased). An
unmatched TAB venue is logged loudly and skipped, never guessed at.

FETCHING
Confirmed against a real payload: the meeting-list response already embeds
each race's raceStatus and finishing results[] directly on its stub, before
any drill-down, plus enough on the meeting object (venueMnemonic) and race
stub (hasFixedOdds, raceStartTime) to decide what's worth fetching further.
Results/conditions read straight off this cheap tier: one request per AU
state per cycle, no drill-down needed at all.

Prices are the one thing that genuinely isn't on the cheap tier (confirmed
via --probe-odds from an AU IP: starting_price_sp and fixedOdds both only
exist at the race-detail level). Rather than following a meeting's
_links.races hop first, the race-detail URL is built directly from
venue_mnemonic + race number (RACE_DETAIL), one extra request per race that
is both still open (hasFixedOdds True, not yet Paying/Abandoned) and
starting within PRICE_LOOKAHEAD_HOURS (same bounding window
toprate_price_refresh.py already uses) -- not every open race on the card
all day. That detail response's runners[] carries a fixedOdds dict per
runner (returnWin/returnPlace/bettingStatus/flucs/...).

USAGE
    pip install curl_cffi
    python tab_results_poller.py --diagnose      # check AU IP + TLS shim first
    python tab_results_poller.py                 # run the live polling loop
    python tab_results_poller.py --once           # single pass (workflow/cron)

Scheduling in production: an external cron-job.org schedule calls
.github/workflows/tab_results.yml's workflow_dispatch endpoint during AU
racing hours, which dispatches to the self-hosted runner, which runs
`--once --no-push` (the workflow's own step handles git).

PUBLISHING (patch_data_json vs. a full rebuild)
A plain results/prices/scratches cycle no longer runs the full
`toprate_daily.py --rebuild-only` subprocess (~2-3 min on a modest 1
vCPU/2GB box, dominated by a form-history/settling-band rebuild that
doesn't depend on any of these fields at all) - it patches just the
touched runners' fx/f/won/scr keys directly into the existing
toprate_data.json (see toprate_daily.patch_data_json()), which is a
fraction of a second. Only a real going change still forces the full
rebuild, since that's what the scoped WPR recompute needs to get its
wprp_* fields serialized. A typical cycle should now complete in well
under a minute; the workflow's concurrency group (skips an overlapping
trigger rather than queuing it) still guards against a genuinely slow
cycle (a real going change, or patch_data_json falling back to a full
rebuild) overlapping the next trigger.
"""
import argparse
import json
import re
import shutil
import subprocess
import sys
import time
import urllib.parse
import urllib.request
from datetime import date, datetime, timedelta, timezone
from pathlib import Path

import pandas as pd

sys.path.insert(0, str(Path(__file__).parent))
import toprate_daily as td  # reuse load_runners/save_runners/RUNNERS_CSV, keeps schema identical

ROOT = "https://api.beta.tab.com.au"
MEETINGS = ROOT + "/v1/tab-info-service/racing/dates/{date}/meetings"
RACE_DETAIL = ROOT + "/v1/tab-info-service/racing/dates/{date}/meetings/R/{venue_mnemonic}/races/{race_no}"
RACE_TYPE = "R"  # thoroughbred only; TopRate doesn't track harness/greyhound
FINAL_STATUSES = ("Paying", "Abandoned")
# Matches toprate_price_refresh.py's own LOOKAHEAD_HOURS default (2.0) and
# "last 30 min" past-window - same reasoning: bound the per-race price
# drill-down to races that actually matter right now, not every open race
# on the card all day.
PRICE_LOOKAHEAD_HOURS = 2.0
PRICE_PAST_WINDOW_MINUTES = 30
AU_STATES = ("VIC", "NSW", "QLD", "SA", "WA", "TAS", "NT", "ACT")

# TAB meeting name (upper-cased -- TAB returns AU venues in ALL CAPS,
# confirmed against a real payload) -> provider (toprate.au) venue name, as
# it appears in toprate_runners.csv. Confirmed mismatches so far; expect to
# grow this the first few times a live run logs an UNMATCHED VENUE line.
# Never guess a mapping -- a wrong alias silently writes a result onto the
# wrong race.
VENUE_ALIASES = {
    "BELMONT": "Belmont Park",
    "SANDOWN-HILLSIDE": "Sandown",
    "SANDOWN-LAKESIDE": "Sandown",
    "RANDWICK-KENSINGTON": "Randwick",
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


def probe_odds():
    """
    ONE-OFF, read-only investigation tool -- not part of the regular poll
    cycle, never writes anything. Answers the question the meeting-list
    endpoint's own docstring already flags (see FETCHING above):
    starting_price_sp only exists at the race-detail level, one tier down
    via _links.races/_links.self -- fixedOdds is presumed to live there too,
    but that's unconfirmed until a real payload is inspected from an AU IP.
    Run this on the Vultr box (or wherever --diagnose already passes) and
    paste the output back -- it decides whether live TAB prices are a cheap
    add to the existing meeting-list poll, or need the pricier per-race
    drill-down (1 + N-meetings + N*M-races requests/cycle) the results/
    conditions path deliberately avoided.
    """
    today = date.today().isoformat()
    for jurisdiction in AU_STATES:
        payload = get(MEETINGS.format(date=today), {"jurisdiction": jurisdiction})
        for m in payload.get("meetings", []):
            if m.get("raceType") != RACE_TYPE or m.get("location") not in AU_STATES:
                continue
            # Prefer a race that's still open to fixed-odds betting - a
            # settled/Interim race closes hasFixedOdds and drops any
            # drill-down link, which is a dead end for this probe.
            open_races = [rc for rc in m.get("races", [])
                          if rc.get("raceStatus") not in FINAL_STATUSES
                          and rc.get("hasFixedOdds")]
            if not open_races:
                continue
            rc = open_races[0]
            print(f"Meeting: {m.get('meetingName')} ({m.get('location')})  "
                  f"Race {rc.get('raceNumber')}  status={rc.get('raceStatus')}  "
                  f"hasFixedOdds={rc.get('hasFixedOdds')}")
            print("Meeting top-level keys:", sorted(m.keys()))
            print("Race stub top-level keys:", sorted(rc.keys()))
            hit = {k: v for k, v in rc.items()
                   if any(t in k.lower() for t in ("odd", "price", "fixed"))}
            print("  price-ish keys on the race stub itself:", hit or "(none)")

            # _links has shown up on the MEETING object in a real payload
            # before (see fetch_today_results' own comment on international
            # meetings), not necessarily on each race stub - check both.
            race_link = ((rc.get("_links") or {}).get("self")
                         or (m.get("_links") or {}).get("races"))
            if not race_link:
                print("  no _links.self (race) or _links.races (meeting) found -- stopping here")
                print("  Full meeting dict (first 3000 chars):")
                print(json.dumps(m, indent=2, default=str)[:3000])
                return 0
            print(f"  fetching race detail: {race_link}")
            detail = get(race_link)
            # _links.races returns EVERY race at the meeting, not one race -
            # handle both shapes.
            if isinstance(detail, dict) and "races" in detail and "runners" not in detail:
                races_list = detail["races"]
                print(f"  meeting detail: {len(races_list)} races returned")
                match = next((r for r in races_list
                              if r.get("raceNumber") == rc.get("raceNumber")), races_list[0])
                print("  Matching race's top-level keys:", sorted(match.keys()))
                detail = match
            print("  Race detail top-level keys:", sorted(detail.keys()))
            runners = detail.get("runners") or (detail.get("race") or {}).get("runners") or []
            print(f"  {len(runners)} runners in detail payload")
            if runners:
                print("  First runner's full dict:")
                print(json.dumps(runners[0], indent=2, default=str)[:3000])
            out_path = RAW_ARCHIVE_DIR / "probe_race_detail.json"
            RAW_ARCHIVE_DIR.mkdir(exist_ok=True)
            out_path.write_text(json.dumps(detail, indent=2, default=str))
            print(f"  Full race detail saved to {out_path}")
            return 0
    print("No open (hasFixedOdds=True, non-final) AU thoroughbred race found today to probe.")
    return 1


# --------------------------------------------------------------------- terminal-race cache
def load_terminal_cache():
    if CACHE_FILE.exists():
        return set(json.loads(CACHE_FILE.read_text()))
    return set()


def save_terminal_cache(cache):
    CACHE_FILE.write_text(json.dumps(sorted(cache)))


# --------------------------------------------------------------------- fetch + parse
# Matches TAB's condensed condition strings ("SOFT7", "GOOD4") into
# (going, track_grading) matching the provider's own format in
# toprate_runners.csv ("Soft 7", 7.0 -- confirmed by inspecting real CSV
# rows). Conditions with no trailing number are real too (confirmed in a
# live payload: "FIRM", "HEAVY", "AWT" for synthetic/all-weather tracks) --
# those get title-cased with no grading number rather than guessed at.
_CONDITION_RE = re.compile(r"^([A-Za-z]+)\s*(\d+)?$")

def parse_track_condition(raw):
    if not raw:
        return None, None
    m = _CONDITION_RE.match(str(raw).strip())
    if not m:
        return str(raw).strip(), None
    word, number = m.groups()
    going = f"{word.capitalize()} {number}" if number else word.capitalize()
    grading = float(number) if number else None
    return going, grading


def _parse_tab_time(raw):
    """Parse TAB's raceStartTime ('2026-09-11T08:00:00.000Z') to a UTC
    datetime, or None. Matches toprate_price_refresh.py's own
    parse_start_time tolerance for a bad/missing value."""
    if not raw:
        return None
    try:
        dt = pd.to_datetime(raw, errors="coerce", utc=True)
        if pd.isna(dt):
            return None
        return dt.to_pydatetime()
    except Exception:
        return None


def _within_price_window(start_dt):
    """True if start_dt falls in [now - 30min, now + PRICE_LOOKAHEAD_HOURS] --
    the same window toprate_price_refresh.py already uses for the existing
    fixed_win_price refresh, so this drill-down stays bounded to races that
    actually matter right now rather than every open race on the card."""
    if start_dt is None:
        return False
    now = datetime.now(timezone.utc)
    return (now - timedelta(minutes=PRICE_PAST_WINDOW_MINUTES)) <= start_dt <= \
        (now + timedelta(hours=PRICE_LOOKAHEAD_HOURS))


def fetch_today_results(target_date, states=AU_STATES, terminal_cache=None,
                        archive=True, fetch_prices=True):
    """
    Returns (results, conditions, prices, terminal_cache).

    results: a list of dicts {venue, race_no, tab_number, finish} for every
    runner in every non-terminal AU thoroughbred race, read straight off the
    meeting-list response (raceStatus and results[] are already embedded on
    each race stub -- confirmed against a real payload, no drill-down into
    _links.races/_links.self needed).

    conditions: a list of dicts {date, venue, going, track_grading,
    rail_position}, one per AU meeting that reported a trackCondition or
    railPosition this cycle -- these are whole-card properties in TAB's
    payload (on the meeting object, not per-race), so they apply to every
    runner at that venue+date, not a specific race/tab_number.

    prices: a list of dicts {date, venue, race_no, tab_number, scratched,
    fixed_win_price (optional)} -- ONE extra HTTP call per race that is
    still open (hasFixedOdds, not yet Paying/Abandoned) and starting within
    PRICE_LOOKAHEAD_HOURS (or finished in the last 30 min). Confirmed via a
    real payload (--probe-odds): the cheap meeting-list response has no
    price data at all, but each race's own detail endpoint -- constructed
    directly from the meeting's venueMnemonic + the race number, no need to
    follow a meeting-level _links.races hop first -- returns runners[] with
    a fixedOdds dict per runner (returnWin/returnPlace/bettingStatus/...).
    fixed_win_price is only included when bettingStatus isn't LateScratched
    and returnWin > 1 (same sanity floor toprate_price_refresh.py already
    applies to the existing fixed-odds source) -- scratched is always
    reported so a late scratch is caught even without a valid price.
    fetch_prices=False skips this tier entirely (used by callers that only
    want results/conditions, e.g. tests).

    Mutates terminal_cache in place with any race that reached
    Paying/Abandoned.
    """
    terminal_cache = terminal_cache if terminal_cache is not None else set()
    out = []
    conditions = []
    prices = []
    seen_meetings = set()

    # Circuit breaker: if TAB starts blocking/degrading this IP again (see
    # module docstring -- it's happened before), every get() below would
    # otherwise sit out its own timeout one at a time across 8 jurisdictions
    # plus every open race's price drill-down, turning a normal sub-second
    # cycle into many minutes and eating the self-hosted runner's whole job
    # budget on a single stuck run (2026-09-11 outage: one cycle's "Poll TAB"
    # step alone ran ~8 min, and the runner never picked up a job again
    # afterward). 3 consecutive failures aborts the rest of THIS cycle only
    # (results/conditions already collected are kept, nothing is lost) --
    # the next trigger a minute or two later tries again from scratch.
    MAX_CONSECUTIVE_FAILURES = 3
    FAST_FAIL_TIMEOUT = 10  # this poller runs every 1-2 min; a slow-but-
    # working response isn't worth patiently waiting 30s for at this cadence.
    consecutive_failures = 0
    aborted = False

    for jurisdiction in states:
        if aborted:
            break
        try:
            payload = get(MEETINGS.format(date=target_date), {"jurisdiction": jurisdiction},
                         timeout=FAST_FAIL_TIMEOUT)
            consecutive_failures = 0
        except Exception as e:
            print(f"  {jurisdiction}: meeting list failed: {type(e).__name__}: {str(e)[:80]}")
            consecutive_failures += 1
            if consecutive_failures >= MAX_CONSECUTIVE_FAILURES:
                print(f"  {consecutive_failures} consecutive failures -- aborting rest of this "
                      f"cycle (TAB likely blocking/degraded) instead of grinding through every "
                      f"remaining state/race at full timeout")
                aborted = True
            continue

        if archive:
            _archive_raw(target_date, jurisdiction, payload)

        for m in payload.get("meetings", []):
            if aborted:
                break
            if m.get("raceType") != RACE_TYPE:
                continue
            # Jurisdiction is a query filter, not a location filter -- the
            # response mixes in international meetings (confirmed: USA/JPN/
            # TUR/GBR/etc thoroughbred meetings appear even under
            # jurisdiction=VIC, some with a full _links.races of their own).
            # TopRate is AU-thoroughbred only.
            if m.get("location") not in AU_STATES:
                continue
            venue = str(m.get("meetingName", "")).strip()
            venue_mnemonic = m.get("venueMnemonic")
            # A venue can also appear under more than one jurisdiction loop
            # (same reason as above). Dedupe by (date, venue).
            mkey = (target_date, venue)
            if mkey in seen_meetings:
                continue
            seen_meetings.add(mkey)

            going, track_grading = parse_track_condition(m.get("trackCondition"))
            rail_position = m.get("railPosition")
            if going or rail_position:
                conditions.append(dict(
                    date=target_date, venue=venue, going=going,
                    track_grading=track_grading, rail_position=rail_position,
                ))

            for rc in m.get("races", []):
                if aborted:
                    break
                race_no = rc.get("raceNumber")
                rkey = f"{target_date}|{venue}|{race_no}"
                if rkey in terminal_cache:
                    continue  # Paying/Abandoned already -- never changes again

                status = rc.get("raceStatus")
                if status in FINAL_STATUSES:
                    terminal_cache.add(rkey)

                # Price drill-down: independent of whether results[] exists
                # yet -- this is exactly for races that HAVEN'T run, so it
                # has to run before the `if not results: continue` below,
                # not after.
                if (fetch_prices and venue_mnemonic and rc.get("hasFixedOdds")
                        and status not in FINAL_STATUSES
                        and _within_price_window(_parse_tab_time(rc.get("raceStartTime")))):
                    try:
                        race_detail = get(
                            RACE_DETAIL.format(date=target_date, venue_mnemonic=venue_mnemonic,
                                               race_no=race_no),
                            {"jurisdiction": jurisdiction}, timeout=FAST_FAIL_TIMEOUT)
                        consecutive_failures = 0
                        for run in race_detail.get("runners", []):
                            tab_no = run.get("runnerNumber")
                            if tab_no is None:
                                continue
                            fo = run.get("fixedOdds") or {}
                            is_scratched = fo.get("bettingStatus") == "LateScratched"
                            entry = dict(date=target_date, venue=venue, race_no=race_no,
                                        tab_number=tab_no, scratched=is_scratched)
                            win_price = fo.get("returnWin")
                            if not is_scratched and win_price and win_price > 1:
                                entry["fixed_win_price"] = win_price
                            prices.append(entry)
                    except Exception as e:
                        print(f"  price fetch failed for {venue} R{race_no}: "
                              f"{type(e).__name__}: {str(e)[:60]}")
                        consecutive_failures += 1
                        if consecutive_failures >= MAX_CONSECUTIVE_FAILURES:
                            print(f"  {consecutive_failures} consecutive failures -- aborting "
                                  f"rest of this cycle (TAB likely blocking/degraded) instead of "
                                  f"grinding through every remaining state/race at full timeout")
                            aborted = True
                    time.sleep(0.15)  # polite spacing between per-race calls

                results = rc.get("results") or []
                if not results:
                    continue

                # results[] is a list of finishing-position groups; each
                # group is a list of runner numbers (more than one on a dead
                # heat), and can be shorter than the full field (confirmed:
                # some races only carry placegetters, with empty trailing
                # groups) -- enumerate() and the inner loop both degrade
                # safely to zero iterations on an empty group.
                for pos, group in enumerate(results, start=1):
                    numbers = group if isinstance(group, list) else [group]
                    for tab_no in numbers:
                        if tab_no is None:
                            continue
                        out.append(dict(
                            date=target_date, venue=venue, race_no=race_no,
                            tab_number=tab_no, finish=pos,
                        ))

        time.sleep(0.3)  # polite spacing between the (at most 8) state calls

    return out, conditions, prices, terminal_cache


def _archive_raw(target_date, jurisdiction, payload):
    try:
        d = RAW_ARCHIVE_DIR / target_date
        d.mkdir(parents=True, exist_ok=True)
        (d / f"meetings_{jurisdiction}.json").write_text(json.dumps(payload))
    except Exception:
        pass  # archival is best-effort, never blocks the actual result write


RAW_ARCHIVE_RETENTION_DAYS = 3  # this is a debugging aid (per field notes
# point 4), not data anything depends on -- nothing was ever pruning it, and
# at one dated folder added per day forever with no reader ever deleting
# old ones, it's the one genuinely unbounded thing this poller writes to
# disk on a box that otherwise gets restarted rarely (self-hosted, meant to
# run unattended for months). Confirmed as a live problem 2026-09-11: the
# runner reported 0 MB free disk space right after the outage above.


def _prune_raw_archive(target_date):
    """Delete tab_raw/<date> folders older than the retention window. Best-
    effort and cheap (a handful of directory-name comparisons) -- run once
    per cycle so disk usage stays flat regardless of how long this poller
    runs unattended."""
    try:
        if not RAW_ARCHIVE_DIR.is_dir():
            return
        cutoff = date.fromisoformat(target_date) - timedelta(days=RAW_ARCHIVE_RETENTION_DAYS)
        for d in RAW_ARCHIVE_DIR.iterdir():
            if not d.is_dir():
                continue
            try:
                d_date = date.fromisoformat(d.name)
            except ValueError:
                continue  # not a dated archive folder -- leave it alone
            if d_date < cutoff:
                shutil.rmtree(d, ignore_errors=True)
    except Exception as e:
        print(f"  raw archive prune failed (non-fatal): {type(e).__name__}: {e}")


# --------------------------------------------------------------------- match + write
def apply_results(runners_df, tab_results):
    """
    Match each TAB result row onto toprate_runners.csv by
    (date, provider-venue, race, tab_number), case-insensitively on venue --
    TAB returns AU venues in ALL CAPS, the provider CSV uses Title Case
    (confirmed against a real payload). Returns (updated_df, n_written,
    unmatched_venues).

    Also sets interim_resulted = 1 on every row written -- this is what
    flips the dashboard's race-level "done" flag (see toprate_daily.py's
    RACES payload build) as soon as TAB reports a finishing position, well
    before update_results() gets to that meeting and sets the real
    `resulted`. Never touches resulted/wpr_actual/comments_* -- see module
    docstring.

    Also returns `patches`: run_id -> {"f": finish, "won": won} for every
    row written, keyed the same way toprate_data.json's own runner records
    are ("rid") -- lets run_once() patch the JSON directly instead of
    running the full rebuild for a plain results cycle. Only rows with a
    non-blank run_id are included (a runner not yet through a full rebuild
    has no "rid" match in the JSON yet - patching it would be a no-op
    anyway, and its result is safely picked up on the next full rebuild).
    """
    unmatched_venues = set()
    n_written = 0
    patches = {}
    runner_venue_upper = runners_df["venue"].astype(str).str.upper()

    for res in tab_results:
        tab_venue_upper = res["venue"].upper()
        provider_venue = VENUE_ALIASES.get(tab_venue_upper, res["venue"])
        mask = (
            (runners_df["date"] == res["date"]) &
            (runner_venue_upper == provider_venue.upper()) &
            (pd.to_numeric(runners_df["race"], errors="coerce") == res["race_no"]) &
            (pd.to_numeric(runners_df["tab_number"], errors="coerce") == res["tab_number"])
        )
        rows = runners_df[mask]
        if rows.empty:
            unmatched_venues.add(res["venue"])
            continue

        idx = rows.index[0]
        finish = res["finish"]
        won = 1 if finish == 1 else 0
        runners_df.loc[idx, "finish_position"] = finish
        runners_df.loc[idx, "won"] = won
        runners_df.loc[idx, "placed"] = 1 if finish <= 3 else 0
        runners_df.loc[idx, "interim_resulted"] = 1
        # Deliberately NOT touching resulted / wpr_actual / comments_* -- see
        # module docstring. The authoritative feed still owns those.
        n_written += 1
        run_id = rows["run_id"].iloc[0] if "run_id" in rows.columns else None
        if run_id and str(run_id) != "nan":
            patches[str(run_id)] = {"f": finish, "won": won}

    return runners_df, n_written, unmatched_venues, patches


def apply_conditions(runners_df, conditions):
    """
    Update going/track_grading/rail_position for every runner at a meeting,
    case-insensitively on venue (same matching as apply_results). Applied to
    the whole (date, venue) group, not a specific race/tab_number -- track
    condition and rail position are meeting-wide, not per-race. Returns
    (updated_df, n_rows_touched, changes, changed_venues, unmatched_venues),
    where `changes` is a list of human-readable "old -> new" strings for
    going values that actually differ from what was already there -- so a
    run that reconfirms an unchanged condition stays quiet, but a real
    downgrade/upgrade is always visible in the log. `changed_venues` is the
    matching set of CSV-cased venue names (a subset of what `changes`
    describes), for the caller to scope a WPR recompute to just the
    meetings that actually moved.
    """
    unmatched_venues = set()
    n_written = 0
    changes = []
    changed_venues = set()
    runner_venue_upper = runners_df["venue"].astype(str).str.upper()

    for cond in conditions:
        tab_venue_upper = cond["venue"].upper()
        provider_venue = VENUE_ALIASES.get(tab_venue_upper, cond["venue"])
        mask = (
            (runners_df["date"] == cond["date"]) &
            (runner_venue_upper == provider_venue.upper())
        )
        rows = runners_df[mask]
        if rows.empty:
            unmatched_venues.add(cond["venue"])
            continue

        if cond.get("going"):
            old_going = rows["going"].iloc[0] if "going" in rows.columns else None
            if str(old_going) != str(cond["going"]):
                # Log using the CSV's own venue casing (Title Case), not
                # provider_venue's TAB-cased fallback when there's no alias
                # entry - reads properly in the Action log either way.
                csv_venue = rows["venue"].iloc[0]
                changes.append(f"{csv_venue}: going {old_going!r} -> {cond['going']!r}")
                changed_venues.add(csv_venue)
            runners_df.loc[mask, "going"] = cond["going"]
        if cond.get("track_grading") is not None:
            runners_df.loc[mask, "track_grading"] = cond["track_grading"]
        if cond.get("rail_position"):
            runners_df.loc[mask, "rail_position"] = cond["rail_position"]
        n_written += len(rows)

    return runners_df, n_written, changes, changed_venues, unmatched_venues


def apply_prices(runners_df, prices):
    """
    Write fixed_win_price/scratched from TAB's per-race fixedOdds drill-down
    (see fetch_today_results' `prices` docstring). Matches the same way as
    apply_results: (date, provider-venue, race, tab_number), case-
    insensitively on venue. This is a SECOND, independent source for
    fixed_win_price alongside toprate_price_refresh.py's existing 5-min
    refresh (untouched, still running) - not a replacement, see CLAUDE.md's
    Current state section for why a cutover needs separate validation
    first. Only ever ADDS a fresher price or a newly-discovered scratch;
    never clears an existing scratched=1 (a scratch is permanent) or writes
    a price for a scratched runner. Returns (updated_df, n_priced,
    n_scratched, unmatched_venues, patches).

    `patches` is run_id -> {"fx": price} or {"scr": 1} -- see
    apply_results' own `patches` docstring for why (lets run_once() patch
    toprate_data.json directly instead of a full rebuild).
    """
    unmatched_venues = set()
    n_priced = 0
    n_scratched = 0
    patches = {}
    runner_venue_upper = runners_df["venue"].astype(str).str.upper()

    for p in prices:
        tab_venue_upper = p["venue"].upper()
        provider_venue = VENUE_ALIASES.get(tab_venue_upper, p["venue"])
        mask = (
            (runners_df["date"] == p["date"]) &
            (runner_venue_upper == provider_venue.upper()) &
            (pd.to_numeric(runners_df["race"], errors="coerce") == p["race_no"]) &
            (pd.to_numeric(runners_df["tab_number"], errors="coerce") == p["tab_number"])
        )
        rows = runners_df[mask]
        if rows.empty:
            unmatched_venues.add(p["venue"])
            continue

        idx = rows.index[0]
        run_id = rows["run_id"].iloc[0] if "run_id" in rows.columns else None
        has_run_id = bool(run_id) and str(run_id) != "nan"

        if p.get("scratched"):
            already = rows.get("scratched")
            already_scratched = already is not None and int(already.iloc[0] or 0) == 1
            runners_df.loc[idx, "scratched"] = 1
            if not already_scratched:
                n_scratched += 1
                if has_run_id:
                    patches[str(run_id)] = {"scr": 1}
            continue  # never write a price alongside a scratch

        if "fixed_win_price" in p:
            runners_df.loc[idx, "fixed_win_price"] = p["fixed_win_price"]
            n_priced += 1
            if has_run_id:
                patches[str(run_id)] = {"fx": p["fixed_win_price"]}

    return runners_df, n_priced, n_scratched, unmatched_venues, patches


# --------------------------------------------------------------------- publish
def rebuild_data_json():
    """Refresh toprate_data.json from toprate_runners.csv (--rebuild-only,
    no network fetch) so the dashboard actually picks up what was just
    written. Always runs, independent of --no-push -- that flag means "let
    the caller handle git", not "skip regenerating the payload". (This used
    to live inside rebuild_and_push(), gated behind `if push`, which meant
    the workflow's --no-push call silently never rebuilt toprate_data.json
    at all -- confirmed live: a run wrote 100 result rows to the CSV but
    only 1 file changed in the commit, not 2.)"""
    subprocess.run([sys.executable, "toprate_daily.py", "--rebuild-only"], check=True)


def commit_and_push():
    """Commit + push toprate_runners.csv/toprate_data.json, same way
    price_refresh.yml does: pull --rebase first, retry a few times,
    take theirs on conflicts in generated files (never code)."""
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
    _prune_raw_archive(target_date)
    terminal_cache = load_terminal_cache()

    results, conditions, prices, terminal_cache = fetch_today_results(
        target_date, terminal_cache=terminal_cache)
    save_terminal_cache(terminal_cache)

    if not results and not conditions and not prices:
        print("  No new TAB results, conditions, or prices this cycle")
        return

    runners_df = td.load_runners()
    n_result_rows = 0
    n_condition_rows = 0
    n_priced = 0
    n_scratched = 0
    result_patches = {}
    price_patches = {}
    scratch_patches = {}

    if results:
        runners_df, n_result_rows, unmatched, result_patches = apply_results(runners_df, results)
        if unmatched:
            print(f"  UNMATCHED VENUE(S) for results, skipped (add to VENUE_ALIASES): {sorted(unmatched)}")

    changed_venues = set()
    if conditions:
        runners_df, n_condition_rows, changes, changed_venues, unmatched = apply_conditions(
            runners_df, conditions)
        if unmatched:
            print(f"  UNMATCHED VENUE(S) for conditions, skipped (add to VENUE_ALIASES): {sorted(unmatched)}")
        for c in changes:
            print(f"  Track condition update: {c}")

    if prices:
        runners_df, n_priced, n_scratched, unmatched, price_scratch_patches = apply_prices(
            runners_df, prices)
        if unmatched:
            print(f"  UNMATCHED VENUE(S) for prices, skipped (add to VENUE_ALIASES): {sorted(unmatched)}")
        for rid, patch in price_scratch_patches.items():
            if "fx" in patch:
                price_patches[rid] = patch["fx"]
            if "scr" in patch:
                scratch_patches[rid] = patch["scr"]

    if n_result_rows == 0 and n_condition_rows == 0 and n_priced == 0 and n_scratched == 0:
        print("  Nothing matched this cycle")
        return

    if changed_venues:
        # going feeds wpr_going as a live model input - a real track
        # condition change makes every not-yet-run projection at that
        # meeting stale until this recomputes it. Scoped to just the
        # changed venue(s), not the whole day (~30s vs ~75s+ measured for a
        # typical multi-meeting day - see CLAUDE.md's Current state note),
        # since this runs on the same tight 5-min cycle as everything else
        # here. Best-effort: compute_wpr_projection() itself is fail-safe
        # (returns runners_df unchanged on any internal error).
        t0 = time.time()
        runners_df = td.compute_wpr_projection(runners_df, target_date, target_venues=changed_venues)
        print(f"  WPR recompute for {sorted(changed_venues)} took {time.time()-t0:.1f}s")

    td.save_runners(runners_df)
    if n_result_rows:
        print(f"  Wrote {n_result_rows} TAB result rows")
    if n_condition_rows:
        print(f"  Updated conditions for {n_condition_rows} runner rows across {len(conditions)} meetings")
    if n_priced:
        print(f"  Updated fixed_win_price for {n_priced} runners")
    if n_scratched:
        print(f"  {n_scratched} newly late-scratched runner(s) via TAB fixedOdds")

    # The expensive part of a full rebuild (form-history/settling-band/
    # per-race-payload, ~2.5-3 min - see CLAUDE.md's Current state note) is
    # entirely about STATIC data that only the daily pipeline changes -
    # none of it depends on price/result/scratch fields. A going change is
    # the one thing here that genuinely needs the full pipeline (it just
    # recomputed wprp_* fields above, which only rebuild_html() knows how
    # to serialize). Everything else gets the fast, direct JSON patch;
    # patch_data_json() itself falls back (returns False) if anything
    # about it looks unsafe (missing/unparseable JSON, an unrecognized
    # run_id), so this never ships a half-patched payload.
    did_full_rebuild = False
    if changed_venues or not patch_data_json_safe(price_patches, result_patches, scratch_patches):
        rebuild_data_json()
        did_full_rebuild = True
    print(f"  {'Full rebuild' if did_full_rebuild else 'Fast JSON patch (no full rebuild)'} this cycle")

    if push:
        commit_and_push()


def patch_data_json_safe(price_patches, result_patches, scratch_patches):
    """Thin wrapper around toprate_daily.patch_data_json() -- treats any
    exception as "unsafe, fall back to full rebuild" rather than letting a
    patching bug take down the whole cycle."""
    try:
        return td.patch_data_json(price_patches, result_patches, scratch_patches)
    except Exception as e:
        print(f"  patch_data_json failed ({type(e).__name__}: {e}), falling back to full rebuild")
        return False


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--diagnose", action="store_true")
    ap.add_argument("--probe-odds", action="store_true",
                    help="one-off, read-only: inspect where TAB exposes fixed prices (see probe_odds())")
    ap.add_argument("--once", action="store_true", help="single pass (for cron/Task Scheduler)")
    ap.add_argument("--no-push", action="store_true", help="write the CSV but skip git commit/push")
    ap.add_argument("--interval", type=int, default=90,
                    help="seconds between polls in loop mode (default 90)")
    a = ap.parse_args()

    if a.diagnose:
        return diagnose()

    if a.probe_odds:
        return probe_odds()

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
