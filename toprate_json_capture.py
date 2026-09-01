"""
toprate_json_capture.py
-----------------------
Rich per-runner form capture from the TopRate SvelteKit __data.json
endpoint.

WHY THIS MODULE EXISTS
  toprate_daily.py builds wpr_form_history.csv from the thin RPC feed
  (get_race_wpr_chart), which does NOT carry starters / class / sectional
  ratings. The richer per-runner endpoint:

    https://toprate.au/runners/{run_id}/__data.json?x-sveltekit-invalidated=0001

  does carry all of it. backfill_sectionals.py already reads that endpoint
  as a separate after-the-fact pass. This module factors that fetch +
  parse logic out so the DAILY run can capture the rich data natively.

STAGE 1 STATUS (per SCOPING_daily_json_capture.md)
  This module is NOT yet wired into the daily flow. It provides the
  building blocks - fetch, parse, extract - plus a manual test entry
  point so one runner can be fetched and inspected before any wiring.
  Stage 2 (rate-limit decision) and Stage 3 (wiring) come later.

AUTH
  The __data.json route needs the JWT as a Bearer header AND the
  sb-api-auth-token.0/.1 cookie pair, rebuilt from the full Supabase
  session object. This module imports toprate_daily.login() for the JWT
  and reads toprate_daily._SESSION_OBJ for the session object, so there
  is ONE login path shared across the project.

NO EM DASHES policy: hyphens only in this file.
"""

import base64
import json
import sys
import threading
import time

import requests
import urllib3

urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

WEB_BASE = "https://toprate.au"
VERIFY_SSL = False
TIMEOUT = 30
MAX_RETRIES = 3

# The 13 sectionalRating keys -> CSV column names. Matches
# backfill_sectionals.py SECT_MAP exactly so the two write identical
# columns into wpr_form_history.csv.
SECT_MAP = {
    "individualTime":            "sect_i_time",
    "leaderEarlySpeed":          "sect_ld_early",
    "individualEarlySpeed":      "sect_i_early",
    "individualTo600mSpeed":     "sect_i_to600",
    "individualTo800mSpeed":     "sect_i_to800",
    "individualLast200mSpeed":   "sect_i_l200",
    "individualLast400mSpeed":   "sect_i_l400",
    "individualLast600mSpeed":   "sect_i_l600",
    "individualLast800mSpeed":   "sect_i_l800",
    "individual400mTo200mSpeed": "sect_i_400_200",
    "individual600mTo400mSpeed": "sect_i_600_400",
    "individual800mTo400mSpeed": "sect_i_800_400",
    "individual800mTo600mSpeed": "sect_i_800_600",
}
SECT_COLS = list(SECT_MAP.values())

# Non-sectional columns the rich capture adds. Matches backfill EXTRA_COLS.
EXTRA_COLS = [
    "field_size", "weight_handicap", "race_class", "is_letup", "is_spell",
    "race_id", "meeting_id", "blinkers_on", "gear_changes",
    "comments_steward", "comments_video", "time_last600m",
    "jockey", "trainer", "is_jumpout",
]

# Core per-run columns that the THIN feed (get_race_wpr_chart) already
# supplies for TODAY's runners (see toprate_daily._WPR_FORM_FIELDS - keep
# these two lists in sync, same raw API key names). The rich __data.json
# 'form' array carries these same fields for EVERY past run it returns, not
# just the ones the thin feed happened to include, so extracting them here
# lets the rich fetch backfill core columns on existing (thin) rows AND
# supply everything needed to create brand-new rows for runs the thin feed
# never surfaced at all (see toprate_daily._enrich_form_history_rich). Only
# "date" is left out - that is handled separately (it is the join key).
CORE_COLS = [
    "formNumber", "raceNumber",
    "track", "trackCode", "trackGrading",
    "distance", "going",
    "wpr", "weightCarried", "barrier", "priceStarting",
    "positionSettled", "position800m", "position600m",
    "position400m", "position200m", "positionFinish",
    "margin800m", "margin600m", "margin400m", "margin200m", "marginFinish",
    "raceShapeEarly", "raceShapeMid", "raceShapeLate",
    "winner", "isBarrierTrial",
]
ALL_COLS = SECT_COLS + EXTRA_COLS + CORE_COLS


def _scalar(v):
    """Keep only JSON-scalar values (str/int/float/bool); anything else
    (an undereferenced pointer, a nested dict/list) becomes None rather than
    being written into the CSV as garbage."""
    return v if isinstance(v, (str, int, float, bool)) else None


# ---------------------------------------------------------------------------
# Auth - cookie pair built from toprate_daily's shared session object
# ---------------------------------------------------------------------------
def _cookie_pair(session_obj):
    """Rebuild the sb-api-auth-token.0/.1 cookie pair from the Supabase
    session object, matching the browser's base64-prefixed split format.
    Splitting anywhere under the 4KB cookie limit works as long as the
    concatenation order is .0 then .1."""
    raw = json.dumps(session_obj, separators=(",", ":"))
    enc = "base64-" + base64.b64encode(raw.encode()).decode()
    half = (len(enc) + 1) // 2
    return {
        "sb-api-auth-token.0": enc[:half],
        "sb-api-auth-token.1": enc[half:],
    }


_LOGIN_LOCK = threading.Lock()


def _auth_bits():
    """Return (headers, cookies) for the __data.json route, using
    toprate_daily's login() and shared _SESSION_OBJ. Logs in if needed.

    Re-login is serialized with a lock: when a long run's token expires, many
    parallel workers hit the login bounce at the same moment and would
    otherwise all call login() simultaneously (a login storm). The lock lets
    the first thread re-authenticate while the rest wait and then reuse the
    freshly populated session."""
    import toprate_daily as td
    if td._SESSION_OBJ is None:
        with _LOGIN_LOCK:
            # Re-check inside the lock: another thread may have logged in while
            # we were waiting, in which case we skip a redundant login.
            if td._SESSION_OBJ is None:
                td.login()  # populates td._SESSION_OBJ as a side effect
    session = td._SESSION_OBJ
    token = session.get("access_token")
    headers = {
        "apikey": td.ANON_KEY,
        "Authorization": f"Bearer {token}",
        "Accept": "application/json",
    }
    return headers, _cookie_pair(session)


# ---------------------------------------------------------------------------
# SvelteKit __data.json parsing
# ---------------------------------------------------------------------------
# The response is a de-duplicated structure: nodes[k].data is a flat array,
# data[0] is the root index map, every value in any object/list is an
# integer POINTER into that array. Everything must be resolved through it.

# One-shot structural diagnostic. When a payload cannot be parsed we print
# the shape of the response ONCE (not per-runner - that would be 1600+ lines
# of noise) so a TopRate format change is immediately visible in the log.
_DIAG_DONE = False


def _diag_payload(payload):
    global _DIAG_DONE
    if _DIAG_DONE:
        return
    _DIAG_DONE = True
    try:
        # Surface a SvelteKit application-level redirect explicitly: knowing
        # the target tells us whether it is an auth bounce (/login) or a
        # canonical-URL redirect (followable to real data).
        if isinstance(payload, dict) and payload.get("type") == "redirect":
            print("  [diag] __data.json parse failed - dumping structure once:")
            print(f"  [diag] top-level keys: {list(payload.keys())}")
            print(f"  [diag] REDIRECT location: {payload.get('location')!r}")
            return
        nodes = payload.get("nodes")
        print("  [diag] __data.json parse failed - dumping structure once:")
        print(f"  [diag] top-level keys: {list(payload.keys())}")
        if not isinstance(nodes, list):
            print(f"  [diag] 'nodes' is not a list: {type(nodes).__name__}")
            return
        print(f"  [diag] node count: {len(nodes)}")
        for i, n in enumerate(nodes):
            if isinstance(n, dict) and isinstance(n.get("data"), list):
                data = n["data"]
                root = data[0] if data else None
                keys = list(root.keys())[:40] if isinstance(root, dict) else root
                print(f"  [diag] node[{i}] data[0] keys: {keys}")
            elif isinstance(n, dict):
                print(f"  [diag] node[{i}] dict keys (no data list): {list(n.keys())}")
            else:
                print(f"  [diag] node[{i}] type: {type(n).__name__}")
    except Exception as e:
        print(f"  [diag] diagnostic itself failed: {e}")


def _is_login_bounce(payload):
    """True when the __data.json is the LOGIN page rather than runnerDetail.
    The session expired mid-run, so SvelteKit served the login route at HTTP
    200. Signature (from the diagnostic): a data node whose root index map
    contains 'login' and there is no runnerDetail anywhere. Detecting this lets
    the caller re-authenticate and retry instead of treating it as a permanent
    parse failure."""
    if not isinstance(payload, dict):
        return False
    nodes = payload.get("nodes")
    if not isinstance(nodes, list):
        return False
    saw_login = False
    for n in nodes:
        if not (isinstance(n, dict) and isinstance(n.get("data"), list)):
            continue
        data = n["data"]
        root = data[0] if data else None
        if isinstance(root, dict):
            keys = root.keys()
            if "runnerDetail" in keys:
                return False  # real runner data present - not a bounce
            if "login" in keys:
                saw_login = True
    return saw_login


def _parse_data_json(payload):
    """Return (runnerDetail dict, deref function), or None if malformed,
    or the string 'EMPTY' if runnerDetail is null (runner outside the
    served window - not an error, do not retry).

    Newer SvelteKit responses can carry MORE than one data-bearing node
    (e.g. a layout node before the page node). The runner page is not
    necessarily the first one, so we search every data node for the one
    whose root index map actually contains 'runnerDetail', rather than
    taking the first data list and assuming it is the page."""
    nodes = payload.get("nodes")
    if not isinstance(nodes, list) or not nodes:
        _diag_payload(payload)
        return None

    for n in nodes:
        if not (isinstance(n, dict) and isinstance(n.get("data"), list)):
            continue
        data = n["data"]
        if not data:
            continue
        root = data[0]
        if not isinstance(root, dict) or "runnerDetail" not in root:
            continue

        # Bind deref to THIS node's data array (each node has its own).
        def deref(p, _data=data):
            return _data[p] if isinstance(p, int) else p

        rd = deref(root["runnerDetail"])
        if rd is None:
            return "EMPTY"
        if not isinstance(rd, dict):
            return None
        return rd, deref

    # No node carried runnerDetail - structure changed (or key renamed).
    _diag_payload(payload)
    return None


def extract_runs(payload):
    """From a parsed __data.json payload return (horse_id, runs,
    gear_changes_today) where runs is a list of {date, fields} - fields
    being the SECT_COLS + EXTRA_COLS dict for that form run.

    gear_changes_today (Aug 2026 addition - see gear_change ADJ_TERM):
    this runner's gear changes for the CURRENT/upcoming race, a JSON
    list string (same format as the per-run "gear_changes" field inside
    each past form entry below) or None if there are none/unavailable.
    Lives at the TOP LEVEL of the runner object (rd["gearChanges"]),
    NOT inside the "form" array - the "form" array holds only ALREADY-
    RUN races (each entry requires a real sectionalRating dict, which an
    upcoming race can't have), so this top-level field is the only place
    a horse's gear for its NEXT start actually appears on this same
    already-fetched runner page. Confirmed against a real page capture
    (see chat): a runner's "Ear Muffs Off Again, Tongue Tie Off First
    Time" badge for its next start came through as rd["gearChanges"] ->
    ["Ear Muffs Off Again", "Tongue Tie Off First Time"], sibling to
    "form", not inside it.

    Returns (None, [], None) on a malformed payload (caller may retry),
    ('EMPTY', [], None) when runnerDetail is null (do NOT retry)."""
    parsed = _parse_data_json(payload)
    if parsed == "EMPTY":
        return "EMPTY", [], None
    if parsed is None:
        return None, [], None
    rd, deref = parsed

    horse_id = deref(rd.get("horseId"))

    gc_today = deref(rd.get("gearChanges"))
    gear_changes_today = (json.dumps([deref(x) for x in gc_today])
                          if isinstance(gc_today, list) else None)

    form = deref(rd.get("form"))
    if not isinstance(form, list):
        return horse_id, [], gear_changes_today

    # weightHandicap: the weight basis this scrape's wpr figures are
    # adjusted to. One value per scrape, written to every form row.
    weight_handicap = deref(rd.get("weightHandicap"))
    if not isinstance(weight_handicap, (int, float)):
        weight_handicap = None

    out = []
    for fp in form:
        fe = deref(fp)
        if not isinstance(fe, dict):
            continue
        run_date = deref(fe.get("date"))
        sr = deref(fe.get("sectionalRating"))
        if run_date is None or not isinstance(sr, dict):
            continue
        figs = {}
        for src_key, col in SECT_MAP.items():
            v = deref(sr.get(src_key))
            figs[col] = v if isinstance(v, (int, float)) else None

        # field size - the missing piece. Lives on the form entry as
        # 'starters', NOT in sectionalRating.
        starters = deref(fe.get("starters"))
        figs["field_size"] = (starters
                              if isinstance(starters, (int, float))
                              else None)
        figs["weight_handicap"] = weight_handicap

        cls = deref(fe.get("class"))
        figs["race_class"] = cls if isinstance(cls, str) else None

        il = deref(fe.get("isLetup"))
        isp = deref(fe.get("isSpell"))
        figs["is_letup"] = bool(il) if isinstance(il, bool) else None
        figs["is_spell"] = bool(isp) if isinstance(isp, bool) else None

        rid = deref(fe.get("raceId"))
        mid = deref(fe.get("meetingId"))
        figs["race_id"] = rid if isinstance(rid, (int, float)) else None
        figs["meeting_id"] = mid if isinstance(mid, (int, float)) else None

        bo = deref(fe.get("blinkersOn"))
        figs["blinkers_on"] = bool(bo) if isinstance(bo, bool) else None
        gc = deref(fe.get("gearChanges"))
        if isinstance(gc, list):
            figs["gear_changes"] = json.dumps([deref(x) for x in gc])
        else:
            figs["gear_changes"] = None

        cs = deref(fe.get("commentsSteward"))
        cv = deref(fe.get("commentsVideo"))
        figs["comments_steward"] = cs if isinstance(cs, str) else None
        figs["comments_video"] = cv if isinstance(cv, str) else None

        t6 = deref(fe.get("timeLast600m"))
        figs["time_last600m"] = t6 if isinstance(t6, (int, float)) else None

        jk = deref(fe.get("jockey"))
        tr = deref(fe.get("trainer"))
        figs["jockey"] = jk if isinstance(jk, str) else None
        figs["trainer"] = tr if isinstance(tr, str) else None

        jo = deref(fe.get("isJumpout"))
        figs["is_jumpout"] = bool(jo) if isinstance(jo, bool) else None

        # Core per-run fields (see CORE_COLS above) - same raw key names as
        # the thin feed uses, so these merge straight into the same columns.
        # A key genuinely absent from the rich feed (positionSettled, per
        # inspection) just comes through as None like everything else here.
        for k in CORE_COLS:
            figs[k] = _scalar(deref(fe.get(k)))

        out.append({"date": str(run_date), "fields": figs})
    return horse_id, out, gear_changes_today


# ---------------------------------------------------------------------------
# Fetch one runner page
# ---------------------------------------------------------------------------
def fetch_runner(run_id):
    """Fetch and parse one runner-page __data.json.
    Returns (horse_id, runs, gear_changes_today) on success (see
    extract_runs' docstring for gear_changes_today), ('EMPTY', [], None)
    when the runner is not served, or (None, [], None) on a hard
    failure."""
    url = (f"{WEB_BASE}/runners/{run_id}/__data.json"
           f"?x-sveltekit-invalidated=0001")
    last_err = None
    for attempt in range(1, MAX_RETRIES + 1):
        headers, cookies = _auth_bits()
        try:
            resp = requests.get(url, headers=headers, cookies=cookies,
                                 verify=VERIFY_SSL, timeout=TIMEOUT,
                                 allow_redirects=False)
        except requests.RequestException as e:
            last_err = f"request error: {e}"
            time.sleep(2 * attempt)
            continue

        if resp.status_code in (301, 302, 303, 307, 308):
            # redirect to /login means auth was rejected - force re-login
            last_err = f"redirect (auth rejected)"
            import toprate_daily as td
            td._SESSION_OBJ = None
            time.sleep(2 * attempt)
            continue
        if resp.status_code == 401:
            last_err = "401 unauthorized"
            import toprate_daily as td
            td._SESSION_OBJ = None
            time.sleep(2 * attempt)
            continue
        if resp.status_code == 404:
            return None, [], None
        if resp.status_code != 200:
            last_err = f"HTTP {resp.status_code}"
            time.sleep(2 * attempt)
            continue

        try:
            payload = resp.json()
        except ValueError:
            last_err = "response was not JSON"
            time.sleep(2 * attempt)
            continue

        # SvelteKit can return an APPLICATION-level redirect: HTTP 200 with a
        # JSON body {"type":"redirect","location":"..."} rather than an HTTP
        # 30x. The data lives at the location URL, so follow it (once) by
        # re-requesting the redirected __data.json. Without this the payload
        # has no "nodes" and the parse fails ("could not parse runnerDetail").
        if isinstance(payload, dict) and payload.get("type") == "redirect":
            loc = payload.get("location") or ""
            if loc and not loc.startswith(("__redirect_followed",)):
                # Build an absolute __data.json URL from the redirect target.
                if loc.startswith("http"):
                    redir = loc
                elif loc.startswith("/"):
                    redir = f"{WEB_BASE}{loc}"
                else:
                    redir = f"{WEB_BASE}/{loc}"
                # Ensure we request the data route, not the HTML page.
                if "__data.json" not in redir:
                    redir = redir.rstrip("/") + "/__data.json"
                if "x-sveltekit-invalidated" not in redir:
                    sep = "&" if "?" in redir else "?"
                    redir = f"{redir}{sep}x-sveltekit-invalidated=0001"
                try:
                    resp2 = requests.get(redir, headers=headers, cookies=cookies,
                                         verify=VERIFY_SSL, timeout=TIMEOUT,
                                         allow_redirects=False)
                    if resp2.status_code == 200:
                        payload = resp2.json()
                    else:
                        last_err = f"redirect target HTTP {resp2.status_code}"
                        time.sleep(2 * attempt)
                        continue
                except (requests.RequestException, ValueError) as e:
                    last_err = f"redirect follow failed: {e}"
                    time.sleep(2 * attempt)
                    continue
            else:
                # Redirect with no usable location - treat as not-served, not a
                # hard parse failure (avoids the noisy error spam).
                return "EMPTY", [], None

        # Login bounce: the session expired mid-run, so the route returns
        # HTTP 200 but the page node is the LOGIN page, not runnerDetail. The
        # diagnostic shows this as a 'login' key in a data node. This is NOT a
        # permanent parse failure (re-auth fixes it), so force a re-login and
        # retry rather than failing fast. Long runs (~9 min) outlive a single
        # token, so the tail of the field hits this.
        if _is_login_bounce(payload):
            last_err = "login bounce (session expired) - re-authenticating"
            import toprate_daily as td
            td._SESSION_OBJ = None
            time.sleep(2 * attempt)
            continue

        horse_id, runs, gear_changes_today = extract_runs(payload)
        if horse_id == "EMPTY":
            return "EMPTY", [], None
        if horse_id is None:
            # Deterministic parse failure on a valid 200 JSON response:
            # retrying the same page returns the same structure, so fail
            # fast rather than burning retry sleeps across the whole field
            # (that is what pushed the daily run toward the 15-min timeout).
            print(f"  fetch_runner({run_id}) failed: could not parse runnerDetail/form")
            return None, [], None
        return horse_id, runs, gear_changes_today

    print(f"  fetch_runner({run_id}) failed: {last_err}")
    return None, [], None


# ---------------------------------------------------------------------------
# Manual test entry point (Stage 1 verification)
# ---------------------------------------------------------------------------
# Usage:  python toprate_json_capture.py <run_id>
# Fetches one runner page and prints what was parsed, so the fetch + parse
# + auth can be verified before any wiring into the daily flow.
if __name__ == "__main__":
    if len(sys.argv) < 2:
        sys.exit("Usage: python toprate_json_capture.py <run_id>")
    rid = sys.argv[1]
    print(f"Fetching runner page {rid} ...")
    horse_id, runs, gear_changes_today = fetch_runner(rid)
    if horse_id == "EMPTY":
        print("Result: EMPTY - runnerDetail null (runner not served).")
        sys.exit(0)
    if horse_id is None:
        print("Result: hard failure - see message above.")
        sys.exit(1)
    print(f"horse_id = {horse_id}")
    print(f"gear_changes_today = {gear_changes_today}")
    print(f"{len(runs)} form runs parsed:\n")
    for r in runs:
        f = r["fields"]
        print(f"  {r['date']}  field_size={f.get('field_size')}  "
              f"class={f.get('race_class')}  "
              f"sect_i_time={f.get('sect_i_time')}  "
              f"jockey={f.get('jockey')}")
    # show the full field set of the first run so every captured column
    # can be eyeballed
    if runs:
        print("\nFull field set of the first run:")
        for k in ALL_COLS:
            print(f"  {k:20s} = {runs[0]['fields'].get(k)}")
