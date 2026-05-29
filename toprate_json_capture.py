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
ALL_COLS = SECT_COLS + EXTRA_COLS


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


def _auth_bits():
    """Return (headers, cookies) for the __data.json route, using
    toprate_daily's login() and shared _SESSION_OBJ. Logs in if needed."""
    import toprate_daily as td
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
    """From a parsed __data.json payload return (horse_id, runs) where
    runs is a list of {date, fields} - fields being the SECT_COLS +
    EXTRA_COLS dict for that form run.
    Returns (None, []) on a malformed payload (caller may retry),
    ('EMPTY', []) when runnerDetail is null (do NOT retry)."""
    parsed = _parse_data_json(payload)
    if parsed == "EMPTY":
        return "EMPTY", []
    if parsed is None:
        return None, []
    rd, deref = parsed

    horse_id = deref(rd.get("horseId"))
    form = deref(rd.get("form"))
    if not isinstance(form, list):
        return horse_id, []

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

        out.append({"date": str(run_date), "fields": figs})
    return horse_id, out


# ---------------------------------------------------------------------------
# Fetch one runner page
# ---------------------------------------------------------------------------
def fetch_runner(run_id):
    """Fetch and parse one runner-page __data.json.
    Returns (horse_id, runs) on success, ('EMPTY', []) when the runner is
    not served, or (None, []) on a hard failure."""
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
            return None, []
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

        horse_id, runs = extract_runs(payload)
        if horse_id == "EMPTY":
            return "EMPTY", []
        if horse_id is None:
            # Deterministic parse failure on a valid 200 JSON response:
            # retrying the same page returns the same structure, so fail
            # fast rather than burning retry sleeps across the whole field
            # (that is what pushed the daily run toward the 15-min timeout).
            print(f"  fetch_runner({run_id}) failed: could not parse runnerDetail/form")
            return None, []
        return horse_id, runs

    print(f"  fetch_runner({run_id}) failed: {last_err}")
    return None, []


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
    horse_id, runs = fetch_runner(rid)
    if horse_id == "EMPTY":
        print("Result: EMPTY - runnerDetail null (runner not served).")
        sys.exit(0)
    if horse_id is None:
        print("Result: hard failure - see message above.")
        sys.exit(1)
    print(f"horse_id = {horse_id}")
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
