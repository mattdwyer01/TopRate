"""Fetch declared fields and TopRate's pre-race numbers from toprate.au race pages (14 Oct 2026).

Replaces the retired race-detail RPCs (`/rest/v1/rpc/get_race_*`, Cloudflare 403 since about 5 Oct 2026) with the website's own SvelteKit
data route, `https://toprate.au/races/{raceId}/__data.json`, which answers 200 with the same login. Read-only: logs in with the account in
TOPRATE_EMAIL / TOPRATE_PASSWORD, reads the calendar, fetches each race page once and writes one JSON file per date. Normal request volume
(a few requests in flight, a short pause between them); TopRate has said automated access to the account is fine.

wpr_nett is the page's `raceUser.runAdjustments[].defaults.wprBase` (checked 14 Oct 2026 against the archived wpr_nett of all six runners
of Balaklava R1 on 16 Sep, exact match), speed_rating is `defaults.speed`. A runner with no rated history has no wprBase (None).

Environment: TOPRATE_EMAIL, TOPRATE_PASSWORD, TOPRATE_ANON_KEY (the site's public Supabase key, same one the website sends).
Usage: python toprate_race_fetch.py [--days 2] [--from YYYY-MM-DD] [--out data/tr_fields] [--workers 3]
"""
import argparse
import base64
import json
import os
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from datetime import date, datetime, timedelta
from pathlib import Path

import requests

API_BASE = "https://api.toprate.au"
WEB_BASE = "https://toprate.au"
# Cloudflare in front of the API rejects clients that do not look like the website's own browser calls.
BROWSER_HEADERS = {
    "User-Agent": ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) "
                   "Chrome/130.0.0.0 Safari/537.36"),
    "Origin": WEB_BASE, "Referer": WEB_BASE + "/",
    "Accept": "*/*", "Accept-Language": "en-AU,en;q=0.9",
    "Sec-Fetch-Mode": "cors", "Sec-Fetch-Site": "same-site", "Sec-Fetch-Dest": "empty",
    "sec-ch-ua": '"Chromium";v="130", "Google Chrome";v="130", "Not?A_Brand";v="99"',
    "sec-ch-ua-mobile": "?0", "sec-ch-ua-platform": '"Windows"',
    "x-client-info": "supabase-js-web/2",
}
TIMEOUT = 30
RETRIES = 3
PAUSE = 0.3  # seconds between page requests per worker


def login(email, password, anon_key):
    r = requests.post(f"{API_BASE}/auth/v1/token?grant_type=password",
                      headers={**BROWSER_HEADERS, "apikey": anon_key, "Authorization": f"Bearer {anon_key}",
                               "Content-Type": "application/json"},
                      json={"email": email, "password": password}, timeout=TIMEOUT)
    r.raise_for_status()
    data = r.json()
    if not data.get("access_token"):
        raise RuntimeError("login returned no access token")
    return data


def cookie_pair(session):
    """The website's sb-api-auth-token.0/.1 cookie pair, built from the whole session object."""
    enc = "base64-" + base64.b64encode(json.dumps(session, separators=(",", ":")).encode()).decode()
    half = (len(enc) + 1) // 2
    return {"sb-api-auth-token.0": enc[:half], "sb-api-auth-token.1": enc[half:]}


def calendar(session, anon_key):
    r = requests.post(f"{API_BASE}/rest/v1/rpc/get_calendar_upcoming",
                      headers={**BROWSER_HEADERS, "apikey": anon_key, "Authorization": f"Bearer {session['access_token']}",
                               "Content-Type": "application/json"},
                      json={}, timeout=TIMEOUT)
    r.raise_for_status()
    return r.json()


def deref(data, i, depth=14, seen=()):
    """Resolve SvelteKit's de-duplicated data array: every value inside an object or list is an integer pointer into `data`."""
    if depth < 0 or i in seen:
        return None
    v = data[i]

    def ptr(p):
        if isinstance(p, int) and not isinstance(p, bool) and 0 <= p < len(data):
            return deref(data, p, depth - 1, seen + (i,))
        return p

    if isinstance(v, dict):
        return {k: ptr(p) for k, p in v.items()}
    if isinstance(v, list):
        return [ptr(p) for p in v]
    return v


def parse_page(payload):
    """Return the race page dict (raceId, raceRecord, raceUser, raceResult, raceFields) from a __data.json payload, or None."""
    for node in payload.get("nodes", []):
        if node.get("type") == "data" and node.get("data"):
            d = deref(node["data"], 0)
            if isinstance(d, dict) and d.get("raceFields") is not None:
                return d
    return None


def runner_rows(page):
    rec = page.get("raceRecord") or {}
    meet = rec.get("meetingSummary") or {}
    race = rec.get("raceSummary") or {}
    adj = {a.get("runId"): (a.get("defaults") or {}) for a in ((page.get("raceUser") or {}).get("runAdjustments") or [])}
    rows = []
    for f in page.get("raceFields") or []:
        d = adj.get(f.get("runId"), {})
        ls = f.get("lastStart") or {}
        rows.append({
            "race_id": page.get("raceId"), "run_id": f.get("runId"), "date": rec.get("date"),
            "venue": meet.get("venue"), "state": meet.get("state"), "going": race.get("going") or meet.get("going"),
            "track_grading": race.get("trackGrading"), "rail": meet.get("railPosition"),
            "race_no": race.get("number"), "race_name": race.get("name"), "race_class": race.get("class"),
            "distance": race.get("distance"), "start_time": race.get("startTime"), "prize_money": race.get("prizeMoney"),
            "weight_restriction": race.get("weightRestriction"), "age_restriction": race.get("ageRestriction"),
            "horse": f.get("horse"), "horse_id": f.get("horseId"), "silk_url": f.get("silksURL"), "tab_number": f.get("tabNumber"), "barrier": f.get("barrier"),
            "jockey": f.get("jockey"), "jockey_id": f.get("jockeyId"), "trainer": f.get("trainer"), "trainer_id": f.get("trainerId"),
            "horse_age": f.get("horseAge"), "horse_sex": f.get("horseSex"), "sire": f.get("sire"), "sire_of_dam": f.get("sireOfDam"),
            "weight": f.get("weightHandicap"), "wfa": f.get("wfa"), "handicap_rating": f.get("handicapRating"),
            "scratched": bool(f.get("isScratched")), "emergency": bool(f.get("isEmergency")),
            # TopRate numbers
            "wpr_nett": d.get("wprBase"), "speed_rating": d.get("speed") or f.get("speed"), "iap_value": d.get("iapValue"),
            "toprate_rating": f.get("topRateRating"), "toprate_price": f.get("topRatePrice"),
            "pfm_score": f.get("pfmScore"), "pfm_score_rank": f.get("pfmScoreRank"), "jockey_rating": f.get("jockeyRating"),
            # market
            "fixed_win_price": f.get("fixedWinPrice"), "fixed_win_opening": f.get("fixedWinOpening"),
            "fixed_win_top_fluc": f.get("fixedWinTopFluc"),
            # first-up / spell
            "dslr": f.get("dslr"), "is_spell": f.get("isSpell"), "is_letup": f.get("isLetUp", f.get("isLetup")),
            "runs_from_spell": f.get("runsFromSpell"), "last4": f.get("last4"), "last10": f.get("last10"),
            "career_starts": (f.get("career") or {}).get("starts"), "career_wins": (f.get("career") or {}).get("wins"),
            "career_places": (f.get("career") or {}).get("places"),
            "last_start": ls or None,
            "accepted_at": f.get("acceptedAt"),
        })
    return rows


def fetch_race(session, race_id):
    url = f"{WEB_BASE}/races/{race_id}/__data.json?x-sveltekit-invalidated=0001"
    headers = {"apikey": os.environ["TOPRATE_ANON_KEY"], "Authorization": f"Bearer {session['access_token']}",
               "Accept": "application/json", "User-Agent": BROWSER_HEADERS["User-Agent"], "Referer": WEB_BASE + "/"}
    last = None
    for attempt in range(1, RETRIES + 1):
        time.sleep(PAUSE)
        try:
            r = requests.get(url, headers=headers, cookies=cookie_pair(session), timeout=TIMEOUT, allow_redirects=False)
        except requests.RequestException as e:
            last = f"request error: {type(e).__name__}"
            time.sleep(2 * attempt)
            continue
        if r.status_code == 200:
            try:
                page = parse_page(r.json())
            except ValueError:
                page = None
            if page:
                return page, None
            last = "200 but no race data (login bounce or format change)"
        else:
            last = f"HTTP {r.status_code}"
        time.sleep(2 * attempt)
    return None, last


def race_ids_for(cal, dates):
    out = {}
    for day in cal if isinstance(cal, list) else []:
        d = day.get("date", "")
        if d not in dates:
            continue
        for m in day.get("meetings", []):
            if m.get("isJumpout"):
                continue
            for r in m.get("races", []):
                if r.get("raceId") and not r.get("isAbandoned"):
                    out.setdefault(d, []).append(r["raceId"])
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--days", type=int, default=2, help="how many days from --from (default 2: today and tomorrow)")
    ap.add_argument("--from", dest="start", default=None, help="first date, YYYY-MM-DD (default: today, local time)")
    ap.add_argument("--out", default="data/tr_fields")
    ap.add_argument("--workers", type=int, default=3)
    a = ap.parse_args()
    email, password, anon = (os.environ.get(k, "").strip() for k in ("TOPRATE_EMAIL", "TOPRATE_PASSWORD", "TOPRATE_ANON_KEY"))
    if not (email and password and anon):
        sys.exit("TOPRATE_EMAIL, TOPRATE_PASSWORD and TOPRATE_ANON_KEY must be set")
    first = datetime.strptime(a.start, "%Y-%m-%d").date() if a.start else date.today()
    dates = {(first + timedelta(days=i)).isoformat() for i in range(a.days)}
    session = login(email, password, anon)
    print(f"logged in | token expires {datetime.fromtimestamp(session.get('expires_at', 0)):%H:%M:%S}")
    ids = race_ids_for(calendar(session, anon), dates)
    out_dir = Path(a.out)
    out_dir.mkdir(parents=True, exist_ok=True)
    for d in sorted(ids):
        with ThreadPoolExecutor(max_workers=a.workers) as ex:
            results = list(ex.map(lambda rid: (rid, *fetch_race(session, rid)), ids[d]))
        rows, failed = [], []
        for rid, page, err in results:
            if page:
                rows.extend(runner_rows(page))
            else:
                failed.append((rid, err))
        nett = sum(1 for r in rows if r["wpr_nett"] is not None)
        print(f"{d}: {len(ids[d])} races, {len(failed)} failed, {len(rows)} runners, wpr_nett on {nett}")
        for rid, err in failed[:10]:
            print(f"   race {rid}: {err}")
        (out_dir / f"{d}.json").write_text(json.dumps({"date": d, "fetched": datetime.utcnow().isoformat() + "Z", "rows": rows,
                                                       "failed": [{"race_id": r, "error": e} for r, e in failed]},
                                                      separators=(",", ":"), default=str))
    if not ids:
        print("no races found for", sorted(dates))


if __name__ == "__main__":
    main()
