"""Fetch each declared runner's page data from toprate.au (14 Oct 2026): pedigree and owners, win/place stats by first-up, second-up, distance,
track, track+distance, going, jumps, current jockey and sire/dam-sire wet/dry, rating profiles by period and condition, and the full past-run list.

Source: https://toprate.au/runners/{runId}/__data.json (same login as toprate_race_fetch.py; the race-detail RPCs stay Cloudflare-blocked). One request per
runner, a few in flight, a short pause between requests. Input: data/tr_fields/<date>.json (written by toprate_race_fetch.py). Output:
data/tr_runners/<date>.json.gz, one record per runner, rewritten only when a record changed. A runner already fetched today (UTC date) is skipped,
so the many daily.yml runs in a day cost the requests once and the file changes at most once a day unless a record changed. Files older than --keep-days are removed.

These are TopRate's CURRENT-state aggregates: right for an upcoming race, never to be attached to a race that has already run (tr_field_rows.merge_tr_runners
enforces that).

Environment: TOPRATE_EMAIL, TOPRATE_PASSWORD, TOPRATE_ANON_KEY.
Usage: python toprate_runner_fetch.py [--days 2] [--from YYYY-MM-DD] [--limit N]
"""
import argparse
import gzip
import json
import os
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from datetime import date, datetime, timedelta, timezone
from pathlib import Path

import requests

import toprate_race_fetch as f

IN_DIR = Path(__file__).parent / "data" / "tr_fields"
OUT_DIR = Path(__file__).parent / "data" / "tr_runners"
TIMEOUT = 30
RETRIES = 3
PAUSE = 0.3

BIO = {"horseCountry": "horse_country", "horseColour": "horse_colour", "horseFoaled": "horse_foaled", "dam": "dam", "damCountry": "dam_country",
       "owners": "owners", "trainingLocation": "training_location", "weightHandicap": "weight_handicap_today"}


def fetch_runner(session, run_id):
    url = f"{f.WEB_BASE}/runners/{run_id}/__data.json?x-sveltekit-invalidated=0001"
    headers = {"apikey": os.environ["TOPRATE_ANON_KEY"], "Authorization": f"Bearer {session['access_token']}",
               "Accept": "application/json", "User-Agent": f.BROWSER_HEADERS["User-Agent"], "Referer": f.WEB_BASE + "/"}
    last = None
    for attempt in range(1, RETRIES + 1):
        time.sleep(PAUSE)
        try:
            r = requests.get(url, headers=headers, cookies=f.cookie_pair(session), timeout=TIMEOUT, allow_redirects=False)
        except requests.RequestException as e:
            last = f"request error: {type(e).__name__}"
            time.sleep(2 * attempt)
            continue
        if r.status_code == 404:
            return {"empty": True}, None
        if r.status_code == 200:
            try:
                for node in r.json().get("nodes", []):
                    if node.get("type") == "data" and node.get("data"):
                        d = f.deref(node["data"], 0)
                        if isinstance(d, dict) and d.get("runnerDetail"):
                            return d["runnerDetail"], None
                return {"empty": True}, None            # a page with no runnerDetail (nothing to read yet)
            except ValueError:
                last = "200 but not JSON"
        else:
            last = f"HTTP {r.status_code}"
        time.sleep(2 * attempt)
    return None, last


def compact(rd, base):
    """The record kept per runner: bio, every stats block, rating profiles, distances and the past-run list as TopRate gives them."""
    if rd.get("empty"):
        return {**base, "empty": True}
    rec = {**base}
    for src, dst in BIO.items():
        rec[dst] = rd.get(src)
    rec["stats"] = rd.get("stats")
    rec["rating_profiles"] = rd.get("ratingProfiles")
    rec["distances"] = rd.get("distances")
    rec["form"] = rd.get("form")
    rec["gear_changes"] = rd.get("gearChanges")
    rec["dslr"] = rd.get("dslr")
    return rec


def load_out(path):
    try:
        with gzip.open(path, "rt") as fh:
            return json.load(fh)
    except Exception:
        return {"rows": {}}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--days", type=int, default=2)
    ap.add_argument("--from", dest="start", default=None)
    ap.add_argument("--limit", type=int, default=0, help="stop after N fetches (testing)")
    ap.add_argument("--workers", type=int, default=3)
    ap.add_argument("--keep-days", type=int, default=7)
    a = ap.parse_args()
    email, password, anon = (os.environ.get(k, "").strip() for k in ("TOPRATE_EMAIL", "TOPRATE_PASSWORD", "TOPRATE_ANON_KEY"))
    if not (email and password and anon):
        sys.exit("TOPRATE_EMAIL, TOPRATE_PASSWORD and TOPRATE_ANON_KEY must be set")
    first = datetime.strptime(a.start, "%Y-%m-%d").date() if a.start else date.today()
    dates = [(first + timedelta(days=i)).isoformat() for i in range(a.days)]
    session = f.login(email, password, anon)
    print(f"logged in | token expires {datetime.fromtimestamp(session.get('expires_at', 0)):%H:%M:%S}")
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    today_utc = datetime.now(timezone.utc).date().isoformat()
    done = 0
    for d in dates:
        try:
            rows = [r for r in json.loads((IN_DIR / f"{d}.json").read_text()).get("rows", []) if not r.get("scratched") and r.get("run_id")]
        except Exception:
            print(f"{d}: no race file, skipped")
            continue
        path = OUT_DIR / f"{d}.json.gz"
        out = load_out(path)
        have = out.get("rows", {})
        todo = []
        for r in rows:
            cur = have.get(str(r["run_id"]))
            if cur and str(cur.get("at", "")) >= today_utc:
                continue
            todo.append(r)
        if a.limit:
            todo = todo[: max(0, a.limit - done)]
        base_of = lambda r: {"run_id": r["run_id"], "horse_id": r.get("horse_id"), "horse": r.get("horse"), "venue": r.get("venue"),
                             "race_no": r.get("race_no"), "tab_number": r.get("tab_number"), "date": d}
        with ThreadPoolExecutor(max_workers=a.workers) as ex:
            results = list(ex.map(lambda r: (r, *fetch_runner(session, r["run_id"])), todo))
        new, failed = dict(have), []
        for r, rd, err in results:
            if rd is None:
                failed.append((r["run_id"], err))
                continue
            rec = compact(rd, base_of(r))
            rec["at"] = today_utc
            new[str(r["run_id"])] = rec
        done += len(todo)
        empty = sum(1 for v in new.values() if v.get("empty"))
        print(f"{d}: {len(rows)} runners, fetched {len(results) - len(failed)}, skipped fresh {len(rows) - len(todo)}, failed {len(failed)}, empty pages {empty}")
        for rid, err in failed[:5]:
            print(f"   runner {rid}: {err}")
        if results and new != have:
            with gzip.GzipFile(path, "wb", mtime=0) as gz:
                gz.write(json.dumps({"date": d, "rows": new}, separators=(",", ":"), sort_keys=True, default=str).encode())
        if a.limit and done >= a.limit:
            break
    cutoff = (date.today() - timedelta(days=a.keep_days)).isoformat()
    for p in OUT_DIR.glob("*.json.gz"):
        if p.name[:10] < cutoff:
            p.unlink()


if __name__ == "__main__":
    main()
