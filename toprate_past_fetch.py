"""Backfill TopRate's numbers (wpr_nett, TopRate rating, speed, form factor, jockey rating) for races that have already run (14 Oct 2026).

toprate_race_fetch.py only reads the calendar of UPCOMING races, so every race before 14 Oct has no nett on the dashboard. This reads the race ids
already in runners.csv (TopRate's own ids, below 7 trillion run ids are racing.com placeholders and are skipped), fetches each race's page the same way
and writes data/tr_past/<date>.json = {"date", "fetched", "rows": {run_id: {column: value}}}. tr_field_rows.merge_tr_past() fills the blanks in
runners.csv from those files (never overwrites a value). Read-only against toprate.au, same pacing as the daily fetch.

CAUTION: a past race page may show the number as recomputed after the result, not as it stood before the jump. Treat backfilled nett as display only.

Environment: TOPRATE_EMAIL, TOPRATE_PASSWORD, TOPRATE_ANON_KEY.  Usage: python toprate_past_fetch.py [--days 25] [--to YYYY-MM-DD] [--workers 3]
"""
import argparse
import json
import os
import sys
from concurrent.futures import ThreadPoolExecutor
from datetime import date, datetime, timedelta
from pathlib import Path

import toprate_race_fetch as F

OUT = Path(__file__).parent / "data" / "tr_past"
PLACEHOLDER_MIN = 7_000_000_000_000
COLS = {"wpr_nett": "wpr_nett", "toprate_rating": "toprate_rating", "speed_rating": "speed_rating", "pfm_score": "pfm_score",
        "pfm_score_rank": "pfm_score_rank", "jockey_rating": "jockey_rating", "toprate_price": "toprate_price"}


def race_ids_by_date(dates):
    import runners_io
    df = runners_io.read_runners()
    df["date"] = df["date"].astype(str).str[:10]
    df = df[df.date.isin(dates)]
    df = df[(df.race_id < PLACEHOLDER_MIN) & (df.run_id < PLACEHOLDER_MIN)]
    out = {}
    for d, g in df.groupby("date"):
        # a race whose runners all have nett already needs nothing
        need = g[g.wpr_nett.isna()] if "wpr_nett" in g.columns else g
        out[d] = sorted({int(x) for x in need.race_id.dropna()})
    return {d: v for d, v in out.items() if v}


def scan(lo, hi, dates, workers):
    """Walk TopRate race ids lo..hi (one attempt each, ids that are not a race answer an error) and keep the races on `dates`. Used for days whose rows
    carry racing.com ids, so there is no TopRate id to look up. Writes data/tr_past/<date>.json with each runner's TopRate identity under "_id"
    (race_id, horse, venue, race_no) next to its numbers, for tr_field_rows.remap_ids()."""
    import requests
    email, password, anon = (os.environ[k].strip() for k in ("TOPRATE_EMAIL", "TOPRATE_PASSWORD", "TOPRATE_ANON_KEY"))
    session = F.login(email, password, anon)
    state = {"s": session}
    found, errs = {}, {}

    def one(rid):
        if state["s"].get("expires_at", 0) - datetime.now().timestamp() < 300:
            state["s"] = F.login(email, password, anon)
        sess = state["s"]
        F.time.sleep(F.PAUSE)
        url = f"{F.WEB_BASE}/races/{rid}/__data.json?x-sveltekit-invalidated=0001"
        headers = {"apikey": anon, "Authorization": f"Bearer {sess['access_token']}", "Accept": "application/json",
                   "User-Agent": F.BROWSER_HEADERS["User-Agent"], "Referer": F.WEB_BASE + "/"}
        try:
            r = requests.get(url, headers=headers, cookies=F.cookie_pair(sess), timeout=F.TIMEOUT, allow_redirects=False)
            if r.status_code != 200:
                return rid, None, f"HTTP {r.status_code}"
            return rid, F.parse_page(r.json()), None
        except (requests.RequestException, ValueError) as e:
            return rid, None, type(e).__name__

    with ThreadPoolExecutor(max_workers=workers) as ex:
        for n, (rid, page, err) in enumerate(ex.map(one, range(lo, hi + 1))):
            if err:
                errs[err] = errs.get(err, 0) + 1
            if page:
                for r in F.runner_rows(page):
                    if r.get("date") in dates and r.get("run_id") is not None:
                        vals = {c: r.get(k) for c, k in COLS.items() if r.get(k) is not None}
                        vals["_id"] = {"race_id": r["race_id"], "horse": r["horse"], "venue": r["venue"], "race_no": r["race_no"]}
                        found.setdefault(r["date"], {})[str(r["run_id"])] = vals
            if n % 500 == 0:
                print(f"  scanned {n}/{hi - lo + 1}, {sum(len(v) for v in found.values())} runners on {sorted(found)}", flush=True)
    print("errors by kind:", errs)
    OUT.mkdir(parents=True, exist_ok=True)
    for d, rows in found.items():
        nett = sum(1 for v in rows.values() if "wpr_nett" in v)
        print(f"{d}: {len(rows)} runners, {len({v['_id']['race_id'] for v in rows.values()})} races, wpr_nett on {nett}")
        (OUT / f"{d}.json").write_text(json.dumps({"date": d, "fetched": datetime.utcnow().isoformat() + "Z", "rows": rows}, separators=(",", ":")))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--scan-from", type=int, default=None, help="scan TopRate race ids from here (with --scan-to and --scan-dates)")
    ap.add_argument("--scan-to", type=int, default=None)
    ap.add_argument("--scan-dates", default="2026-10-12,2026-10-13")
    ap.add_argument("--days", type=int, default=25)
    ap.add_argument("--to", default=None, help="last date (default yesterday, Melbourne)")
    ap.add_argument("--workers", type=int, default=3)
    a = ap.parse_args()
    email, password, anon = (os.environ.get(k, "").strip() for k in ("TOPRATE_EMAIL", "TOPRATE_PASSWORD", "TOPRATE_ANON_KEY"))
    if not (email and password and anon):
        sys.exit("TOPRATE_EMAIL, TOPRATE_PASSWORD and TOPRATE_ANON_KEY must be set")
    if a.scan_from is not None:
        return scan(a.scan_from, a.scan_to, set(a.scan_dates.split(",")), a.workers)
    if a.to:
        last = datetime.strptime(a.to, "%Y-%m-%d").date()
    else:
        from zoneinfo import ZoneInfo
        last = datetime.now(ZoneInfo("Australia/Melbourne")).date() - timedelta(days=1)
    dates = {(last - timedelta(days=i)).isoformat() for i in range(a.days)}
    ids = race_ids_by_date(dates)
    print(f"{len(ids)} dates, {sum(len(v) for v in ids.values())} races to fetch")
    session = F.login(email, password, anon)
    OUT.mkdir(parents=True, exist_ok=True)
    for d in sorted(ids):
        # the token lasts about an hour; log in again when it is close to expiring
        if session.get("expires_at", 0) - datetime.now().timestamp() < 600:
            session = F.login(email, password, anon)
        with ThreadPoolExecutor(max_workers=a.workers) as ex:
            results = list(ex.map(lambda rid: (rid, *F.fetch_race(session, rid)), ids[d]))
        rows, failed = {}, []
        for rid, page, err in results:
            if not page:
                failed.append((rid, err))
                continue
            for r in F.runner_rows(page):
                vals = {c: r.get(k) for c, k in COLS.items() if r.get(k) is not None}
                if r.get("run_id") is not None and vals:
                    rows[str(r["run_id"])] = vals
        nett = sum(1 for v in rows.values() if "wpr_nett" in v)
        print(f"{d}: {len(ids[d])} races, {len(failed)} failed, {len(rows)} runners with numbers, wpr_nett on {nett}", flush=True)
        for rid, err in failed[:5]:
            print(f"   race {rid}: {err}")
        if rows:
            (OUT / f"{d}.json").write_text(json.dumps({"date": d, "fetched": datetime.utcnow().isoformat() + "Z", "rows": rows},
                                                      separators=(",", ":")))


if __name__ == "__main__":
    main()
