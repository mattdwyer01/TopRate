"""Post-race numbers from TopRate's race pages for the meeting review (21 Oct 2026).
A resulted race's page carries `raceResult.runners` for the WHOLE field (not only horses whose runner page was fetched again): the run's rating at the weight carried
(`atw`) and plain (`wpr`), positions at 800m and 400m, finish position and margin, starting price, weight carried, comments and `sectionalRating` (empty so far), and
`raceResult.wprStatus` (Preliminary at 2 days). Written to data/tr_results/<date>.json.gz as {race_id: {meta..., runners: [...]}}, one file per day, rewritten when it changes.
Read-only against toprate.au at the daily fetch's pace. Environment: TOPRATE_EMAIL, TOPRATE_PASSWORD, TOPRATE_ANON_KEY.
Usage: python toprate_result_fetch.py [--days 7] [--to YYYY-MM-DD] [--workers 3] [--refetch]"""
import argparse
import gzip
import json
import os
import sys
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timedelta
from pathlib import Path

import toprate_race_fetch as F

OUT = Path(__file__).parent / "data" / "tr_results"
PLACEHOLDER_MIN = 7_000_000_000_000
KEEP = ["runId", "horseId", "horse", "tabNumber", "barrier", "atw", "wpr", "weightCarried", "positionFinish", "marginFinish", "position800m", "position400m",
        "priceStarting", "priceTop", "sectionalRating", "commentsVideo", "commentsSteward", "gearChanges", "jockey", "trainer"]


def race_ids_by_date(dates):
    import runners_io
    df = runners_io.read_runners()
    df["date"] = df["date"].astype(str).str[:10]
    df = df[df.date.isin(dates) & (df.race_id < PLACEHOLDER_MIN)]
    return {d: sorted({int(x) for x in g.race_id.dropna()}) for d, g in df.groupby("date")}


def pack(page):
    rr = page.get("raceResult") or {}
    runners = rr.get("runners") or []
    if not runners:
        return None
    rec = page.get("raceRecord") or {}
    meet = rec.get("meetingSummary") or {}
    return {"venue": meet.get("venue"), "race": rr.get("number"), "going": rr.get("going"), "grading": rr.get("trackGrading"), "distance": rr.get("distance"),
            "class": rr.get("class"), "wprStatus": rr.get("wprStatus"), "rail": meet.get("railPosition"),
            "runners": [{k: r.get(k) for k in KEEP if r.get(k) not in (None, "", [], {})} for r in runners]}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--days", type=int, default=7)
    ap.add_argument("--to", default=None)
    ap.add_argument("--workers", type=int, default=3)
    ap.add_argument("--refetch", action="store_true", help="fetch races already stored (their rating status may have moved on from Preliminary)")
    a = ap.parse_args()
    email, password, anon = (os.environ.get(k, "").strip() for k in ("TOPRATE_EMAIL", "TOPRATE_PASSWORD", "TOPRATE_ANON_KEY"))
    if not (email and password and anon):
        sys.exit("TOPRATE_EMAIL, TOPRATE_PASSWORD and TOPRATE_ANON_KEY must be set")
    if a.to:
        last = datetime.strptime(a.to, "%Y-%m-%d").date()
    else:
        from zoneinfo import ZoneInfo
        last = datetime.now(ZoneInfo("Australia/Melbourne")).date() - timedelta(days=1)
    dates = {(last - timedelta(days=i)).isoformat() for i in range(a.days)}
    ids = race_ids_by_date(dates)
    session = F.login(email, password, anon)
    OUT.mkdir(parents=True, exist_ok=True)
    for d in sorted(ids):
        path = OUT / f"{d}.json.gz"
        have = json.loads(gzip.open(path, "rt").read()).get("races", {}) if path.exists() else {}
        todo = [r for r in ids[d] if a.refetch or str(r) not in have]
        if not todo:
            print(f"{d}: all {len(ids[d])} races stored"); continue
        if session.get("expires_at", 0) - datetime.now().timestamp() < 600:
            session = F.login(email, password, anon)
        with ThreadPoolExecutor(max_workers=a.workers) as ex:
            results = list(ex.map(lambda rid: (rid, *F.fetch_race(session, rid)), todo))
        races, failed, empty = dict(have), 0, 0
        for rid, page, err in results:
            if not page:
                failed += 1; continue
            p = pack(page)
            if p:
                races[str(rid)] = p
            else:
                empty += 1
        print(f"{d}: fetched {len(todo)} races, {failed} failed, {empty} with no result yet, {len(races)} stored; status {sorted({v['wprStatus'] for v in races.values() if v.get('wprStatus')})}", flush=True)
        text = json.dumps({"date": d, "fetched": datetime.utcnow().isoformat() + "Z", "races": races}, separators=(",", ":"))
        with gzip.GzipFile(path, "wb", mtime=0) as fh:
            fh.write(text.encode())


if __name__ == "__main__":
    main()
