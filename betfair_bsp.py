"""Betfair starting price (BSP) history for Australian racing.

Betfair publishes one CSV per day and market type at
  https://promo.betfair.com/betfairsp/prices/dwbfpricesauswin<DDMMYYYY>.csv   (win)
  https://promo.betfair.com/betfairsp/prices/dwbfpricesausplace<DDMMYYYY>.csv (place)
Columns (as published): EVENT_ID, MENU_HINT, EVENT_NAME, EVENT_DT, SELECTION_ID, SELECTION_NAME, WIN_LOSE, BSP,
PPWAP, MORNINGWAP, PPMAX, PPMIN, IPMAX, IPMIN, MORNINGTRADEDVOL, PPTRADEDVOL, IPTRADEDVOL.

The site answers 403 to non-Australian addresses (cloud sessions, GitHub-hosted runners), so this runs on the AU
runner (workflow betfair_bsp.yml). Standard library only. Rows are kept as published, with the file date appended,
in data/betfair_bsp/<kind>_<YYYY-MM>.csv.gz; data/betfair_bsp/index.json records the dates done (rows per date, 0 for a
date with no file) so a run only fetches what is missing. A run stops fetching after --budget seconds (the runner
is shared with the live results poller) and can simply be run again.

  python betfair_bsp.py download --since 2025-01-01 --until 2026-11-09 --kinds win
"""
import argparse
import concurrent.futures as cf
import datetime as dt
import gzip
import json
import os
import sys
import time
import urllib.error
import urllib.request

BASE = "https://promo.betfair.com/betfairsp/prices/dwbfpricesaus{kind}{d}.csv"
OUT = os.path.join("data", "betfair_bsp")
INDEX = os.path.join(OUT, "index.json")
UA = "Mozilla/5.0 (compatible; personal-research-downloader; python-urllib)"
FRESH_DAYS = 3          # a missing file this recent is tried again next run


def fetch(kind, day):
    url = BASE.format(kind=kind, d=day.strftime("%d%m%Y"))
    req = urllib.request.Request(url, headers={"User-Agent": UA})
    try:
        with urllib.request.urlopen(req, timeout=40) as r:
            body = r.read().decode("utf-8", "replace")
        return kind, day, 200, body
    except urllib.error.HTTPError as e:
        return kind, day, e.code, ""
    except Exception as e:            # timeouts, resets
        return kind, day, -1, str(e)


def load_index():
    if os.path.exists(INDEX):
        with open(INDEX) as f:
            return json.load(f)
    return {}


def append_month(kind, month, header, lines):
    path = os.path.join(OUT, "%s_%s.csv.gz" % (kind, month))
    new = not os.path.exists(path)
    with gzip.open(path, "at", encoding="utf-8", newline="") as f:
        if new:
            f.write(header + ",FILE_DATE\n")
        f.write("".join(lines))


def download(since, until, kinds, budget, workers):
    os.makedirs(OUT, exist_ok=True)
    idx = load_index()
    today = dt.date.today()
    jobs = []
    d = since
    while d <= until:
        for k in kinds:
            if "%s:%s" % (k, d.isoformat()) not in idx:
                jobs.append((k, d))
        d += dt.timedelta(days=1)
    print("to fetch: %d files" % len(jobs))
    if not jobs:
        return 0

    # one request first: stop at once if the site refuses us
    k0, d0, code, body = fetch(*jobs[0])
    print("first file %s %s -> %s, %d bytes" % (k0, d0, code, len(body)))
    if code == 403:
        print("403 from Betfair (not an Australian address, or blocked). Nothing fetched.")
        return 2
    if code == 200:
        print("header: " + body.split("\n", 1)[0][:300])

    t0 = time.time()
    results = [(k0, d0, code, body)]
    rest = jobs[1:]
    with cf.ThreadPoolExecutor(max_workers=workers) as ex:
        for i in range(0, len(rest), workers * 4):          # small batches so the time budget is honoured
            if time.time() - t0 > budget:
                print("time budget reached, run again for the rest")
                break
            results.extend(ex.map(lambda j: fetch(*j), rest[i:i + workers * 4]))

    ok = missing = failed = rows = 0
    by_month = {}
    for kind, day, code, body in sorted(results, key=lambda r: (r[0], r[1])):
        key = "%s:%s" % (kind, day.isoformat())
        if code == 200 and body.lstrip().upper().startswith("EVENT_ID"):
            lines = [ln for ln in body.replace("\r\n", "\n").split("\n") if ln.strip()]
            header, data = lines[0].strip(), lines[1:]
            by_month.setdefault((kind, day.strftime("%Y-%m")), (header, []))[1].extend(
                ln + "," + day.isoformat() + "\n" for ln in data)
            idx[key] = len(data)
            ok += 1
            rows += len(data)
        elif code == 404 or (code == 200 and not body.strip()):
            missing += 1
            if (today - day).days > FRESH_DAYS:
                idx[key] = 0
        else:
            failed += 1
            if failed <= 5:
                print("failed %s %s: %s %s" % (kind, day, code, body[:120].replace("\n", " ")))
    for (kind, month), (header, lines) in sorted(by_month.items()):
        append_month(kind, month, header, lines)
    with open(INDEX, "w") as f:
        json.dump(idx, f, sort_keys=True)
    left = len(jobs) - ok - missing - failed
    print("fetched %d files (%d rows), %d dates with no file, %d failed, %d not attempted, %.0fs"
          % (ok, rows, missing, failed, left, time.time() - t0))
    return 0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", choices=["download"])
    ap.add_argument("--since", required=True)
    ap.add_argument("--until", default="")
    ap.add_argument("--kinds", default="win")
    ap.add_argument("--budget", type=int, default=240)
    ap.add_argument("--workers", type=int, default=6)
    a = ap.parse_args()
    since = dt.date.fromisoformat(a.since)
    until = dt.date.fromisoformat(a.until) if a.until else dt.date.today() - dt.timedelta(days=1)
    sys.exit(download(since, until, a.kinds.split(","), a.budget, a.workers))


if __name__ == "__main__":
    main()
