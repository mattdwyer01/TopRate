"""Live latency probe for Racing Queensland GPS: when does a meeting's ZIP appear on the site, and does it grow race by race?
Polls the RQ sectionals listing and the meeting ZIP (default: today's meeting at the venue) and logs, with UTC times: first seen in the listing, ZIP size,
number of race files inside and their stamped times. Needs no secrets. Usage:
  python research/rq_gps_live_probe.py --date 2026-10-22 --venue Ipswich --until 10:00 --every 180"""
import argparse, io, json, re, sys, time, zipfile
from datetime import datetime, timezone
import requests

BASE = "https://www.racingqueensland.com.au"
LISTING = BASE + "/industry/thoroughbred/thoroughbred-sectionals"
UA = {"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/140.0 Safari/537.36"}
ap = argparse.ArgumentParser()
ap.add_argument("--date", required=True)
ap.add_argument("--venue", required=True)
ap.add_argument("--until", default="10:00", help="stop at this UTC HH:MM (the next day if earlier than the start)")
ap.add_argument("--every", type=int, default=180)
ap.add_argument("--out", default="rq_gps_live_probe.json")
a = ap.parse_args()
tag = a.date.replace("-", "") + "_" + a.venue.strip().replace(" ", "_")
rx = re.compile(r"RacingFile\.ashx\?path=(/Sectional/" + re.escape(tag) + r"[^\"'<>&]*\.zip)", re.I)
s = requests.Session(); s.headers.update(UA)
h, m = map(int, a.until.split(":"))
now = lambda: datetime.now(timezone.utc)
stop = now().replace(hour=h, minute=m, second=0, microsecond=0)
if stop <= now():
    stop = stop.replace(day=stop.day) + __import__("datetime").timedelta(days=1)
events, last, path = [], None, None


def log(what, detail=""):
    events.append({"t": now().strftime("%Y-%m-%dT%H:%M:%SZ"), "what": what, "detail": detail})
    print(events[-1]["t"], what, detail, flush=True)


while now() < stop:
    try:
        if path is None:
            html = s.get(LISTING, timeout=60).text
            hit = rx.search(html)
            if hit:
                path = hit.group(1); log("listed", path)
        if path:
            r = s.get(BASE + "/RacingFile.ashx?path=" + path, timeout=60)
            if r.status_code == 200:
                z = zipfile.ZipFile(io.BytesIO(r.content))
                stamps = sorted((i.filename.split("_")[-1][:3], "%02d:%02d:%02d" % i.date_time[3:6]) for i in z.infolist())
                key = (len(r.content), tuple(stamps))
                if key != last:
                    last = key; log("zip", f"{len(r.content)} bytes, {len(stamps)} race files: " + ", ".join(f"{n}@{t}" for n, t in stamps))
            else:
                log("zip_status", str(r.status_code))
    except Exception as e:
        log("error", str(e)[:120])
    json.dump({"venue": a.venue, "date": a.date, "events": events}, open(a.out, "w"), indent=1)
    time.sleep(a.every)
log("done", f"{len(events)} events")
json.dump({"venue": a.venue, "date": a.date, "events": events}, open(a.out, "w"), indent=1)
