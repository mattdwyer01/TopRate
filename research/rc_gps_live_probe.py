"""Live latency probe for racing.com GPS: how long after a race does it appear?

Polls one meeting through the day and logs, per race, the UTC time each state is first seen:
raceStatus change, hasSectionals true, getRaceForm with split times / distance run / ground lost.
Run from the manual workflow rc_gps_live_probe.yml (needs RACINGCOM_API_KEY and RACINGCOM_CAL_API_KEY).
Usage: python research/rc_gps_live_probe.py --rm ../rm --venue Mornington --date 2026-10-22 --until 09:30
"""
import argparse
import json
import sys
import time
from datetime import datetime, timezone

ap = argparse.ArgumentParser()
ap.add_argument("--rm", required=True, help="path to the racing-model checkout")
ap.add_argument("--venue", default="Mornington")
ap.add_argument("--date", required=True, help="Melbourne meeting date YYYY-MM-DD")
ap.add_argument("--until", default="09:30", help="stop at this UTC HH:MM")
ap.add_argument("--every", type=int, default=60, help="seconds between polls")
ap.add_argument("--out", default="rc_gps_live_probe.json")
a = ap.parse_args()

sys.path.insert(0, a.rm)
from ingest import racingcom_sectionals as rc  # noqa: E402

CAL = "https://graphql.api.racing.com/"
cal = rc.Client(delay=0.3, endpoint=CAL, key_var="RACINGCOM_CAL_API_KEY")
form = rc.Client(delay=0.3)
idx = rc.CalendarIndex(cal, ["VIC", "SA"])
code = idx.lookup(a.date, [a.venue])
if not code:
    sys.exit(f"no racing.com meeting code for {a.venue} on {a.date}")


def now():
    return datetime.now(timezone.utc).strftime("%H:%M:%S")


print(f"{now()}Z meeting code {code}", flush=True)
events = []   # {race, t, what, detail}
seen = {}     # (race, what) -> True
state = {}


def mark(race, what, detail=""):
    if (race, what) in seen:
        return
    seen[(race, what)] = True
    events.append({"race": race, "t": now(), "what": what, "detail": detail})
    print(f"{now()}Z R{race} {what} {detail}", flush=True)


def save():
    with open(a.out, "w") as f:
        json.dump({"venue": a.venue, "date": a.date, "code": code, "events": events}, f, indent=1)


h, m = map(int, a.until.split(":"))
while True:
    t = datetime.now(timezone.utc)
    if (t.hour, t.minute) >= (h, m):
        break
    try:
        d = form.q(rc.RACES_FOR_MEET % code)
        races = ((d.get("data") or {}).get("racesForMeet")) or []
    except Exception as e:
        print(f"{now()}Z meet query failed: {e}", flush=True)
        time.sleep(a.every)
        continue
    for r in races:
        n = r.get("raceNumber")
        if r.get("isTrial") or r.get("isJumpOut") or n is None:
            continue
        mark(n, "jump_time_listed", str(r.get("time")))
        st = r.get("raceStatus")
        if state.get(n) != st:
            state[n] = st
            events.append({"race": n, "t": now(), "what": "status", "detail": str(st)})
            print(f"{now()}Z R{n} status {st}", flush=True)
        if r.get("hasSectionals"):
            mark(n, "hasSectionals_true")
        # form is only worth fetching once the race has a result
        if str(st).lower() in ("final", "paying", "closed", "resulted", "protest", "provisional") or r.get("hasSectionals"):
            try:
                f = form.q(rc.RACE_FORM % (code, n))
                fm = ((f.get("data") or {}).get("f")) or {}
            except Exception as e:
                print(f"{now()}Z R{n} form query failed: {e}", flush=True)
                continue
            hs = fm.get("Horses") or []
            if hs:
                mark(n, "form_rows", f"{len(hs)} horses")
            with_splits = [x for x in hs if x.get("SplitTimes")]
            with_dist = [x for x in hs if x.get("DistanceRun")]
            with_lost = [x for x in hs if x.get("DistanceVarToWinner") is not None]
            if with_dist:
                mark(n, "distance_run", f"{len(with_dist)}/{len(hs)}")
            if with_lost:
                mark(n, "ground_lost", f"{len(with_lost)}/{len(hs)}")
            if with_splits:
                mark(n, "split_times", f"{len(with_splits)}/{len(hs)} source={fm.get('Source')} complete={fm.get('IsComplete')}")
    save()
    time.sleep(a.every)
save()
print(f"{now()}Z done, {len(events)} events", flush=True)
