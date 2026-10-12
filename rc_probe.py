"""Read-only probe: does racing.com's API return results/margins for non-VIC/SA/QLD meetings?

Uses the same GraphQL queries as the racing-model repo's ingest/racingcom_sectionals.py.
Few requests (about 30), 1 s apart. Never prints keys. Run via tab_probe.yml (script=rc_probe.py).
"""
import json, os, sys, time
import requests

FORM_EP = "https://graphql.rmdprod.racing.com/"
CAL_EP = "https://graphql.api.racing.com/"
UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/140.0 Safari/537.36")
CAL = """query GetCalendarEvents { getCalendarItems(
  meetTypes: ["Metro","Provincial","Country","Picnic"], eventTypes: ["Racing"],
  states: [%s], year: %d, month: %d, hideHiddenEvents: true) {
  race_meet_id name location_name race_meet_type event_start_time state } }"""
RACES = """query{ racesForMeet: getRacesForMeet(meetCode: "%s") {
  id raceNumber raceStatus distance time name trackCondition trackRating isTrial isJumpOut
  hasSectionals rdcClass meet { venue } } }"""
FORM = """query{ f: getRaceForm(meetCode: "%s", raceNumber:%d) {
  Horses: raceEntryTimes { FinalPosition: finishPosition FullName: horseName SaddleNumber: saddleNumber
    RaceTime: finishTime BeatenMargin: beatenMargin SplitTimes: splitTimes { Distance: distance Time: time } }
  RaceTime: raceTime Source: timingSource IsComplete: isTimingComplete IsCompleteData: isCompleteData } }"""


def client(var, ep, extra):
    key = (os.environ.get(var) or "").strip()
    if not key:
        print(f"{var} not set"); return None
    s = requests.Session()
    s.headers.update({"User-Agent": UA, "Content-Type": "application/json",
                      "Referer": "https://dxp-static.racing.com/", "X-Api-Key": key, **extra})
    return s


def q(s, ep, query):
    time.sleep(1.0)
    try:
        r = s.get(ep, params={"query": query}, timeout=30)
        if r.status_code != 200:
            return {"_http": r.status_code, "_body": r.text[:200]}
        return r.json()
    except Exception as e:
        return {"_err": str(e)[:200]}


def main():
    cal = client("RACINGCOM_CAL_API_KEY", CAL_EP, {"Origin": "https://www.racing.com", "Referer": "https://www.racing.com/"})
    frm = client("RACINGCOM_API_KEY", FORM_EP, {})
    if not cal or not frm:
        return
    meets = {}
    for st in ["NSW", "WA", "TAS", "NT", "ACT", "VIC"]:
        for (y, m) in [(2026, 9)]:
            d = q(cal, CAL_EP, CAL % (f'"{st}"', y, m))
            items = ((d.get("data") or {}).get("getCalendarItems")) or []
            print(st, y, m, "items:", len(items), "" if items else str(d)[:200])
            meets[st] = items
    for st in ["NSW", "WA", "TAS", "NT", "ACT", "VIC"]:
        items = [i for i in meets.get(st, []) if str(i.get("event_start_time", "")) < "2026-10-05"]
        items = sorted(items, key=lambda i: i.get("event_start_time", ""))[-2:]
        for it in items:
            code = it["race_meet_id"]
            print("\n==", st, it.get("name"), it.get("location_name"), it.get("race_meet_type"), it.get("event_start_time"))
            d = q(frm, FORM_EP, RACES % code)
            races = ((d.get("data") or {}).get("racesForMeet")) or []
            print(" races:", len(races), "" if races else str(d)[:200])
            for r in races[:1]:
                print(" race1:", {k: r.get(k) for k in ("raceNumber", "raceStatus", "distance", "hasSectionals", "trackCondition")})
                f = q(frm, FORM_EP, FORM % (code, r["raceNumber"]))
                fo = ((f.get("data") or {}).get("f")) or {}
                hs = fo.get("Horses") or []
                print(" runners:", len(hs), "RaceTime:", fo.get("RaceTime"), "src:", fo.get("Source"),
                      "complete:", fo.get("IsComplete"), fo.get("IsCompleteData"))
                for h in hs[:4]:
                    print("   ", json.dumps({k: h.get(k) for k in ("FinalPosition", "FullName", "RaceTime", "BeatenMargin")}),
                          "splits:", len(h.get("SplitTimes") or []))
                if not hs:
                    print(" raw:", str(f)[:300])


if __name__ == "__main__":
    main()
