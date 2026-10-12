"""rc_fields.py -- race fields (runners, barriers, weights, riders) for upcoming races from racing.com.

Why: toprate.au answers 403 on every race-detail call since Oct 2026, so toprate_daily.fetch_todays_races() can no longer
build runner rows. racing.com publishes the declared field of every Australian race; this script reads it and writes one
small file per race day, data/rc_fields/<date>.json, that toprate_daily.py turns into runner rows when toprate.au fails.

  python rc_fields.py --date 2026-10-13 [--date ...]     write data/rc_fields/<date>.json
  python rc_fields.py --days-ahead 0 1 2                 Melbourne dates today + N
  python rc_fields.py --probe --date 2026-10-13          print every RaceEntryItem field and a raw sample, write nothing
  python rc_fields.py --selftest

Needs RACINGCOM_API_KEY and RACINGCOM_CAL_API_KEY in the environment (never printed). About 1 request per race at 1 s spacing.
"""
import argparse, datetime as dt, functools, json, os, re, sys, time
from pathlib import Path
from zoneinfo import ZoneInfo

import requests

print = functools.partial(print, flush=True)
FORM_EP = "https://graphql.rmdprod.racing.com/"
CAL_EP = "https://graphql.api.racing.com/"
UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/140.0 Safari/537.36")
STATES = ["NSW", "VIC", "QLD", "SA", "WA", "TAS", "NT", "ACT"]
TZ = {"NSW": "Australia/Sydney", "VIC": "Australia/Melbourne", "ACT": "Australia/Sydney", "TAS": "Australia/Hobart",
      "QLD": "Australia/Brisbane", "SA": "Australia/Adelaide", "WA": "Australia/Perth", "NT": "Australia/Darwin"}
MEL = ZoneInfo("Australia/Melbourne")
OUT = Path("data/rc_fields")
T0 = time.time()

CAL = """query GetCalendarEvents { getCalendarItems(
  meetTypes: ["Metro","Provincial","Country","Picnic"], eventTypes: ["Racing"],
  states: ["%s"], year: %d, month: %d, hideHiddenEvents: true) {
  race_meet_id name location_name race_meet_type event_start_time state } }"""
RACES = """query{ racesForMeet: getRacesForMeet(meetCode: "%s") {
  raceNumber raceStatus distance name time trackCondition trackRating isTrial isJumpOut rdcClass } }"""
# runner fields we want, in order of preference; only the ones RaceEntryItem really has are requested
WANT = ["horseName", "horseCode", "barrierNumber", "weight", "weightCarried", "scratched", "raceEntryNumber", "jockeyName", "jockeyCode",
        "trainerName", "trainerCode", "apprentice", "apprenticeAllowedClaim", "emergency", "emergencyNumber", "isLateScratching",
        "jockeyChanged", "handicapRating", "silkUrl", "startingPrice"]   # scalars only: jockey / trainer / horse are objects and break the query


class Api:
    def __init__(self, deadline=1500, max_req=1500):
        self.n, self.deadline, self.max_req = 0, deadline, max_req
        self.sf = self._s("RACINGCOM_API_KEY", {})
        self.sc = self._s("RACINGCOM_CAL_API_KEY", {"Origin": "https://www.racing.com", "Referer": "https://www.racing.com/"})

    @staticmethod
    def _s(var, extra):
        key = (os.environ.get(var) or "").strip()
        if not key:
            sys.exit(f"{var} not set")
        s = requests.Session()
        s.headers.update({"User-Agent": UA, "Content-Type": "application/json", "X-Api-Key": key,
                          "Referer": "https://dxp-static.racing.com/", **extra})
        return s

    def q(self, which, query):
        if self.n >= self.max_req or time.time() - T0 > self.deadline:
            raise TimeoutError("request cap or deadline reached")
        time.sleep(1.0)
        self.n += 1
        s, ep = (self.sf, FORM_EP) if which == "form" else (self.sc, CAL_EP)
        for attempt in range(3):
            try:
                r = s.get(ep, params={"query": query}, timeout=15)
                if r.status_code == 429:
                    time.sleep(20 * (attempt + 1)); continue
                return r.json() if r.status_code == 200 else {}
            except Exception:
                time.sleep(3)
        return {}


def parse_weight(w):
    m = re.search(r"([0-9]+\.?[0-9]*)", str(w or ""))
    return float(m.group(1)) if m else None


def first(d, *names):
    for n in names:
        v = d.get(n)
        if v not in (None, ""):
            return v
    return None


def meetings(api, dates):
    out = []
    months = sorted({(d.year, d.month) for d in dates})
    for st in STATES:
        for (y, m) in months:
            d = api.q("cal", CAL % (st, y, m))
            for it in ((d.get("data") or {}).get("getCalendarItems")) or []:
                try:
                    utc = dt.datetime.fromisoformat(str(it["event_start_time"]).replace("Z", "+00:00"))
                    local = utc.astimezone(ZoneInfo(TZ.get(it.get("state") or st, "Australia/Sydney"))).date()
                except Exception:
                    continue
                if local in dates:
                    out.append({**it, "state": it.get("state") or st, "race_date": local.isoformat()})
    seen, uniq = set(), []
    for it in out:
        if it["race_meet_id"] not in seen:
            seen.add(it["race_meet_id"]); uniq.append(it)
    return uniq


def entry_fields(api):
    d = api.q("form", '{ __type(name:"RaceEntryItem"){ fields{ name } } }')
    return [f["name"] for f in (((d.get("data") or {}).get("__type") or {}).get("fields") or [])]


def fetch_meeting(api, it, fields):
    form_q = ('query{ f: getRaceForm(meetCode: "%s", raceNumber:%d) { Horses: raceEntries { ' + " ".join(fields) + " } } }")
    d = api.q("form", RACES % it["race_meet_id"])
    races = []
    for r in ((d.get("data") or {}).get("racesForMeet")) or []:
        if r.get("isTrial") or r.get("isJumpOut"):
            continue
        f = api.q("form", form_q % (it["race_meet_id"], r["raceNumber"]))
        hs = (((f.get("data") or {}).get("f")) or {}).get("Horses") or []
        if not hs and f.get("errors") and not getattr(fetch_meeting, "_warned", False):
            fetch_meeting._warned = True
            print("   graphql errors:", json.dumps(f.get("errors"))[:300])
        runners = []
        for h in hs:
            if not h.get("horseName"):
                continue
            runners.append({
                "horse": h.get("horseName"), "horse_code": h.get("horseCode"),
                "barrier": h.get("barrierNumber"), "weight_kg": parse_weight(first(h, "weightCarried", "weight")),
                "tab_number": h.get("raceEntryNumber"), "jockey": h.get("jockeyName"), "trainer": h.get("trainerName"),
                "claim": h.get("apprenticeAllowedClaim"), "silk_url": h.get("silkUrl"), "rating": h.get("handicapRating"),
                "scratched": 1 if (h.get("scratched") or h.get("isLateScratching")) else 0,
                "emergency": h.get("emergencyNumber") or (1 if h.get("emergency") else 0)})
        races.append({"race_no": r["raceNumber"], "distance": r.get("distance"), "name": r.get("name"), "time": r.get("time"),
                      "going": r.get("trackCondition"), "rating": r.get("trackRating"), "class": r.get("rdcClass"),
                      "status": r.get("raceStatus"), "runners": runners})
    return {"meeting_code": it["race_meet_id"], "venue": it.get("location_name") or it.get("name"), "state": it["state"],
            "meet_type": it.get("race_meet_type"), "races": races}


def melbourne_dates(offsets):
    today = dt.datetime.now(MEL).date()
    return {today + dt.timedelta(days=int(o)) for o in offsets}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--date", action="append", default=[])
    ap.add_argument("--days-ahead", nargs="*", default=[])
    ap.add_argument("--probe", action="store_true")
    ap.add_argument("--n"); ap.add_argument("--any-status", action="store_true")   # accepted for tab_probe.yml, unused
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--deadline", type=int, default=1500)
    a = ap.parse_args()
    if a.selftest:
        assert parse_weight("55.5kg") == 55.5 and parse_weight(None) is None
        assert first({"a": None, "b": 3}, "a", "b") == 3
        print("selftest ok"); return
    a.probe = a.probe or bool(os.environ.get("RC_LIST_ONLY"))   # tab_probe.yml show_hidden=list
    dates = {dt.date.fromisoformat(d) for d in a.date} | melbourne_dates(a.days_ahead)
    if not dates:
        sys.exit("no dates")
    api = Api(a.deadline)
    names = entry_fields(api)
    if a.probe:
        print("RaceEntryItem fields (%d):" % len(names), ", ".join(names))
    if a.probe:
        d = api.q("form", '{ __schema { queryType { fields { name args { name } } } } }')
        qf = (((d.get("data") or {}).get("__schema") or {}).get("queryType") or {}).get("fields") or []
        print("Query fields:", "; ".join(f["name"] + "(" + ",".join(x["name"] for x in f.get("args") or []) + ")" for f in qf))
    fields = [w for w in WANT if w in names] or ["horseName", "barrierNumber", "weight", "scratched", "horseCode"]
    print("requesting runner fields:", fields)
    ms = meetings(api, dates)
    print("dates:", sorted(str(d) for d in dates), "meetings:", len(ms))
    OUT.mkdir(parents=True, exist_ok=True)
    by_date = {}
    try:
        for it in ms:
            m = fetch_meeting(api, it, fields)
            nr = sum(len(r["runners"]) for r in m["races"])
            print(f"  {m['state']} {m['venue']}: races {len(m['races'])}, runners {nr}")
            by_date.setdefault(it["race_date"], []).append(m)
            if a.probe and m["races"]:
                for r in m["races"][:1]:
                    print("   sample:", json.dumps({k: v for k, v in r.items() if k != "runners"}), json.dumps(r["runners"][:2]))
                if len(by_date.get(it["race_date"], [])) >= 3:
                    break
    except TimeoutError as e:
        print("stopped early:", e)
    if a.probe:
        return
    now = dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    for d, mm in by_date.items():
        # never replace a day's file with fewer runners (a partial run must not shrink the field)
        path = OUT / f"{d}.json"
        n_new = sum(len(r["runners"]) for m in mm for r in m["races"])
        if path.exists():
            try:
                old = json.loads(path.read_text())
                n_old = sum(len(r["runners"]) for m in old.get("meetings", []) for r in m["races"])
                have = {m["meeting_code"] for m in mm}
                keep = [m for m in old.get("meetings", []) if m["meeting_code"] not in have]
                mm = mm + keep
                n_new = sum(len(r["runners"]) for m in mm for r in m["races"])
                if n_new < n_old:
                    print(f"  {d}: {n_new} runners < existing {n_old}, kept the old file"); continue
            except Exception:
                pass
        path.write_text(json.dumps({"date": d, "generated": now, "meetings": mm}, separators=(",", ":")))
        print(f"wrote {path} ({n_new} runners, {len(mm)} meetings)")
    print("requests:", api.n, "elapsed s:", int(time.time() - T0))


if __name__ == "__main__":
    main()
