"""racing.com results ingest (all states): finishing order, margin to winner, SP, weight, barrier per runner.

Uses the same GraphQL API as the racing-model repo (calendar -> getRacesForMeet -> getRaceForm raceEntries).
Writes data/gps/rc_results_runs_<year>.parquet (one row per runner). Idempotent: rows for a meeting are replaced.
Polite: 1 s between requests, short timeouts, hard request cap and deadline. Never prints keys.

  python rc_results_ingest.py --date 2026-10-11            one local date, all states
  python rc_results_ingest.py --days 2                     the last 2 days ending yesterday
  python rc_results_ingest.py --selftest                   offline parser check
Via tab_probe.yml: script=rc_results_ingest.py, n = days (default 1); needs RACINGCOM_API_KEY / RACINGCOM_CAL_API_KEY.
"""
import argparse, datetime as dt, functools, os, re, sys, time
from pathlib import Path
from zoneinfo import ZoneInfo

import pandas as pd
import requests

print = functools.partial(print, flush=True)
FORM_EP = "https://graphql.rmdprod.racing.com/"
CAL_EP = "https://graphql.api.racing.com/"
UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/140.0 Safari/537.36")
STATES = ["NSW", "VIC", "QLD", "SA", "WA", "TAS", "NT", "ACT"]
TZ = {"NSW": "Australia/Sydney", "VIC": "Australia/Melbourne", "ACT": "Australia/Sydney", "TAS": "Australia/Hobart",
      "QLD": "Australia/Brisbane", "SA": "Australia/Adelaide", "WA": "Australia/Perth", "NT": "Australia/Darwin"}
CAL = """query GetCalendarEvents { getCalendarItems(
  meetTypes: ["Metro","Provincial","Country","Picnic"], eventTypes: ["Racing"],
  states: ["%s"], year: %d, month: %d, hideHiddenEvents: true) {
  race_meet_id name location_name race_meet_type event_start_time state } }"""
RACES = """query{ racesForMeet: getRacesForMeet(meetCode: "%s") {
  raceNumber raceStatus distance name trackCondition isTrial isJumpOut hasSectionals } }"""
FORM = """query{ f: getRaceForm(meetCode: "%s", raceNumber:%d) { Horses: raceEntries {
  finish finishAbv beatenMargin barrierNumber horseName horseCode weight startingPrice scratched } } }"""
WORDS = {"SH": 0.1, "HD": 0.2, "NK": 0.3, "NS": 0.05, "DH": 0.0}   # short head, head, neck, nose, dead heat
OUT = Path("data/gps")
T0 = time.time()


def parse_margin(m):
    """'3.32L' -> 3.32, '0.75L' -> .75, 'SH'/'HD'/'NK'/'NS' -> small fixed values, None -> None."""
    if m is None:
        return None
    s = str(m).strip().upper().replace("LEN", "L")
    r = re.fullmatch(r"([0-9]*\.?[0-9]+)\s*L?", s)
    if r:
        return float(r.group(1))
    return WORDS.get(s)


def parse_money(x):
    r = re.search(r"([0-9]+\.?[0-9]*)", str(x or ""))
    return float(r.group(1)) if r else None


def selftest():
    assert parse_margin("3.32L") == 3.32 and parse_margin("2L") == 2.0 and parse_margin(None) is None
    assert parse_margin("HD") == 0.2 and parse_margin("zzz") is None
    assert parse_money("$21.00") == 21.0 and parse_money("55kg") == 55.0 and parse_money(None) is None
    print("selftest ok")


class Api:
    def __init__(self, max_req, deadline):
        self.n, self.max_req, self.deadline = 0, max_req, deadline
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
                if r.status_code != 200:
                    return {}
                return r.json()
            except Exception:
                time.sleep(3)
        return {}


def meetings_for(api, dates):
    out = []
    months = sorted({(d.year, d.month) for d in dates} | {((d + dt.timedelta(days=1)).year, (d + dt.timedelta(days=1)).month) for d in dates})
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


def fetch_meeting(api, it):
    rows, n_races, n_with = [], 0, 0
    d = api.q("form", RACES % it["race_meet_id"])
    for r in ((d.get("data") or {}).get("racesForMeet")) or []:
        if r.get("isTrial") or r.get("isJumpOut"):
            continue
        n_races += 1
        if str(r.get("raceStatus") or "").lower() not in ("paying", "closed", "results", "resulted", "final"):
            continue
        f = api.q("form", FORM % (it["race_meet_id"], r["raceNumber"]))
        hs = ((((f.get("data") or {}).get("f")) or {}).get("Horses")) or []
        if not any(h.get("finish") for h in hs):
            continue
        n_with += 1
        dist = parse_money(r.get("distance"))
        for h in hs:
            rows.append({"source": "rc_entries", "race_date": it["race_date"], "state": it["state"],
                         "meeting_code": it["race_meet_id"], "venue": it.get("location_name") or it.get("name"),
                         "meet_type": it.get("race_meet_type"), "race_no": r["raceNumber"], "race_distance": dist,
                         "going": r.get("trackCondition"), "horse": h.get("horseName"), "horse_code": h.get("horseCode"),
                         "barrier": h.get("barrierNumber"), "weight_kg": parse_money(h.get("weight")),
                         "sp": parse_money(h.get("startingPrice")), "finish": h.get("finish"),
                         "margin_l": 0.0 if h.get("finish") == 1 else parse_margin(h.get("beatenMargin")),
                         "margin_raw": h.get("beatenMargin"), "scratched": bool(h.get("scratched"))})
    return rows, n_races, n_with


def save(df):
    OUT.mkdir(parents=True, exist_ok=True)
    for yr, g in df.groupby(df.race_date.str[:4]):
        p = OUT / f"rc_results_runs_{yr}.parquet"
        if p.exists():
            old = pd.read_parquet(p)
            old = old[~old.meeting_code.isin(g.meeting_code.unique())]
            g = pd.concat([old, g], ignore_index=True)
        g.to_parquet(p, index=False)
        print("wrote", p, len(g), "rows")
    raw = Path("tab_raw"); raw.mkdir(exist_ok=True)
    df.to_csv(raw / "rc_results_last_run.csv", index=False)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--date"); ap.add_argument("--days", type=int); ap.add_argument("--n", type=int)
    ap.add_argument("--selftest", action="store_true"); ap.add_argument("--max-requests", type=int, default=450)
    ap.add_argument("--deadline", type=int, default=900)
    a = ap.parse_args()
    if a.selftest:
        return selftest()
    if a.date:
        dates = {dt.date.fromisoformat(a.date)}
    else:
        days = a.days or a.n or 1
        y = dt.datetime.now(ZoneInfo("Australia/Melbourne")).date() - dt.timedelta(days=1)
        dates = {y - dt.timedelta(days=i) for i in range(days)}
    print("dates:", sorted(str(d) for d in dates))
    api = Api(a.max_requests, a.deadline)
    ms = meetings_for(api, dates)
    print("meetings:", len(ms), {s: sum(1 for m in ms if m["state"] == s) for s in STATES})
    rows, stat = [], {}
    try:
        for it in ms:
            r, nr, nw = fetch_meeting(api, it)
            rows += r
            s = stat.setdefault(it["state"], [0, 0, 0, 0])
            s[0] += 1; s[1] += nr; s[2] += nw; s[3] += len(r)
            print(f"  {it['state']} {it.get('location_name')}: races {nr}, with results {nw}, runners {len(r)}")
    except TimeoutError as e:
        print("stopped early:", e)
    print("requests:", api.n, "elapsed s:", int(time.time() - T0))
    for st, (m, nr, nw, nrun) in stat.items():
        print(f"{st}: meetings {m}, races {nr}, races with results {nw}, runners {nrun}")
    if rows:
        df = pd.DataFrame(rows)
        bad = df[(df.finish > 1) & df.margin_l.isna()]
        print("non-winners with unparsed margin:", len(bad), "raw samples:", bad.margin_raw.dropna().unique()[:10].tolist())
        if len(bad):
            print("null-margin finish positions:", bad.finish.value_counts().sort_index().head(30).to_dict())
            print("null-margin finishAbv-like samples (finish, scratched, state):",
                  bad.groupby(["state", "scratched"]).size().to_dict())
            print("null-margin share by state:", (bad.groupby("state").size() / df[df.finish > 1].groupby("state").size()).round(2).to_dict())
            print("max finish per race for null-margin rows (sample):",
                  bad.groupby(["meeting_code", "race_no"]).finish.agg(["min", "max", "count"]).head(8).to_dict("index"))
        print("margin_l describe:", df.margin_l.describe().round(2).to_dict())
        save(df)


if __name__ == "__main__":
    main()
