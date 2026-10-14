"""rc_price_capture.py -- timestamped win/place prices from every bookmaker racing.com lists, for races about to jump.

Why: the closing price already contains everything our models can see (Oct 2026 analysis), so any further edge has to come from price
behaviour: steam and drift before the jump, and differences between bookmakers. That needs a history of prices with times, which nothing
stored. racing.com lists one odds entry per bookmaker for each runner (`odds { providerCode oddsWin oddsPlace updated }`).

Each run writes ONE snapshot file price_log/rc/<date>/<HHMMSS>.csv.gz for the races that start within the next WINDOW minutes (and for
races that started up to 20 minutes ago, to catch the last price). The workflow pushes the files to the `price-log` branch only, never to
main. Rows: snap_utc, meeting_code, venue, state, race_no, start_utc, tab_no, horse, scratched, provider, win, place, updated.

  python rc_price_capture.py [--window 180] [--deadline 240] [--date 2026-10-14]
  python rc_price_capture.py --selftest

Needs RACINGCOM_API_KEY and RACINGCOM_CAL_API_KEY (never printed). About 50 requests per run at 1 s spacing (8 calendar + one per meeting
+ one per race in the window).
"""
import argparse, csv, datetime as dt, gzip, json, os, re, sys
from pathlib import Path

import rc_fields as rf

OUT = Path("price_log/rc")
FINAL = {"paying", "closed", "results", "resulted", "final", "abandoned"}
ENTRY_Q = ('query{ f: getRaceForm(meetCode: "%s", raceNumber:%d) { Horses: formRaceEntries { horseName raceEntryNumber scratched '
           + rf.ODDS_SEL + ' } } }')
FIELDS = ["snap_utc", "meeting_code", "venue", "state", "race_no", "start_utc", "tab_no", "horse", "scratched", "provider", "win", "place", "updated"]


def money(v):
    m = re.search(r"([0-9]+\.?[0-9]*)", str(v if v is not None else ""))
    return float(m.group(1)) if m else None


def parse_start(s):
    try:
        return dt.datetime.fromisoformat(str(s).replace("Z", "+00:00"))
    except Exception:
        return None


def entry_rows(snap, meeting, race, horses):
    rows = []
    for h in horses or []:
        for o in h.get("odds") or []:
            win, place = money((o or {}).get("oddsWin")), money((o or {}).get("oddsPlace"))
            if win is None and place is None:
                continue
            rows.append({"snap_utc": snap, "meeting_code": meeting["meeting_code"], "venue": meeting["venue"], "state": meeting["state"],
                         "race_no": race["race_no"], "start_utc": race["start_utc"], "tab_no": h.get("raceEntryNumber"),
                         "horse": h.get("horseName"), "scratched": 1 if h.get("scratched") else 0,
                         "provider": (o or {}).get("providerCode"), "win": win, "place": place, "updated": (o or {}).get("updated")})
    return rows


def due_races(races, now, window_min):
    """Races that start within window_min minutes, or started up to 20 minutes ago, and are not final."""
    out = []
    for r in races:
        if r.get("isTrial") or r.get("isJumpOut") or str(r.get("raceStatus") or "").lower() in FINAL:
            continue
        st = parse_start(r.get("time"))
        if st is None:
            continue
        mins = (st - now).total_seconds() / 60
        if -20 <= mins <= window_min:
            out.append({"race_no": r["raceNumber"], "start_utc": st.strftime("%Y-%m-%dT%H:%M:%SZ")})
    return out


def selftest():
    assert money("$5.50") == 5.5 and money(None) is None and money("SP") is None
    now = dt.datetime(2026, 10, 14, 3, 0, tzinfo=dt.timezone.utc)
    races = [{"raceNumber": 1, "time": "2026-10-14T03:30:00.000Z", "raceStatus": "Open"},
             {"raceNumber": 2, "time": "2026-10-14T08:30:00.000Z", "raceStatus": "Open"},
             {"raceNumber": 3, "time": "2026-10-14T02:50:00.000Z", "raceStatus": "Paying"},
             {"raceNumber": 4, "time": "2026-10-14T02:55:00.000Z", "raceStatus": "Closed"},
             {"raceNumber": 5, "time": "2026-10-14T03:05:00.000Z", "raceStatus": "Open", "isTrial": True},
             {"raceNumber": 6, "time": "2026-10-14T02:45:00.000Z", "raceStatus": "Open"},
             {"raceNumber": 7, "time": "2026-10-14T02:30:00.000Z", "raceStatus": "Open"}]
    d = due_races(races, now, 180)
    assert [x["race_no"] for x in d] == [1, 6], d
    rows = entry_rows("S", {"meeting_code": "1", "venue": "V", "state": "NSW"}, d[0],
                      [{"horseName": "A", "raceEntryNumber": 1, "scratched": False,
                        "odds": [{"providerCode": "TAB", "oddsWin": "$3.50", "oddsPlace": "$1.50", "updated": 5}, {"providerCode": "X", "oddsWin": None, "oddsPlace": None}]}])
    assert len(rows) == 1 and rows[0]["win"] == 3.5 and rows[0]["place"] == 1.5 and rows[0]["provider"] == "TAB"
    print("selftest ok")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--window", type=int, default=180)
    ap.add_argument("--deadline", type=int, default=240)
    ap.add_argument("--date", default=None, help="Melbourne date to read (default today); the calendar covers every state")
    ap.add_argument("--selftest", action="store_true")
    a = ap.parse_args()
    if a.selftest:
        return selftest()
    now = dt.datetime.now(dt.timezone.utc)
    snap = now.strftime("%Y-%m-%dT%H:%M:%SZ")
    dates = {dt.date.fromisoformat(a.date)} if a.date else {now.astimezone(rf.MEL).date()}
    # a race that jumps just after midnight Melbourne time but is still "yesterday" in WA is covered by also reading the previous date at night
    dates |= {d - dt.timedelta(days=1) for d in dates if now.astimezone(rf.MEL).hour < 6}
    api = rf.Api(a.deadline, 250)
    rows, n_req_races = [], 0
    try:
        for it in rf.meetings(api, dates):
            d = api.q("form", rf.RACES % it["race_meet_id"])
            raw = ((d.get("data") or {}).get("racesForMeet")) or []
            meeting = {"meeting_code": it["race_meet_id"], "venue": it.get("location_name") or it.get("name"), "state": it["state"]}
            for race in due_races(raw, now, a.window):
                f = api.q("form", ENTRY_Q % (it["race_meet_id"], race["race_no"]))
                hs = (((f.get("data") or {}).get("f")) or {}).get("Horses") or []
                rows += entry_rows(snap, meeting, race, hs); n_req_races += 1
    except TimeoutError as e:
        print("stopped early:", e)
    print(f"{snap}: {n_req_races} races, {len(rows)} price rows, {len({r['provider'] for r in rows})} providers, {api.n} requests")
    if not rows:
        return
    folder = OUT / now.astimezone(rf.MEL).strftime("%Y-%m-%d")
    folder.mkdir(parents=True, exist_ok=True)
    path = folder / (now.strftime("%H%M%S") + ".csv.gz")
    with gzip.open(path, "wt", newline="") as f:
        w = csv.DictWriter(f, fieldnames=FIELDS); w.writeheader(); w.writerows(rows)
    print("wrote", path)


if __name__ == "__main__":
    main()
