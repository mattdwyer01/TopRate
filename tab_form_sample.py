"""
tab_form_sample.py -- read-only sample of TAB's per-runner past form (runners[]._links.form) across every AU state.

Why (Oct 2026): the form link (.../races/N/form/RUNNER_NUMBER?jurisdiction=XX) returns each runner's age, sex and
previousStarts[] with finishing position, margin, time, position in running, starters, winner/second, weight carried and
track condition. That could replace toprate.au as the source of margins and times for ALL states (GPS data covers only
VIC, SA and QLD). This takes a few races per state, fetches the form for each runner and prints one compact row per
previous start, so the values can be checked against TopRate's own results (margins, times, weights).

Use the link EXACTLY as TAB gives it: it already carries ?jurisdiction=XX, and our poller.get() would append a second
one (that duplicate produced HTTP 503 in the first probe).

Run on the AU self-hosted runner via tab_probe.yml (script=tab_form_sample.py). Read-only; writes only to tab_raw/.
Output lines starting FORMROW| are tab separated: state, venue, race, runner, age, sex, start_date, venue_abbr,
race_no, distance, finish, margin, time, position_in_run, starters, winner_or_second, handicap, track, class, steward.
"""
import argparse
import json
import sys
import time
from datetime import date
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import tab_results_poller as poller

OUT = Path(__file__).parent / "tab_raw"


def fetch_form(url, tries=3):
    for i in range(tries):
        try:
            r = poller._cr.get(url, impersonate="chrome", timeout=20, headers={"Accept": "application/json"})
            if r.status_code == 200:
                return r.json()
            print(f"  form HTTP {r.status_code} (try {i + 1}) {url[-70:]}")
        except Exception as e:
            print(f"  form error {type(e).__name__} (try {i + 1}) {url[-70:]}")
        time.sleep(2)
    return None


def clean(v):
    return "" if v is None else str(v).replace("\t", " ").replace("\n", " ")[:60]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--date", default=str(date.today()))
    ap.add_argument("--races", type=int, default=2, help="races per state")
    ap.add_argument("--runners", type=int, default=8, help="runners per race")
    args = ap.parse_args()
    if poller._cr is None:
        print("curl_cffi not installed; cannot run")
        return
    OUT.mkdir(exist_ok=True)
    seen_states, n_req, key_report = set(), 0, False
    for jur in poller.TAB_JURISDICTIONS:
        try:
            payload = poller.get(poller.MEETINGS.format(date=args.date), {"jurisdiction": jur}, timeout=20)
        except Exception as e:
            print(f"{jur} meetings failed: {type(e).__name__}")
            continue
        for m in payload.get("meetings", []):
            state = m.get("location")
            if m.get("raceType") != poller.RACE_TYPE or state not in poller.AU_STATES or state in seen_states \
                    or not m.get("venueMnemonic"):
                continue
            seen_states.add(state)
            venue = m.get("meetingName")
            races = [rc for rc in m.get("races", []) if rc.get("raceNumber")]
            races = races[len(races) // 2: len(races) // 2 + args.races]       # mid-card races
            for rc in races:
                rno = rc["raceNumber"]
                det = poller.get(poller.RACE_DETAIL.format(date=args.date, venue_mnemonic=m["venueMnemonic"], race_no=rno),
                                 {"jurisdiction": jur}, timeout=20)
                n_run = 0
                for run in det.get("runners", []):
                    link = (run.get("_links") or {}).get("form")
                    if not link or (run.get("fixedOdds") or {}).get("bettingStatus") in ("Scratched", "LateScratched"):
                        continue
                    frm = fetch_form(link)
                    n_req += 1
                    time.sleep(0.15)
                    if frm is None:
                        continue
                    if not key_report:
                        key_report = True
                        ps = (frm.get("runnerStarts") or {}).get("previousStarts") or []
                        print("PREVIOUS START KEYS: " + ", ".join(sorted(ps[0].keys())) if ps else "no previous starts")
                        print("RUNNER KEYS: " + ", ".join(sorted(k for k in frm.keys() if not isinstance(frm[k], (dict, list)))))
                    (OUT / f"form_{state}_{venue}_R{rno}_{run.get('runnerNumber')}.json".replace(" ", "-")).write_text(
                        json.dumps(frm, default=str))
                    starts = (frm.get("runnerStarts") or {}).get("previousStarts") or []
                    print(f"RUNNER|{state}|{venue}|R{rno}|{run.get('runnerName')}|age={frm.get('age')}|sex={frm.get('sex')}|"
                          f"prev_starts={len(starts)}|fieldStrength={frm.get('fieldStrength')}|last20={frm.get('last20Starts')}")
                    for s in starts:
                        print("FORMROW|" + "\t".join(clean(x) for x in (
                            state, venue, rno, run.get("runnerName"), frm.get("age"), frm.get("sex"), s.get("startDate"),
                            s.get("venueAbbreviation"), s.get("raceNumber"), s.get("distance"), s.get("finishingPosition"),
                            s.get("margin"), s.get("time"), s.get("positionInRun"), s.get("numberOfStarters"),
                            s.get("winnerOrSecond"), s.get("handicap"), s.get("trackCondition"), s.get("class"),
                            s.get("stewardsComment"))))
                    n_run += 1
                    if n_run >= args.runners:
                        break
            print(f"-- {state} {venue}: {len(races)} races sampled")
    print(f"\nstates sampled: {sorted(seen_states)}; form requests: {n_req}")


if __name__ == "__main__":
    main()
