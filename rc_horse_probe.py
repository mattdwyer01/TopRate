"""rc_horse_probe.py -- read-only probe: can racing.com give a horse's past runs by horse code? (14 Oct 2026)

Motivation: Perisher (Rosehill R6, 14 Oct) has a handicap rating and a previous weight on racing.com but no run in our results
files, so the dashboard calls it a first starter. This lists the query fields and Horse type fields that look like form history,
then tries a few likely queries for the given horse codes and prints the SHAPE of what comes back (keys and a short sample).
Writes nothing. Needs RACINGCOM_API_KEY and RACINGCOM_CAL_API_KEY in the environment (never printed).

  python rc_horse_probe.py --code 5404714
"""
import argparse, json

import rc_fields

KEYS = ("horse", "form", "run", "career", "result", "past", "history", "stat")


def show(label, d, n=1500):
    print(f"--- {label}")
    print(json.dumps(d, default=str)[:n])


def type_fields(api, name):
    d = api.q("form", '{ __type(name:"%s"){ fields{ name type{ name kind ofType{ name kind } } } } }' % name)
    return ((d.get("data") or {}).get("__type") or {}).get("fields") or []


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--code", action="append", default=["5404714"])
    a = ap.parse_args()
    api = rc_fields.Api(deadline=300, max_req=80)
    q = type_fields(api, "Query")
    print("root query fields mentioning horse/form/run/result:", [f["name"] for f in q if any(k in f["name"].lower() for k in KEYS)])
    for tn in ("Horse", "RaceEntryItem"):
        fs = type_fields(api, tn)
        print(f"{tn} fields:", [(f["name"], (f["type"].get("name") or (f["type"].get("ofType") or {}).get("name"))) for f in fs])
    for code in dict.fromkeys(a.code):
        for qs in ('{ getHorse(horseCode: "%s") { name age sex } }',
                   '{ getHorseByCode(horseCode: "%s") { name age sex } }',
                   '{ horse(horseCode: "%s") { name age sex } }',
                   '{ getHorseForm(horseCode: "%s") { raceDate } }'):
            show(qs % code, api.q("form", qs % code), 700)


if __name__ == "__main__":
    main()
