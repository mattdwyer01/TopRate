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


CANDIDATES = ("getHorseProfile", "GetHorseFormAll", "GetHorseFormTop10", "GetRaceEntryItemByHorsePaged", "raceDetailsForHorse",
              "GetHorseRaceStats", "GetRaceEntryTimesByHorseCode")


def unwrap(t):
    while t and not t.get("name") and t.get("ofType"):
        t = t["ofType"]
    return t or {}


def deep(api, code):
    """Argument lists of the candidate query fields, then one call each with horseCode filled in and scalar sub-fields chosen."""
    TREF = "name kind ofType{name kind ofType{name kind ofType{name kind}}}"
    d = api.q("form", '{ __type(name:"Query"){ fields{ name args{ name type{ %s } } type{ %s } } } }' % (TREF, TREF))
    fields = {f["name"]: f for f in (((d.get("data") or {}).get("__type") or {}).get("fields") or [])}
    for name in CANDIDATES:
        f = fields.get(name)
        if not f:
            print(f"== {name}: not found"); continue
        args = f.get("args") or []
        print(f"== {name} args:", [(x["name"], (unwrap(x["type"]).get("name")), x["type"].get("kind")) for x in args], "returns", unwrap(f["type"]).get("name"))
        rt = unwrap(f["type"]).get("name")
        sub = type_fields(api, rt) if rt else []
        scal_all = [x["name"] for x in sub if unwrap(x["type"]).get("name") in ("String", "Int", "Float", "Boolean", "ID", "AWSDate", "AWSDateTime")]
        scal = scal_all
        PRI = ("name", "namePrev", "fullName", "age", "sex", "lastRaceDate", "careerStats", "lastStartsSummary", "lastFive", "lastTen", "raceDate",
               "venueName", "raceNumber", "raceDistance", "finish", "position", "weightCarried", "beatenMargin", "startingPrice", "trackCondition", "isTrial", "horseName")
        scal = [n for n in PRI if n in scal_all] + [n for n in scal_all if n not in PRI][:12]
        print("   scalar fields:", scal)
        use = []
        for x in args:
            n = x["name"]
            if "horsecode" in n.lower() or n.lower() in ("code", "horse", "horseid"):
                use.append('%s: "%s"' % (n, code))
            elif n.lower() in ("first", "limit", "pagesize", "count", "take"):
                use.append("%s: 10" % n)
            elif x["type"].get("kind") == "NON_NULL":
                print(f"   required arg {n} not filled, skipping"); use = None; break
        if use is None or not scal:
            continue
        q = "{ %s(%s) { %s } }" % (name, ", ".join(use), " ".join(scal))
        show("call " + q[:200], api.q("form", q), 2500)


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
        deep(api, code)
        return
        for qs in ('{ getHorse(horseCode: "%s") { name age sex } }',
                   '{ getHorseByCode(horseCode: "%s") { name age sex } }',
                   '{ horse(horseCode: "%s") { name age sex } }',
                   '{ getHorseForm(horseCode: "%s") { raceDate } }'):
            show(qs % code, api.q("form", qs % code), 700)


if __name__ == "__main__":
    main()
