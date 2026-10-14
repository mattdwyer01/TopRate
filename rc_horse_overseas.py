"""rc_horse_overseas.py -- past runs of horses we hold no results for (imports and first-time Australian starters), from racing.com.

Why: a horse such as Perisher (Rosehill R6, 14 Oct 2026) has raced six times in Ireland and Britain, but our results files only
cover Australian races, so the runner gets a placeholder horse_id (own_ratings/fill_runner_ids.py: HORSE_BASE + racing.com horse
code) and the dashboard called it a first starter with "0 rated runs". racing.com's GetHorseFormAll(horseCode) returns every run,
overseas ones included, with finish, beaten margin, weight, starting price and track condition. They have NO rating from us, so they
are shown in the Recent runs table as unrated runs and never feed the projection.

Reads runners.csv rows from yesterday on whose horse_id is a placeholder, fetches each horse once, and merges the result into
overseas_runs.json ({horse name lower-case: [run, ...]}, newest first). Needs RACINGCOM_API_KEY and RACINGCOM_CAL_API_KEY (never printed).

  python rc_horse_overseas.py            update overseas_runs.json
  python rc_horse_overseas.py --dry-run  print what would be fetched, write nothing
  python rc_horse_overseas.py --selftest
"""
import argparse, datetime as dt, json, re, sys
from pathlib import Path

import pandas as pd

import rc_fields

HORSE_BASE = 9_000_000_000      # own_ratings/build_results_ext.py HORSE_BASE (not imported: that module pulls in the ratings chain)
OUT = Path("overseas_runs.json")
FIELDS = ("raceDate venueName raceDistance finish weightCarried beatenMargin startingPrice trackCondition isTrial "
          "jockeyName rdcClass barrierNumber horseName")


def num(s, pat):
    m = re.search(pat, str(s or ""))
    return float(m.group(1)) if m else None


def to_run(e: dict):
    d = str(e.get("raceDate") or "")[:10]
    if not re.match(r"\d{4}-\d{2}-\d{2}$", d):
        return None
    dist = num(e.get("raceDistance"), r"(\d+)")
    return {
        "d": d, "trk": str(e.get("venueName") or "").strip(), "dist": int(dist) if dist else None,
        "go": str(e.get("trackCondition") or "").strip(),
        "fin": e.get("finish") if isinstance(e.get("finish"), int) and e.get("finish") > 0 else None,
        "wt": num(e.get("weightCarried"), r"([0-9]+\.?[0-9]*)"), "sp": num(e.get("startingPrice"), r"([0-9]+\.?[0-9]*)"),
        "mgn": num(e.get("beatenMargin"), r"([0-9]+\.?[0-9]*)"),
        "jck": str(e.get("jockeyName") or "").strip(), "cls": str(e.get("rdcClass") or "").strip(),
        "bar": e.get("barrierNumber") if isinstance(e.get("barrierNumber"), int) else None,
        "tr": 1 if e.get("isTrial") else 0, "os": 1,
    }


def horses_needed(path="runners.csv", since=None):
    r = pd.read_csv(path, usecols=["date", "horse", "horse_id"], low_memory=False)
    r["hid"] = pd.to_numeric(r.horse_id, errors="coerce")
    r = r[(r.date.astype(str).str[:10] >= since) & (r.hid >= HORSE_BASE)]
    return {str(h).strip(): int(i - HORSE_BASE) for h, i in zip(r.horse, r.hid)}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument("--selftest", action="store_true")
    a = ap.parse_args()
    if a.selftest:
        run = to_run({"raceDate": "2025-08-02", "venueName": "Galway", "raceDistance": "1609m", "finish": 2, "weightCarried": "60.5kg",
                      "beatenMargin": "1.25L", "startingPrice": "$7.50", "trackCondition": "Good", "isTrial": False})
        assert run["dist"] == 1609 and run["wt"] == 60.5 and run["sp"] == 7.5 and run["mgn"] == 1.25 and run["fin"] == 2, run
        print("selftest ok"); return
    today = dt.date.today()
    need = horses_needed(since=(today - dt.timedelta(days=1)).isoformat())
    print(f"{len(need)} horses with a placeholder id:", ", ".join(sorted(need)) or "-")
    if a.dry_run or not need:
        return
    api = rc_fields.Api(deadline=600, max_req=80)
    old = json.loads(OUT.read_text()) if OUT.exists() else {}
    for name, code in need.items():
        d = api.q("form", '{ GetHorseFormAll(horseCode: "%s") { %s } }' % (code, FIELDS))
        rows = ((d.get("data") or {}).get("GetHorseFormAll")) or []
        runs = [x for x in (to_run(e) for e in rows) if x and x["d"] < today.isoformat()]
        runs.sort(key=lambda x: x["d"], reverse=True)
        print(f"  {name} ({code}): {len(runs)} past runs")
        if runs:
            old[name.lower()] = runs
    OUT.write_text(json.dumps(old, separators=(",", ":"), sort_keys=True), encoding="utf-8")


if __name__ == "__main__":
    sys.exit(main())
