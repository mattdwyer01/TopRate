"""Read-only probe (16 Oct 2026): which field of a PAST race's page and of a runner's page carries the rating at the weight actually carried.
One race page and three runner pages of a resulted race, field names matching wpr/atw/rating/weight with their values, next to the results file's own
wpr / atw / weightCarried for the same runners. Writes nothing. Environment: TOPRATE_EMAIL, TOPRATE_PASSWORD, TOPRATE_ANON_KEY.
Usage: python toprate_atw_probe.py [race_id] [run_id ...]"""
import gzip
import json
import os
import re
import sys

import pandas as pd
import requests

import toprate_race_fetch as F

KEY = re.compile(r"wpr|atw|rating|weight|handicap|wfa|adjust", re.I)


def get(session, path):
    url = f"{F.WEB_BASE}{path}/__data.json?x-sveltekit-invalidated=0001"
    headers = {"apikey": os.environ["TOPRATE_ANON_KEY"], "Authorization": f"Bearer {session['access_token']}", "Accept": "application/json",
               "User-Agent": F.BROWSER_HEADERS["User-Agent"], "Referer": F.WEB_BASE + "/"}
    r = requests.get(url, headers=headers, cookies=F.cookie_pair(session), timeout=F.TIMEOUT, allow_redirects=False)
    print(f"GET {path} -> {r.status_code}")
    if r.status_code != 200:
        return None
    for node in r.json().get("nodes", []):
        if node.get("type") == "data" and node.get("data"):
            d = F.deref(node["data"], 0)
            if isinstance(d, dict) and len(d) > 1:
                return d
    return None


def pick(d, depth=0, path=""):
    """Every key matching KEY with a scalar value, one level of nesting deep."""
    out = {}
    if isinstance(d, dict):
        for k, v in d.items():
            if KEY.search(str(k)) and not isinstance(v, (dict, list)):
                out[path + k] = v
            elif isinstance(v, dict) and depth < 2:
                out.update(pick(v, depth + 1, path + k + "."))
    return out


def main():
    race_id = int(sys.argv[1]) if len(sys.argv) > 1 else 1761732
    run_ids = [int(x) for x in sys.argv[2:]] or [14480303, 14480299, 14480308]
    s = F.login(os.environ["TOPRATE_EMAIL"].strip(), os.environ["TOPRATE_PASSWORD"].strip(), os.environ["TOPRATE_ANON_KEY"].strip())
    page = get(s, f"/races/{race_id}")
    if page:
        print("race page keys:", sorted(page.keys()))
        rr = page.get("raceResult")
        print("raceResult type:", type(rr).__name__, (sorted(rr.keys()) if isinstance(rr, dict) else (len(rr) if rr else None)))
        ent = rr[0] if isinstance(rr, list) and rr else (rr or {})
        print("raceResult first:", json.dumps(pick(ent) or {k: type(v).__name__ for k, v in (ent.items() if isinstance(ent, dict) else [])}, default=str)[:900])
        rrr = (rr or {}).get("runners") if isinstance(rr, dict) else None
        print("raceResult.runners:", type(rrr).__name__, len(rrr) if rrr else None)
        for e in (rrr or [])[:3]:
            print("raceResult runner:", json.dumps(e, default=str)[:900])
        for f in (page.get("raceFields") or [])[:3]:
            print("raceField", f.get("runId"), f.get("horse"), json.dumps(pick(f), default=str)[:600])
        ru = page.get("raceUser") or {}
        for a in (ru.get("runAdjustments") or [])[:3]:
            print("runAdjustment", a.get("runId"), json.dumps(a, default=str)[:700])
    for rid in run_ids:
        p = get(s, f"/runners/{rid}")
        if not p:
            continue
        print("runner page keys:", sorted(p.keys())[:30])
        rec = p.get("runnerRecord") or p.get("runner") or p
        form = None
        for k, v in p.items():
            if isinstance(v, dict) and isinstance(v.get("form"), list):
                form = v["form"]
        form = form or p.get("form") or []
        print(f"run {rid}: form rows {len(form)}; first row rating-like fields:", json.dumps(pick(form[0]), default=str)[:700] if form else None)
        for row in form:
            if row.get("raceId") == race_id:
                print("  the probed race inside this runner's own form list:", json.dumps(pick(row), default=str)[:500])
        print("  top-level rating-like:", json.dumps(pick(p), default=str)[:700])
    # results files for the same race
    for y in ("2026",):
        f = f"race_results_{y}.csv.gz"
        if os.path.exists(f):
            d = pd.read_csv(f, low_memory=False)
            d = d[d.race_id == race_id][[c for c in ("horse", "wpr", "atw", "weightCarried", "positionFinish") if c in d.columns]]
            print("results file rows for the race:\n" + d.to_string(index=False))


if __name__ == "__main__":
    main()
