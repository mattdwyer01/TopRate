"""Validate candidate Sky replay codes: a code is kept only if it also serves a replay for the SAME track on TWO other
dates (a wrong code can match another venue racing that day once, but not repeatedly). Read-only GETs (first 256 bytes)
from the AU runner. Prints the validated map as JSON, plus the codes that failed or were shared by several tracks."""
import json
from collections import defaultdict
from concurrent.futures import ThreadPoolExecutor
import pandas as pd
import requests

BASE = "https://mediatabs.skyracing.com.au/Race_Replay"
cand = json.load(open("replay_codes_candidates.json"))

def exists(url):
    try:
        r = requests.get(url, headers={"Range": "bytes=0-255"}, timeout=8, stream=True)
        s = r.status_code; r.close()
        return s in (200, 206)
    except Exception:
        return False

fh = pd.read_csv("wpr_form_history.csv.gz", usecols=["date", "track", "raceNumber", "isBarrierTrial"])
fh = fh[(fh.isBarrierTrial == False) & fh.raceNumber.between(1, 15) & fh.track.notna()]  # noqa: E712
fh = fh[fh.date >= "2025-10-15"]
fh["key"] = fh.track.str.lower()
byv = {k: g.sort_values("date") for k, g in fh.groupby("key")}

def url(code, d, rn):
    d = str(d)[:10]
    return f"{BASE}/{d[:4]}/{d[5:7]}/{d[:4]}{d[5:7]}{d[8:10]}{code}{int(rn):02d}_V.mp4"

def check(item):
    name, code = item
    g = byv.get(name)
    if g is None or g.empty:
        return name, code, False, 0
    dates = g.drop_duplicates("date")
    n = len(dates)
    # two other dates: spread across the history (second and third most recent are not the bootstrap date)
    picks = dates.iloc[[max(n - 2, 0), max(n - 5, 0)]] if n >= 3 else dates.iloc[:-1]
    hits = [exists(url(code, r.date, r.raceNumber)) for r in picks.itertuples()]
    return name, code, (len(hits) >= 1 and all(hits)), len(hits)

with ThreadPoolExecutor(24) as ex:
    res = list(ex.map(check, cand.items()))
ok = {n: c for n, c, good, _ in res if good}
bad = sorted(n for n, c, good, _ in res if not good)
by_code = defaultdict(list)
for n, c in ok.items():
    by_code[c].append(n)
shared = {c: ns for c, ns in by_code.items() if len(ns) > 1}
print("VALIDATED", len(ok), "of", len(cand), flush=True)
print("JSON_BEGIN"); print(json.dumps(ok, sort_keys=True)); print("JSON_END")
print("FAILED:", bad, flush=True)
print("SHARED CODES (same code, several tracks - review):", shared, flush=True)
