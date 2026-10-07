"""One-off: find Sky replay venue codes for every track in the form history by trying likely codes against a real past
race at that track. Sky file names are YYYYMMDD + CODE + 2-digit race number; known codes are 3 letters from the name
plus R (BUBR Bunbury, GEER Geelong, MTGR Mt Gambier, GCPR Gold Coast Poly, RKER Randwick Kensington). Read-only GETs of
public replay files (first 256 bytes) from the AU runner; prints the found map as JSON and the venues with no hit."""
import itertools, json, re
from concurrent.futures import ThreadPoolExecutor
import pandas as pd
import requests

BASE = "https://mediatabs.skyracing.com.au/Race_Replay"

def splits(n, k):
    """All ways to write k as an ordered sum of n positive ints."""
    if n == 1:
        yield (k,); return
    for first in range(1, k - n + 2):
        for rest in splits(n - 1, k - first):
            yield (first,) + rest

def candidates(name):
    words = [w for w in re.findall(r"[A-Za-z]+", name.upper()) if w not in ("PARK", "SYNTHETIC")] or re.findall(r"[A-Za-z]+", name.upper())
    out = []
    if len(words) > 3:
        words = words[:3]
    for total, suffix in ((3, "R"), (4, ""), (3, "T")):
        for sp in splits(len(words), total):
            if any(k > len(w) for k, w in zip(sp, words)):
                continue
            out.append("".join(w[:k] for k, w in zip(sp, words)) + suffix)
    # Codes are not always plain prefixes (Bunbury = BUBR: B, U, then the B of "bury"), so also try ordered letter
    # subsequences that keep each word's first letter.
    def subseq(word, k, span=6):
        for idx in itertools.combinations(range(1, min(len(word), span)), k - 1):
            yield word[0] + "".join(word[i] for i in idx)
    if len(words) == 1:
        subs = [c for c in subseq(words[0], 3)]
    elif len(words) == 2:
        subs = [a + b[0] for a in subseq(words[0], 2, 4) for b in [words[1]]] + [words[0][0] + b for b in subseq(words[1], 2, 4)]
    else:
        subs = []
    out += [c + "R" for c in subs] + [c + "T" for c in subs]
    return list(dict.fromkeys(out))[:40]

def exists(url):
    try:
        r = requests.get(url, headers={"Range": "bytes=0-255"}, timeout=8, stream=True)
        s = r.status_code; r.close()
        return s in (200, 206)
    except Exception:
        return False

fh = pd.read_csv("wpr_form_history.csv.gz", usecols=["date", "track", "raceNumber", "isBarrierTrial"])
fh = fh[(fh.isBarrierTrial == False) & fh.raceNumber.between(1, 15) & fh.track.notna()]  # noqa: E712
fh = fh[fh.date >= "2025-10-15"].sort_values("date")
pick = fh.groupby("track").tail(1)
known = json.load(open("replay_codes.json")) if __import__("os").path.exists("replay_codes.json") else {}

def work(row):
    name, d, rn = row.track, str(row.date)[:10], int(row.raceNumber)
    if name.lower() in known:
        return name, known[name.lower()], d
    y, m = d[:4], d[5:7]
    for code in candidates(name):
        if exists(f"{BASE}/{y}/{m}/{y}{m}{d[8:10]}{code}{rn:02d}_V.mp4"):
            return name, code, d
    return name, None, d

with ThreadPoolExecutor(24) as ex:
    res = list(ex.map(work, [r for r in pick.itertuples()]))
found = {n.lower(): c for n, c, _ in res if c}
print("FOUND", len(found), "of", len(res), flush=True)
print("JSON_BEGIN"); print(json.dumps(found, sort_keys=True)); print("JSON_END")
print("UNRESOLVED:", sorted(n for n, c, _ in res if not c), flush=True)
