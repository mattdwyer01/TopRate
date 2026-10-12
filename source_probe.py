"""
source_probe.py -- read-only probe of free results sources that might carry margins and times for WA, TAS, NT, ACT and country NSW (12 Oct 2026).

Fixed URLs, no inputs (tab_probe.yml passes none to it). For each candidate it prints HTTP status, size, title, which of
margin / time / last-600 / sectional words appear, and the header row of the first results-looking table. For Racing Australia's
FreeFields it first reads the results calendar of each state to find real meeting keys, then opens one meeting per state.
Run on the AU runner via tab_probe.yml (script=source_probe.py). Writes only to tab_raw/ (gitignored).
"""
import argparse
import re
import sys
from pathlib import Path

OUT = Path(__file__).parent / "tab_raw"
BASE_RA = "https://www.racingaustralia.horse"
CANDIDATES = [
    ("RA calendar NSW", BASE_RA + "/FreeFields/Calendar_Results.aspx?State=NSW"),
    ("RA calendar WA", BASE_RA + "/FreeFields/Calendar_Results.aspx?State=WA"),
    ("RA calendar TAS", BASE_RA + "/FreeFields/Calendar_Results.aspx?State=TAS"),
    ("RA calendar NT", BASE_RA + "/FreeFields/Calendar_Results.aspx?State=NT"),
    ("RA calendar ACT", BASE_RA + "/FreeFields/Calendar_Results.aspx?State=ACT"),
    ("racing.com results", "https://www.racing.com/results"),
    ("R&S meeting results (country NSW)", "https://new.racingandsports.com/horse-racing-results/australia/newcastle/2025-01-10"),
    ("RSN meeting results (Tamworth)", "https://rsn.net.au/horse-racing-results/australia/tamworth/2024-09-30"),
    ("Racing NSW", "https://www.racingnsw.com.au/"),
    ("Tasracing", "https://www.tasracing.com.au/"),
    ("Racing and Wagering WA results", "https://www.rwwa.com.au/"),
    ("Sky Racing results", "https://www.skyracing.com.au/"),
    ("Punters results", "https://www.punters.com.au/horse-racing-results/"),
    ("Racenet results", "https://www.racenet.com.au/results/horse-racing"),
]
WORDS = ["margin", "winning time", "race time", "last 600", "l600", "sectional", "length", "lengths", "weight"]


def fetch(url):
    try:
        from curl_cffi import requests as cr
        return cr.get(url, impersonate="chrome", timeout=30, headers={"Accept": "text/html,*/*"})
    except ImportError:
        import requests
        return requests.get(url, timeout=30, headers={"User-Agent": "Mozilla/5.0"})


def squash(t, n=300):
    return re.sub(r"\s+", " ", re.sub(r"<[^>]+>", " ", t or "")).strip()[:n]


def describe(label, url, save=None):
    try:
        r = fetch(url)
    except Exception as e:
        print(f"\n##### {label}: {url}\n  failed {type(e).__name__}: {str(e)[:120]}")
        return None
    body = r.text or ""
    title = re.search(r"<title[^>]*>(.*?)</title>", body, re.I | re.S)
    low = body.lower()
    hits = {w: low.count(w) for w in WORDS if low.count(w)}
    print(f"\n##### {label}: {url}\n  HTTP {r.status_code} len={len(body)} title={squash(title.group(1), 90) if title else None}")
    print(f"  words: {hits}")
    ths = re.findall(r"<th[^>]*>(.*?)</th>", body, re.S)
    if ths:
        print("  table headers: " + " | ".join(squash(t, 25) for t in ths[:24]))
    if r.status_code != 200:
        print("  body: " + squash(body, 200))
    if save:
        OUT.mkdir(exist_ok=True)
        (OUT / save).write_text(body)
    return body


def racing_australia():
    print("\n===== Racing Australia FreeFields: find real meeting keys, open one per state")
    for st in ("NSW", "WA", "TAS", "NT", "ACT", "QLD"):
        body = describe(f"RA calendar {st} (links)", f"{BASE_RA}/FreeFields/Calendar_Results.aspx?State={st}")
        if not body:
            continue
        keys = list(dict.fromkeys(re.findall(r"Results\.aspx\?Key=([^\"'&<>\s]+)", body)))
        print(f"  result links found: {len(keys)}; first: {keys[:4]}")
        if keys:
            k = keys[-1] if len(keys) > 1 else keys[0]
            b = describe(f"RA results {st} {k}", f"{BASE_RA}/FreeFields/Results.aspx?Key={k}", save=f"ra_{st}.html")
            if b:
                j = b.lower().find("margin")
                print("  around 'margin': " + squash(b[max(0, j - 300): j + 900], 700))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=0)
    ap.add_argument("--date", default="")
    ap.add_argument("--any-status", action="store_true")
    ap.parse_args()
    for label, url in CANDIDATES[5:]:
        describe(label, url)
    racing_australia()


if __name__ == "__main__":
    sys.exit(main())
