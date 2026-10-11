"""
sectional_probe.py -- read-only probe of the two NSW / WA sectional sources the user pointed at (11 Oct 2026).

  WA : https://static.p.racingwa.com.au/race-files/<meetingId>/0/secttime/<date>-<track>-<stamp>.xlsx  (sectional times spreadsheet)
       found from the meeting page https://racingwa.com.au/rwa/meetings/thoroughbred/<date>/<Track>/<meetingId>
  NSW: https://racing.australianturfclub.com.au/meeting/<code>  (Australian Turf Club meeting page)

What it prints, so a loader can be written without guessing:
  * the spreadsheet: sheet names, shape, and the first rows of every sheet (does it carry finish time, margin, per-200m splits, tab number?)
  * each page: HTTP status, title, links that look like data (xlsx / json / api / sectional / secttime) and script bundles,
    so the page's own data endpoint or the file pattern for every race can be found.
Raw bytes are saved under tab_raw/ (gitignored). The URLs are fixed below on purpose: tab_probe.yml passes no URL input, so
nothing user-supplied reaches a shell or an HTTP client.

Run on the AU self-hosted runner (the sandbox cannot reach these hosts): tab_probe.yml with script=sectional_probe.py.
"""
import argparse
import io
import re
import sys
from pathlib import Path

URLS = {
    "wa_xlsx": "https://static.p.racingwa.com.au/race-files/5196066/0/secttime/2026-10-03-kal-1791155307821.xlsx",
    "wa_page": "https://racingwa.com.au/rwa/meetings/thoroughbred/2026-10-03/Kalgoorlie/5196066",
    "nsw_page": "https://racing.australianturfclub.com.au/meeting/oY3R5qzn",
}
OUT = Path(__file__).parent / "tab_raw"
LINK = re.compile(r"""https?://[^\s"'<>\\)]+|(?<=["'(])/[A-Za-z0-9_\-./]+\.(?:xlsx|json|csv|pdf)[^\s"'<>\\)]*""", re.I)
INTEREST = re.compile(r"xlsx|json|csv|secttime|sectional|race-files|/api/|graphql|_next/data|\.js(\?|$)", re.I)


def fetch(url, binary=False):
    try:
        from curl_cffi import requests as cr
        r = cr.get(url, impersonate="chrome", timeout=30, headers={"Accept": "*/*"})
    except ImportError:
        import requests
        r = requests.get(url, timeout=30, headers={"User-Agent": "Mozilla/5.0"})
    return r


def show_xlsx(content):
    try:
        import pandas as pd
        sheets = pd.read_excel(io.BytesIO(content), sheet_name=None, header=None)
    except Exception as e:
        print(f"  could not read xlsx: {type(e).__name__}: {e}")
        return
    print(f"  sheets: {list(sheets)}")
    for name, df in sheets.items():
        print(f"\n  --- sheet {name!r} shape={df.shape}")
        with __import__("pandas").option_context("display.width", 250, "display.max_columns", 40, "display.max_colwidth", 22):
            print(df.head(28).to_string())


def show_page(label, url):
    r = fetch(url)
    body = r.text or ""
    title = re.search(r"<title[^>]*>(.*?)</title>", body, re.I | re.S)
    print(f"\n===== {label}: HTTP {r.status_code} {r.headers.get('content-type', '')} len={len(body)} title={title.group(1).strip()[:100] if title else None}")
    (OUT / f"{label}.html").write_text(body)
    links = []
    for m in LINK.findall(body):
        if INTEREST.search(m) and m not in links:
            links.append(m)
    print(f"  data-like links ({len(links)}):")
    for m in links[:60]:
        print("   " + m[:200])
    for kw in ("sectional", "secttime", "xlsx", "__NEXT_DATA__", "window.__", "application/json", "apollo", "graphql"):
        print(f"  mentions {kw!r}: {body.lower().count(kw.lower())}")
    text = re.sub(r"<script.*?</script>|<style.*?</style>", " ", body, flags=re.S | re.I)
    text = re.sub(r"<[^>]+>", " ", text)
    text = re.sub(r"\s+", " ", text).strip()
    print(f"  visible text ({len(text)} chars): {text[:700]}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=0, help="ignored (tab_probe.yml always passes it)")
    ap.add_argument("--date", default="", help="ignored")
    ap.add_argument("--any-status", action="store_true", help="ignored")
    ap.parse_args()
    OUT.mkdir(exist_ok=True)
    print("##### WA spreadsheet")
    try:
        r = fetch(URLS["wa_xlsx"])
        print(f"  HTTP {r.status_code} {r.headers.get('content-type', '')} bytes={len(r.content)}")
        if r.status_code == 200:
            (OUT / "wa_secttime.xlsx").write_bytes(r.content)
            show_xlsx(r.content)
    except Exception as e:
        print(f"  failed: {type(e).__name__}: {e}")
    for label in ("wa_page", "nsw_page"):
        try:
            show_page(label, URLS[label])
        except Exception as e:
            print(f"\n===== {label}: failed: {type(e).__name__}: {e}")


if __name__ == "__main__":
    sys.exit(main())
