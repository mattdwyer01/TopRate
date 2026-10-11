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
            print(df.head(4).to_string())


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


def snippets(body, kw, width=260, limit=6):
    low = body.lower()
    i, out = 0, []
    while len(out) < limit:
        j = low.find(kw.lower(), i)
        if j < 0:
            break
        out.append(re.sub(r"\s+", " ", body[max(0, j - width): j + width]))
        i = j + len(kw)
    return out


def deep_nsw(url):
    r = fetch(url)
    body = r.text or ""
    print("\n##### NSW deep look (HTTP %s, %d chars)" % (r.status_code, len(body)))
    for sn in snippets(body, "sectional"):
        print("  [sectional] ..." + sn + "...")
    for sn in snippets(body, "application/json", 200, 3):
        print("  [json] ..." + sn + "...")
    print("  tables: %d  iframes: %s" % (len(re.findall(r"<table", body, re.I)), re.findall(r"<iframe[^>]+src=[\"']([^\"']+)", body, re.I)[:8]))
    hrefs = [h for h in re.findall(r"href=[\"']([^\"']+)", body, re.I) if re.search(r"sectional|result|race|meeting|download|pdf|xls|csv", h, re.I)]
    print("  relevant hrefs (%d):" % len(set(hrefs)))
    for h in list(dict.fromkeys(hrefs))[:40]:
        print("   " + h[:200])
    print("  ajax/api patterns: %s" % sorted(set(re.findall(r"[\"'](/[A-Za-z0-9_\-/]*(?:ajax|api|rest|json)[A-Za-z0-9_\-/.?=&]*)[\"']", body, re.I)))[:25])
    print("  data-attributes with meeting/race: %s" % sorted(set(re.findall(r"data-(?:meeting|race|track|venue)[a-z\-]*=[\"'][^\"']{1,60}[\"']", body, re.I)))[:20])
    inl = [re.sub(r"\s+", " ", m)[:500] for m in re.findall(r"<script(?![^>]*src)[^>]*>(.*?)</script>", body, re.S | re.I) if re.search(r"meeting|race|sectional|fetch\(|ajax", m, re.I)]
    print("  inline scripts mentioning meeting/race/sectional/fetch: %d" % len(inl))
    for m in inl[:5]:
        print("   > " + m)
    print("  visible text around the first race heading:")
    text = re.sub(r"<script.*?</script>|<style.*?</style>", " ", body, flags=re.S | re.I)
    text = re.sub(r"\s+", " ", re.sub(r"<[^>]+>", " ", text))
    k = text.lower().find("race 1")
    print("   " + text[max(0, k - 200): k + 1500])


def deep_wa():
    base = "https://static.p.racingwa.com.au/race-files/5196066/"
    print("\n##### WA static host: can the file names be listed?")
    for u in (base, base + "0/", base + "0/secttime/", "https://static.p.racingwa.com.au/", base + "0/index.json", base + "index.json"):
        try:
            r = fetch(u)
            print("  %-70s HTTP %s %s len=%d  %s" % (u[-70:], r.status_code, r.headers.get("content-type", ""), len(r.content), (r.text or "")[:160].replace("\n", " ")))
        except Exception as e:
            print("  %s failed: %s" % (u[-60:], type(e).__name__))
    r = fetch("https://racingwa.com.au/")
    print("  racingwa.com.au home: HTTP %s title-ish: %s" % (r.status_code, re.sub(r"\s+", " ", (r.text or "")[:200])))
    import subprocess
    for cmd in (["python3", "-m", "pip", "show", "playwright"], ["python3", "-m", "pip", "show", "openpyxl"]):
        try:
            o = subprocess.run(cmd, capture_output=True, text=True, timeout=30)
            print("  %s -> %s" % (" ".join(cmd[-3:]), (o.stdout.splitlines()[:2] or [o.stderr.strip()[:80]])))
        except Exception as e:
            print("  %s failed: %s" % (cmd, type(e).__name__))


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
    for fn, arg in ((deep_nsw, URLS["nsw_page"]), (deep_wa, None)):
        try:
            fn(arg) if arg else fn()
        except Exception as e:
            print(f"\n{fn.__name__}: failed: {type(e).__name__}: {e}")


if __name__ == "__main__":
    sys.exit(main())
