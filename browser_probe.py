"""
browser_probe.py -- read-only headless-browser probe of the two pages a plain HTTP client cannot read (11 Oct 2026).

  WA : https://racingwa.com.au/rwa/meetings/thoroughbred/2026-10-03/Kalgoorlie/5196066
       sits behind Vercel's bot checkpoint (HTTP 429, needs JavaScript). A real browser passes it; we then list the
       page's links and the network requests it makes, to find where the sectional spreadsheet links come from
       (a JSON endpoint that lists every race's secttime file would remove the need for the browser afterwards).
  NSW: https://racing.australianturfclub.com.au/meeting/oY3R5qzn
       the "Sectionals" tab is filled by an AJAX call; click it and record the call (URL, method, form fields) and the
       rendered text, plus the /race-index page (the likely list of meetings).

Run on the AU self-hosted runner with the one-off venv that tab_probe.yml builds when setup_playwright=true
($HOME/pw-venv). Fixed URLs, no inputs, nothing written to the repo except tab_raw/ (gitignored).
"""
import argparse
import re
import sys
import time
from pathlib import Path

WA = "https://racingwa.com.au/rwa/meetings/thoroughbred/2026-10-03/Kalgoorlie/5196066"
ATC = "https://racing.australianturfclub.com.au/meeting/oY3R5qzn"
ATC_INDEX = "https://racing.australianturfclub.com.au/race-index"
OUT = Path(__file__).parent / "tab_raw"
UA = ("Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) "
      "Chrome/124.0.0.0 Safari/537.36")
DATA = re.compile(r"secttime|\.xlsx|race-files|sectional|/api/|\.json|admin-ajax|graphql", re.I)


def new_page(browser):
    ctx = browser.new_context(user_agent=UA, viewport={"width": 1366, "height": 900}, locale="en-AU",
                              timezone_id="Australia/Perth")
    page = ctx.new_page()
    seen = []
    page.on("response", lambda r: seen.append((r.request.method, r.status, r.request.resource_type, r.url,
                                               (r.request.post_data or "")[:300])))
    return page, seen


def wait_past_checkpoint(page, seconds=40):
    for i in range(seconds):
        t = page.title()
        if "checkpoint" not in t.lower() and "verifying" not in t.lower():
            return True
        time.sleep(1)
    return False


def report_requests(seen, limit=45):
    keep = [s for s in seen if s[2] in ("xhr", "fetch", "document") or DATA.search(s[3])]
    print(f"  network responses: {len(seen)} total, {len(keep)} data-like (xhr/fetch/document or data-looking URL)")
    for m, st, rt, url, post in keep[:limit]:
        print(f"   {m} {st} {rt} {url[:170]}" + (f"  POST={post}" if post else ""))


def probe_wa(browser):
    print("\n##### WA meeting page in a real browser")
    page, seen = new_page(browser)
    page.goto(WA, wait_until="domcontentloaded", timeout=60000)
    ok = wait_past_checkpoint(page)
    print(f"  passed checkpoint: {ok}; title={page.title()!r}; url={page.url}")
    try:
        page.wait_for_load_state("networkidle", timeout=20000)
    except Exception:
        print("  (network did not go idle in 20s)")
    html = page.content()
    (OUT / "wa_page_rendered.html").write_text(html)
    print(f"  rendered html: {len(html)} chars; mentions secttime={html.lower().count('secttime')} xlsx={html.lower().count('xlsx')} sectional={html.lower().count('sectional')}")
    links = page.eval_on_selector_all("a[href]", "els => els.map(e => e.href)")
    want = [l for l in dict.fromkeys(links) if re.search(r"secttime|xlsx|race-files|sectional|/meetings/", l, re.I)]
    print(f"  links of interest ({len(want)} of {len(set(links))}):")
    for l in want[:40]:
        print("   " + l[:190])
    report_requests(seen)
    txt = re.sub(r"\s+", " ", page.inner_text("body"))[:700]
    print(f"  visible text: {txt}")
    page.context.close()


def probe_atc(browser):
    print("\n##### ATC meeting page: click the Sectionals tab")
    page, seen = new_page(browser)
    page.goto(ATC, wait_until="domcontentloaded", timeout=60000)
    try:
        page.wait_for_load_state("networkidle", timeout=20000)
    except Exception:
        pass
    print(f"  title={page.title()!r}")
    before = len(seen)
    try:
        page.click("#aSectionals", timeout=8000)
        page.wait_for_timeout(5000)
        print("  clicked #aSectionals")
    except Exception as e:
        print(f"  could not click #aSectionals: {type(e).__name__}: {str(e)[:100]}")
    report_requests(seen[before:])
    try:
        txt = re.sub(r"\s+", " ", page.inner_text("#dvRacingSectionals"))
        print(f"  #dvRacingSectionals text ({len(txt)} chars): {txt[:1800]}")
    except Exception as e:
        print(f"  no #dvRacingSectionals text: {type(e).__name__}")
    race_tabs = page.eval_on_selector_all("[data-race-number]", "els => els.map(e => [e.tagName, e.className, e.getAttribute('data-race-number')])")
    print(f"  race selectors: {race_tabs[:12]}")
    (OUT / "atc_after_click.html").write_text(page.content())
    page.context.close()
    print("\n##### ATC /race-index")
    page, seen = new_page(browser)
    page.goto(ATC_INDEX, wait_until="domcontentloaded", timeout=60000)
    try:
        page.wait_for_load_state("networkidle", timeout=20000)
    except Exception:
        pass
    links = page.eval_on_selector_all("a[href]", "els => els.map(e => e.href)")
    meet = [l for l in dict.fromkeys(links) if "/meeting/" in l]
    print(f"  title={page.title()!r}; meeting links: {len(meet)}; first: {meet[:6]}")
    print("  text: " + re.sub(r"\s+", " ", page.inner_text("body"))[:900])
    report_requests(seen, 20)
    page.context.close()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=0, help="ignored (tab_probe.yml always passes it)")
    ap.add_argument("--date", default="", help="ignored")
    ap.add_argument("--any-status", action="store_true", help="ignored")
    ap.parse_args()
    OUT.mkdir(exist_ok=True)
    from playwright.sync_api import sync_playwright
    with sync_playwright() as p:
        browser = p.chromium.launch(headless=True)
        print("chromium", browser.version)
        for fn in (probe_wa, probe_atc):
            try:
                fn(browser)
            except Exception as e:
                print(f"\n{fn.__name__} failed: {type(e).__name__}: {str(e)[:300]}")
        browser.close()


if __name__ == "__main__":
    sys.exit(main())
