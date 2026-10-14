"""Read-only inventory of what toprate.au exposes to the logged-in account (14 Oct 2026). Prints structure only: route patterns, the data calls the
site's own scripts make, and for each page type the field names/types of its __data.json. No bulk download, a short pause between requests.

Environment: TOPRATE_EMAIL, TOPRATE_PASSWORD, TOPRATE_ANON_KEY.  Usage: python toprate_inventory.py
"""
import json
import os
import re
import sys
import time
from urllib.parse import urljoin

import requests

import toprate_race_fetch as f

UA = {"User-Agent": f.BROWSER_HEADERS["User-Agent"]}
PAUSE = 0.4
# a known id of each kind (seen on the race page of 14 Oct 2026)
SAMPLE = {"raceId": 1761577, "race": 1761577, "runId": 14477830, "runnerId": 14477830, "runner": 14477830, "meetingId": 145083, "meeting": 145083,
          "horseId": 415921, "horse": 415921, "jockeyId": 3043, "jockey": 3043, "trainerId": 11736, "trainer": 11736, "sireId": 6806, "sire": 6806,
          "trackId": 276, "track": 276, "id": 415921, "date": "2026-10-14"}


def get(url, **kw):
    time.sleep(PAUSE)
    try:
        return requests.get(url, timeout=30, **kw)
    except requests.RequestException as e:
        print("  GET failed:", url[:90], type(e).__name__)
        return None


def shape(o, depth=0, maxd=3):
    if isinstance(o, dict):
        if depth >= maxd:
            return "{" + ",".join(list(o)[:12]) + ("..." if len(o) > 12 else "") + "}"
        return {k: shape(v, depth + 1, maxd) for k, v in list(o.items())[:60]}
    if isinstance(o, list):
        return [shape(o[0], depth + 1, maxd), f"[{len(o)} items]"] if o else []
    return type(o).__name__


def main():
    email, pw, anon = (os.environ.get(k, "").strip() for k in ("TOPRATE_EMAIL", "TOPRATE_PASSWORD", "TOPRATE_ANON_KEY"))
    if not (email and pw and anon):
        sys.exit("credentials missing")
    # 1. the site's scripts
    html = get(f.WEB_BASE + "/", headers=UA).text
    todo = [urljoin(f.WEB_BASE + "/", m) for m in re.findall(r'(?:href|import\()\s*=?\s*["\']([^"\']+\.m?js)["\']', html)]
    texts, seen = {}, set()
    while todo and len(seen) < 400:
        u = todo.pop(0)
        if u in seen or not u.startswith(f.WEB_BASE + "/"):
            continue
        seen.add(u)
        r = get(u, headers=UA)
        if r is None or r.status_code != 200:
            continue
        texts[u] = r.text
        todo += [urljoin(u, m) for m in re.findall(r'["\'](\.{1,2}/[A-Za-z0-9_\-\./]+\.m?js)["\']', r.text)]
    blob = "\n".join(texts.values())
    print(f"scripts read: {len(texts)} ({len(blob) // 1000} KB)")
    routes = sorted(set(re.findall(r'["\'](/[A-Za-z0-9_\-\[\]\.\(\)/]*)["\']\s*:\s*\[\s*\d', blob)))
    print("\nROUTE PATTERNS (SvelteKit client manifest):")
    for x in routes:
        print("  ", x)
    rpcs = sorted(set(re.findall(r'/rest/v1/rpc/([a-z_0-9]+)', blob)) | set(re.findall(r'\.rpc\(\s*["\']([a-z_0-9]+)["\']', blob)))
    tables = sorted(set(re.findall(r'\.from\(\s*["\']([a-z_0-9]+)["\']', blob)))
    print("\nRPC CALLS in the site's scripts:", rpcs)
    print("TABLES read by the site's scripts:", tables)
    rest = sorted(set(re.findall(r'["\'`]/(?:api|v1)/[A-Za-z0-9_\-/\.\$\{\}]+["\'`]', blob)))[:60]
    print("api-like paths:", rest)

    # 2. every parameterised page type, one request each
    session = f.login(email, pw, anon)
    h = {"apikey": anon, "Authorization": f"Bearer {session['access_token']}", "Accept": "application/json",
         "User-Agent": UA["User-Agent"], "Referer": f.WEB_BASE + "/"}
    c = f.cookie_pair(session)
    print("\nPAGE TYPES (authenticated __data.json, structure only):")
    for route in routes:
        if route.startswith("/_") or "api" in route.split("/")[1:2]:
            continue
        def fill(m):
            name = m.group(1)
            return str(SAMPLE.get(name, SAMPLE.get(name.rstrip("s"), 1)))
        path = re.sub(r"\[\[?\.{0,3}([A-Za-z0-9_]+)\]?\]", fill, route)
        path = re.sub(r"/\([^)]*\)", "", path)       # route groups
        url = f.WEB_BASE + (path.rstrip("/") or "") + "/__data.json?x-sveltekit-invalidated=" + "1" * 4
        r = get(url, headers=h, cookies=c, allow_redirects=False)
        if r is None:
            continue
        block = r.text.lstrip().startswith("<!DOCTYPE html") and "cloudflare" in str(r.headers.get("server", "")).lower()
        line = f"  {route} -> {path}: HTTP {r.status_code} bytes {len(r.text)}{' CLOUDFLARE BLOCK' if block else ''}"
        if r.status_code in (301, 302, 303, 307, 308):
            line += f" -> {r.headers.get('location')}"
        print(line)
        if r.status_code == 200 and not block:
            try:
                page = f.parse_page(r.json()) or None
                if page is None:
                    for node in r.json().get("nodes", []):
                        if node.get("type") == "data" and node.get("data"):
                            page = f.deref(node["data"], 0)
                            break
                print("     keys:", json.dumps(shape(page), default=str)[:1500])
            except Exception as e:
                print("     (could not parse:", type(e).__name__, ")")

    # 3. the site's own RPCs, one call each with an empty or id-only body (status only; a Cloudflare block page is reported, not worked around)
    print("\nRPC STATUS (as the site calls them):")
    skipped = [n for n in rpcs if not n.startswith(("get_", "list_", "search_", "find_"))]
    if skipped:
        print("  not called (name does not look read-only):", skipped)
    for name in [n for n in rpcs if n not in skipped]:
        body = {"rc_id": SAMPLE["raceId"]} if "race" in name else ({"horse_id": SAMPLE["horseId"]} if "horse" in name else {})
        time.sleep(PAUSE)
        r = requests.post(f"{f.API_BASE}/rest/v1/rpc/{name}", headers={**f.BROWSER_HEADERS, "apikey": anon, "Authorization": f"Bearer {session['access_token']}",
                                                                       "Content-Type": "application/json"}, json=body, timeout=30)
        block = r.text.lstrip().startswith("<!DOCTYPE html")
        extra = ""
        if r.status_code == 200:
            try:
                j = r.json()
                extra = f" | {type(j).__name__} len {len(j) if hasattr(j, '__len__') else '?'}"
            except ValueError:
                pass
        print(f"  {name}: HTTP {r.status_code}{' CLOUDFLARE BLOCK' if block else ''}{extra} | {'' if block else r.text[:80]!r}")


if __name__ == "__main__":
    main()
