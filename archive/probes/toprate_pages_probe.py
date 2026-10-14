"""Read-only: one GET per candidate toprate.au page, status plus the field names and types of its __data.json (no values kept). Stops probing a
route family at the first 403 (the account is not allowed there; nothing is done to get around it).
Environment: TOPRATE_EMAIL, TOPRATE_PASSWORD, TOPRATE_ANON_KEY."""
import json
import os
import sys
import time

import requests

import toprate_race_fetch as f

PATHS = ["/runners/14477830", "/meetings/145083", "/meetings/145083/history", "/horses/415921", "/persons/3043", "/jockeys/3043",
         "/trainers/11736", "/tracks/276", "/sires/6806", "/calendar/today", "/dashboard"]


def shape(o, depth=0, maxd=5):
    if isinstance(o, dict):
        if depth >= maxd:
            return "{" + ",".join(list(o)[:15]) + ("..." if len(o) > 15 else "") + "}"
        return {k: shape(v, depth + 1, maxd) for k, v in list(o.items())[:80]}
    if isinstance(o, list):
        return [shape(o[0], depth + 1, maxd), f"[{len(o)} items]"] if o else []
    return type(o).__name__


def main():
    email, pw, anon = (os.environ.get(k, "").strip() for k in ("TOPRATE_EMAIL", "TOPRATE_PASSWORD", "TOPRATE_ANON_KEY"))
    if not (email and pw and anon):
        sys.exit("credentials missing")
    session = f.login(email, pw, anon)
    h = {"apikey": anon, "Authorization": f"Bearer {session['access_token']}", "Accept": "application/json",
         "User-Agent": f.BROWSER_HEADERS["User-Agent"], "Referer": f.WEB_BASE + "/"}
    c = f.cookie_pair(session)
    for p in PATHS:
        time.sleep(0.5)
        r = requests.get(f"{f.WEB_BASE}{p}/__data.json?x-sveltekit-invalidated=1111", headers=h, cookies=c, timeout=30, allow_redirects=False)
        block = r.text.lstrip().startswith("<!DOCTYPE html")
        print(f"\n{p}: HTTP {r.status_code} bytes {len(r.text)}{' CLOUDFLARE BLOCK' if block else ''}"
              f"{' -> ' + str(r.headers.get('location')) if r.status_code in (301, 302, 303, 307, 308) else ''}")
        if r.status_code != 200 or block:
            if r.status_code != 404:
                print("   body:", r.text[:60].replace("\n", " "))
            continue
        try:
            payload = r.json()
        except ValueError:
            print("   not JSON")
            continue
        nodes = payload.get("nodes", []) if isinstance(payload, dict) else []
        for n, node in enumerate(nodes):
            if isinstance(node, dict) and node.get("type") == "data" and node.get("data"):
                d = f.deref(node["data"], 0)
                print(f"   node {n}: {json.dumps(shape(d), default=str)[:3500]}")
            elif isinstance(node, dict) and node.get("type") not in (None, "skip"):
                print(f"   node {n}: {node.get('type')}")


if __name__ == "__main__":
    main()
