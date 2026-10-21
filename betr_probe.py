"""Read-only: can the AU runner read Betr's race API without a browser (21 Oct 2026)? Plain urllib, normal headers, no TLS impersonation, no retries
or evasion: if Cloudflare challenges the request the probe reports it and stops. A handful of requests in total. Writes nothing."""
import json
import urllib.error
import urllib.request

H = "https://web20-api.bluebet.com.au"
HDR = {"Accept": "application/json", "User-Agent": "Mozilla/5.0 (X11; Linux x86_64) TopRate-personal-dashboard-probe",
       "Origin": "https://www.betr.com.au", "Referer": "https://www.betr.com.au/"}


def get(path):
    req = urllib.request.Request(H + path, headers=HDR)
    try:
        with urllib.request.urlopen(req, timeout=30) as r:
            return r.status, r.read()
    except urllib.error.HTTPError as e:
        return e.code, e.read()


def main():
    st, body = get("/GroupedRaceCard?DaysToRace=0")
    print("GroupedRaceCard", st, len(body), flush=True)
    if st != 200 or body[:1] not in (b"{", b"["):
        print("Blocked or not JSON, stopping (no workaround attempted). Start of body:", body[:200].decode("utf8", "replace"), flush=True)
        return
    d = json.loads(body)
    hits = []

    def walk(o, p=""):
        if isinstance(o, dict):
            for k, v in o.items():
                if isinstance(v, str) and ("happy valley" in v.lower() or "sha tin" in v.lower()):
                    hits.append((p + "." + k, v))
                walk(v, p + "." + k)
        elif isinstance(o, list):
            for i, v in enumerate(o):
                walk(v, f"{p}[{i}]")
    walk(d)
    print("Happy Valley / Sha Tin mentions:", hits[:6], flush=True)
    # one Hong Kong race: runner prices (a single extra request)
    ev = None

    def find(o):
        nonlocal ev
        if isinstance(o, dict):
            if o.get("Venue") == "Happy Valley" and o.get("RaceNumber") == 1 and o.get("EventId"):
                ev = o["EventId"]
            for v in o.values():
                find(v)
        elif isinstance(o, list):
            for v in o:
                find(v)
    find(d)
    print("Happy Valley R1 event id:", ev, flush=True)
    if not ev:
        return
    st, body = get(f"/Race?eventId={ev}")
    print("Race", st, len(body), flush=True)
    if st != 200 or body[:1] not in (b"{", b"["):
        print("Blocked or not JSON, stopping:", body[:200].decode("utf8", "replace"), flush=True)
        return
    r = json.loads(body)
    print("top-level keys:", sorted(r.keys()) if isinstance(r, dict) else type(r).__name__, flush=True)
    outs = r.get("Outcomes") or r.get("Runners") or r.get("Selections") or []
    if not outs:
        for k, v in r.items():
            if isinstance(v, list) and v and isinstance(v[0], dict):
                print("list key", k, len(v), "item keys", sorted(v[0].keys()), flush=True)
                outs = outs or v
    for o in outs[:4]:
        print(json.dumps(o, default=str)[:700], flush=True)


if __name__ == "__main__":
    main()
