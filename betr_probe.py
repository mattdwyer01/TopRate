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
    s = json.dumps(d)
    i = s.lower().find("happy valley")
    if i >= 0:
        print(s[max(0, i - 300):i + 900], flush=True)


if __name__ == "__main__":
    main()
