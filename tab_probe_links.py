"""
tab_probe_links.py -- read-only probe: follow the _links TAB gives for one race (past form, etc.) and show what comes back.

Why (Oct 2026): the first probe (tab_probe_race_fields.py) showed a race's detail has no margins, race time or sectionals,
but every runner has a `_links.form` link (past form) that returned HTTP 503 from our client. This prints every link in
full, fetches each distinct kind with a few request variants (as given, with/without the jurisdiction parameter,
different TLS fingerprints), and shows the status, content type and a body snippet, so we can tell a real "no data" 503
from a request our client is getting wrong. Successful JSON is saved to tab_raw/ and its key paths printed (">>" marks
margin / time / sectional / distance / age / sex style names).

Run on the AU self-hosted runner (TAB geo-blocks other hosts), via tab_probe.yml with script=tab_probe_links.py.
Read-only: writes only to tab_raw/ (gitignored).
"""
import argparse
import json
import sys
from datetime import date
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import tab_results_poller as poller
import tab_probe_race_fields as P

OUT = P.OUT


def collect_links(obj, path="", out=None):
    out = [] if out is None else out
    if isinstance(obj, dict):
        for k, v in obj.items():
            if k == "_links" and isinstance(v, dict):
                for lk, lv in v.items():
                    out.append((path or "<root>", lk, lv))
            else:
                collect_links(v, f"{path}.{k}" if path else k, out)
    elif isinstance(obj, list):
        for v in obj[:2]:
            collect_links(v, path + "[]", out)
    return out


def raw_get(url, impersonate="chrome", accept=True):
    r = poller._cr.get(url, impersonate=impersonate, timeout=20, headers={"Accept": "application/json"} if accept else {})
    return r


def attempt(label, url, impersonate="chrome", accept=True):
    try:
        r = raw_get(url, impersonate, accept)
    except Exception as e:
        print(f"  [{label}] {impersonate} accept={accept}: {type(e).__name__}: {str(e)[:120]}")
        return None
    ct = r.headers.get("content-type", "")
    body = r.text or ""
    print(f"  [{label}] {impersonate} accept={accept}: HTTP {r.status_code} {ct} len={len(body)}")
    if r.status_code != 200:
        print("     body: " + body[:300].replace("\n", " "))
        keys = {k: v for k, v in r.headers.items() if k.lower() in ("retry-after", "x-cache", "via", "server", "x-amzn-errortype", "x-error")}
        if keys:
            print(f"     headers: {keys}")
        return None
    try:
        return r.json()
    except Exception:
        print("     (200 but not JSON) " + body[:200].replace("\n", " "))
        return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--date", default=str(date.today()))
    ap.add_argument("--jur", default="VIC")
    ap.add_argument("--n", type=int, default=1, help="races to explore")
    ap.add_argument("--any-status", action="store_true", help="unfinished races only (default: finished races)")
    args = ap.parse_args()
    if poller._cr is None:
        print("curl_cffi not installed; cannot run")
        return
    OUT.mkdir(exist_ok=True)
    payload = poller.get(poller.MEETINGS.format(date=args.date), {"jurisdiction": args.jur}, timeout=20)
    done = 0
    for m in payload.get("meetings", []):
        if m.get("raceType") != poller.RACE_TYPE or not m.get("venueMnemonic"):
            continue
        links = collect_links({k: v for k, v in m.items() if k != "races"})
        print(f"\n##### meeting {m.get('meetingName')} ({m.get('venueMnemonic')}) _links:")
        for path, lk, lv in links:
            print(f"   {path}.{lk} = {lv}")
        for rc in m.get("races", []):
            final = rc.get("raceStatus") in poller.FINAL_STATUSES
            if final == args.any_status or not rc.get("hasForm", True):
                continue
            n = rc["raceNumber"]
            print(f"\n##### {m.get('meetingName')} R{n} status={rc.get('raceStatus')}")
            for path, lk, lv in collect_links(rc):
                print(f"   stub {path}.{lk} = {lv}")
            det = poller.get(poller.RACE_DETAIL.format(date=args.date, venue_mnemonic=m["venueMnemonic"], race_no=n),
                             {"jurisdiction": args.jur}, timeout=20)
            seen = {}
            for path, lk, lv in collect_links(det):
                print(f"   detail {path}.{lk} = {lv}")
                if lk != "silk" and isinstance(lv, str) and lv.startswith("http"):
                    seen.setdefault((path.split("[]")[0] if "runners" in path else path, lk), lv)
            for (path, lk), url in seen.items():
                print(f"\n  --- link {path}._links.{lk}")
                print(f"      {url}")
                base = url.split("?")[0]
                variants = [("as given", url, "chrome", True), ("as given", url, "chrome", False),
                            ("as given", url, "safari", True), ("as given", url, "firefox", True)]
                if "jurisdiction" not in url:
                    variants.append(("+jurisdiction", base + "?jurisdiction=" + args.jur, "chrome", True))
                else:
                    variants.append(("-jurisdiction", base, "chrome", True))
                got = None
                for label, u, imp, acc in variants:
                    got = attempt(label, u, imp, acc)
                    if got is not None:
                        break
                if got is not None:
                    name = f"{args.date}_{m.get('meetingName')}_R{n}_{lk}".replace(" ", "-")
                    (OUT / f"{name}.json").write_text(json.dumps(got, indent=1, default=str))
                    P.show(f"{name} ({lk})", got)
            done += 1
            if done >= args.n:
                return
            break


if __name__ == "__main__":
    main()
