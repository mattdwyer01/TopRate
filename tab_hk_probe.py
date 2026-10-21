"""Read-only: how does TAB list Hong Kong thoroughbred meetings (21 Oct 2026)? The poller keeps only Australian locations, but its own notes say the
meeting list mixes in international meetings under every jurisdiction. Lists every non-Australian thoroughbred meeting for today and yesterday (UTC)
with its location code, mnemonic, race count and race stub keys, then reads one Hong Kong race's detail (runner keys, results, fixed odds).
Writes nothing. Run from the AU runner (tab_hk_probe.yml)."""
import json
from datetime import date, timedelta

import tab_results_poller as tp


def keys(o):
    return sorted(o.keys()) if isinstance(o, dict) else type(o).__name__


def main():
    days = [date.today().isoformat(), (date.today() - timedelta(days=1)).isoformat()]
    hk = []
    seen = set()
    for d in days:
        for j in tp.TAB_JURISDICTIONS:
            try:
                p = tp.get(tp.MEETINGS.format(date=d), {"jurisdiction": j}, timeout=30)
            except Exception as e:
                print(f"{d} {j}: {type(e).__name__} {e}", flush=True)
                continue
            for m in p.get("meetings", []):
                if m.get("raceType") != tp.RACE_TYPE or m.get("location") in tp.AU_STATES:
                    continue
                k = (d, m.get("meetingName"))
                if k in seen:
                    continue
                seen.add(k)
                races = m.get("races") or []
                is_hk = any(t in (str(m.get("meetingName")) + str(m.get("location"))).upper() for t in ("HAPPY", "SHA TIN", "HONG", "HK"))
                print(f"{d} [{j}] {m.get('meetingName')!r} location={m.get('location')!r} mnemonic={m.get('venueMnemonic')!r} races={len(races)}"
                      f"{'  <-- HONG KONG?' if is_hk else ''}", flush=True)
                if is_hk:
                    hk.append((d, m))
    if not hk:
        print("\nNo Hong Kong meeting found in today's or yesterday's lists under any jurisdiction.", flush=True)
        return
    d, m = hk[0]
    print("\n=== HK meeting top-level keys ===\n", keys(m), flush=True)
    print({k: v for k, v in m.items() if k not in ("races", "_links")}, flush=True)
    rc = (m.get("races") or [{}])[0]
    print("\n=== first race stub keys ===\n", keys(rc), flush=True)
    print({k: (v if not isinstance(v, (dict, list)) else f"<{type(v).__name__}>") for k, v in rc.items()}, flush=True)
    for rc in m.get("races") or []:
        if rc.get("results"):
            print(f"\nrace {rc.get('raceNumber')} status={rc.get('raceStatus')} results={rc.get('results')}", flush=True)
            break
    for j in tp.TAB_JURISDICTIONS:
        try:
            det = tp.get(tp.RACE_DETAIL.format(date=d, venue_mnemonic=m.get("venueMnemonic"), race_no=(m.get("races") or [{}])[0].get("raceNumber")),
                         {"jurisdiction": j}, timeout=30)
        except Exception as e:
            print(f"detail via {j}: {type(e).__name__} {e}", flush=True)
            continue
        print(f"\n=== race detail via jurisdiction {j} ===\n", keys(det), flush=True)
        rn = det.get("runners") or []
        print("runners:", len(rn), "keys:", keys(rn[0]) if rn else None, flush=True)
        if rn:
            print("sample runner:", json.dumps(rn[0], default=str)[:1200], flush=True)
        print("results:", det.get("results"), flush=True)
        break


if __name__ == "__main__":
    main()
