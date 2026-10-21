"""Read-only: what TAB carries for Hong Kong races (21 Oct 2026): results, scratchings and Sky replay fields on every race stub of today's Hong Kong
meeting (location HKG, found with the first version of this probe). Writes nothing. Run from the AU runner (tab_hk_probe.yml)."""
import json
from datetime import date

import tab_results_poller as tp


def main():
    d = date.today().isoformat()
    seen = False
    for j in tp.TAB_JURISDICTIONS:
        try:
            p = tp.get(tp.MEETINGS.format(date=d), {"jurisdiction": j}, timeout=30)
        except Exception as e:
            print(f"{d} {j}: {type(e).__name__} {e}", flush=True)
            continue
        for m in p.get("meetings", []):
            if m.get("raceType") != tp.RACE_TYPE or m.get("location") != "HKG":
                continue
            seen = True
            print(f"{d} [{j}] {m.get('meetingName')!r} mnemonic={m.get('venueMnemonic')!r} trackCondition={m.get('trackCondition')!r} "
                  f"rail={m.get('railPosition')!r}", flush=True)
            for rc in m.get("races") or []:
                print(f"  R{rc.get('raceNumber')} status={rc.get('raceStatus')} start={rc.get('raceStartTime')} "
                      f"results={json.dumps(rc.get('results'))[:200]} scratchings={json.dumps(rc.get('scratchings'))[:300]}", flush=True)
                print(f"     skyRacing={json.dumps(rc.get('skyRacing'))[:400]}", flush=True)
            break
        if seen:
            break
    if not seen:
        print("No Hong Kong meeting in today's list.", flush=True)


if __name__ == "__main__":
    main()
