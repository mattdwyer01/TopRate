"""Read-only probe of TopRate race pages (6 Nov 2026): for each race id prints whether the page loads, whether it carries a result (raceResult.runners),
its venue, race number, date, rating status and how many runners it has. Used to find why some races never reach data/tr_results.
Environment: TOPRATE_EMAIL, TOPRATE_PASSWORD, TOPRATE_ANON_KEY. Usage: python toprate_result_probe.py 1760592,1829207"""
import os
import sys

import toprate_race_fetch as F


def main():
    ids = [int(x) for x in sys.argv[1].replace(" ", "").split(",") if x]
    session = F.login(os.environ["TOPRATE_EMAIL"], os.environ["TOPRATE_PASSWORD"], os.environ["TOPRATE_ANON_KEY"])
    for rid in ids:
        page, err = F.fetch_race(session, rid)
        if not page:
            print(f"{rid}: NO PAGE ({err})", flush=True)
            continue
        rr = page.get("raceResult") or {}
        rec = page.get("raceRecord") or {}
        meet = rec.get("meetingSummary") or {}
        runners = rr.get("runners") or []
        n_atw = sum(1 for r in runners if r.get("atw") is not None)
        print(f"{rid}: page ok keys={sorted(page)[:8]} venue={meet.get('venue')} date={meet.get('date') or rec.get('date')} race={rr.get('number') or rec.get('number')} "
              f"status={rr.get('wprStatus')} result_runners={len(runners)} with_atw={n_atw} rec_keys={sorted(rec)[:10]}", flush=True)


if __name__ == "__main__":
    main()
