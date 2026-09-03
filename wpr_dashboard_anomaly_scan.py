"""
wpr_dashboard_anomaly_scan.py - broad sanity sweep of the live toprate_
data.json payload, looking for other systematic prediction problems the
same way the Autumn Glow case surfaced the base-tier hinge bug and the
Hot/Fast skew surfaced the race-speed calibration bug.

Checks:
  1. Biggest predicted-vs-actual misses among resulted runners - any
     concentration by venue/going/distance/class would suggest a
     systematic issue, not just normal variance.
  2. Implausible raw values: negative/absurd base, confidence outside
     0-100, price <= 0, edge outside a sane range.
  3. Base vs raw-input sanity: does the calibrated base ever land WAY
     outside the range spanned by its own inputs (the same shape of bug
     as Autumn Glow), for the CURRENT live payload specifically.
  4. rs_label/edge coverage - anything unexpectedly null/missing at scale.

NO EM DASHES policy: hyphens only in this file.
"""
import json
from collections import Counter

import numpy as np

DATA_PATH = "toprate_data.json"


def run():
    print("Loading toprate_data.json...")
    data = json.load(open(DATA_PATH))
    races = data["RACES"]
    print(f"{len(races):,} races")

    rows = []
    for r in races:
        for run in (r.get("runners") or []):
            rows.append({
                "race_id": r.get("race_id"),
                "date": r.get("date"),
                "venue": r.get("venue"),
                "going": r.get("going"),
                "distance": r.get("distance"),
                "rs_label": r.get("rs_label"),
                "horse": run.get("h"),
                "pred": run.get("wpjp"),
                "base": run.get("wpjb"),
                "adj": run.get("wpjadj"),
                "actual": run.get("wpja"),
                "conf": run.get("wpjc"),
                "won": run.get("won"),
                "finish": run.get("f"),
                "price_fixed": run.get("fx"),
                "price_sp": run.get("sp"),
                "edge": run.get("wpje"),
                "wpr_nett": run.get("w"),
                "scratched": run.get("scr"),
            })

    print(f"{len(rows):,} runner rows")

    resulted = [r for r in rows if r["pred"] is not None and r["actual"] is not None and not r["scratched"]]
    print(f"{len(resulted):,} resulted, projected, non-scratched runners")

    for r in resulted:
        r["miss"] = r["actual"] - r["pred"]

    print(f"\n{'='*100}\nTOP 20 BIGGEST MISSES (actual vs predicted)\n{'='*100}")
    worst = sorted(resulted, key=lambda r: abs(r["miss"]), reverse=True)[:20]
    print(f"  {'date':<12} {'venue':<16} {'horse':<22} {'pred':>7} {'actual':>7} {'miss':>7} {'won':>4}")
    for r in worst:
        print(f"  {str(r['date']):<12} {str(r['venue'])[:16]:<16} {str(r['horse'])[:22]:<22} "
              f"{r['pred']:>7.1f} {r['actual']:>7.1f} {r['miss']:>+7.1f} {'Y' if r['won'] else '':>4}")

    print(f"\n{'='*100}\nMISS CONCENTRATION BY VENUE (top 15 by avg abs miss, min 15 runners)\n{'='*100}")
    by_venue = {}
    for r in resulted:
        by_venue.setdefault(r["venue"], []).append(abs(r["miss"]))
    venue_stats = [(v, len(m), np.mean(m)) for v, m in by_venue.items() if len(m) >= 15]
    venue_stats.sort(key=lambda x: -x[2])
    print(f"  {'venue':<20} {'n':>6} {'avg |miss|':>10}")
    for v, n, m in venue_stats[:15]:
        print(f"  {str(v)[:20]:<20} {n:>6} {m:>10.2f}")

    print(f"\n{'='*100}\nIMPLAUSIBLE RAW VALUES\n{'='*100}")
    bad_conf = [r for r in rows if r["conf"] is not None and not (0 <= r["conf"] <= 100)]
    print(f"  confidence outside [0,100]: {len(bad_conf)}")
    for r in bad_conf[:10]:
        print(f"    {r['horse']} conf={r['conf']}")

    bad_price = [r for r in rows if (r["price_fixed"] is not None and r["price_fixed"] <= 0)
                 or (r["price_sp"] is not None and r["price_sp"] <= 0)]
    print(f"  price <= 0: {len(bad_price)}")

    bad_edge = [r for r in rows if r["edge"] is not None and abs(r["edge"]) > 1]
    print(f"  |edge| > 1 (should be a probability difference, max magnitude 1): {len(bad_edge)}")
    for r in bad_edge[:10]:
        print(f"    {r['horse']} edge={r['edge']}")

    neg_base = [r for r in rows if r["base"] is not None and r["base"] < 0]
    print(f"  negative base: {len(neg_base)}")

    extreme_base = [r for r in rows if r["base"] is not None and (r["base"] < 20 or r["base"] > 130)]
    print(f"  base outside [20,130] (implausible WPR scale): {len(extreme_base)}")
    for r in extreme_base[:10]:
        print(f"    {r['horse']} base={r['base']} wpr_nett={r['wpr_nett']}")

    print(f"\n{'='*100}\nBASE VS RAW-INPUT SANITY (base far outside its own wpr_nett, the Autumn Glow shape of bug)\n{'='*100}")
    gap_rows = [r for r in rows if r["base"] is not None and r["wpr_nett"] is not None]
    for r in gap_rows:
        r["base_vs_nett_gap"] = r["base"] - r["wpr_nett"]
    worst_gap = sorted(gap_rows, key=lambda r: abs(r["base_vs_nett_gap"]), reverse=True)[:15]
    print(f"  {'date':<12} {'horse':<22} {'wpr_nett':>9} {'base':>7} {'gap':>7}")
    for r in worst_gap:
        print(f"  {str(r['date']):<12} {str(r['horse'])[:22]:<22} {r['wpr_nett']:>9.1f} "
              f"{r['base']:>7.1f} {r['base_vs_nett_gap']:>+7.1f}")

    print(f"\n{'='*100}\nCOVERAGE\n{'='*100}")
    n_rows = len(rows)
    for field in ["pred", "base", "conf", "edge", "rs_label"]:
        missing = sum(1 for r in rows if r.get(field) is None)
        print(f"  {field}: {missing:,} / {n_rows:,} missing ({missing/n_rows*100:.1f}%)")


if __name__ == "__main__":
    run()
