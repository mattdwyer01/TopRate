"""One-off scratch analysis: does adding a minimum jockey_starts_90d floor
(on top of the tracker's existing JW_MIN win% floor) further improve strike
rate, by filtering out a jockey whose win% looks strong only because it's
built on a handful of rides (e.g. 1-of-2 = 50%)? Real user request,
2026-09-19 ("do a backtest on min jockey starts") - the exact follow-up
CLAUDE.md's jockey_starts_90d entry already flagged as blocked pending
"enough freshly-captured rows" to mean anything.

Read-only against toprate_data.json/toprate_runners.csv - writes nothing,
never touches tracker_high_volume.csv/tracker_low_volume.csv or any
production file. Reuses speedmap_jockey_tracker.build_candidates()
unmodified (current production GAP_MAX=5/JW_MIN=20 rule) and post-filters
its own output by each candidate's real jwN (jockey_starts_90d) value -
not a re-implementation of the qualifying rule itself.

CRITICAL CAVEAT, checked before running anything: jockey_starts_90d
(payload key "jwN") was only fixed to actually populate from 2026-09-17
onward (see CLAUDE.md's jockey_merit entry) - every older row in the
25-30 day toprate_data.json window is null. Of RESULTED (already-run)
dates as of today, only 2026-09-17 and 2026-09-18 have any jwN data at
all. This means every number below is built on at most 2 days of real
data - nowhere near enough to trust, only enough to see whether it's
even worth re-checking once more days accumulate.
"""
import json
from datetime import date

import speedmap_jockey_tracker as sjt

TODAY = date.today().isoformat()


def stake_for(price: float, return_units: float = 4.0) -> float:
    return return_units / price


def summarize(picks: list) -> dict | None:
    resulted = [p for p in picks if p["resulted"] and p["price_final"] is not None]
    if not resulted:
        return None
    wins = sum(1 for p in resulted if p["won"])
    flat_staked = len(resulted)
    flat_returned = sum(p["price_final"] for p in resulted if p["won"])
    prop_staked = sum(stake_for(p["price_final"]) for p in resulted)
    prop_returned = sum(4.0 for p in resulted if p["won"])
    return {
        "n": len(resulted),
        "win_pct": 100 * wins / len(resulted),
        "flat_roi_pct": 100 * (flat_returned - flat_staked) / flat_staked,
        "prop_roi_pct": 100 * (prop_returned - prop_staked) / prop_staked,
    }


def main():
    with open(sjt.DATA_JSON) as f:
        data = json.load(f)
    pfm_rank_by_rid, pfm_score_by_rid = sjt._load_pfm_lookup()
    bush_keys = sjt._bush_meeting_keys(data)
    dates = sorted({r.get("date") for r in data.get("RACES", []) if r.get("date") and r.get("date") <= TODAY})

    # How many candidates even carry real jwN data, before any floor.
    n_with_jwn = {"A": 0, "B": 0}
    n_total = {"A": 0, "B": 0}
    picks_by_floor: dict[float, dict[str, list]] = {}
    floors = [0, 5, 10, 15, 20]
    for floor in floors:
        picks_by_floor[floor] = {"A": [], "B": []}

    for d in dates:
        for r, u, extra in sjt.build_candidates(data, pfm_rank_by_rid, pfm_score_by_rid, d, bush_keys):
            f_pos = u.get("f")
            won = u.get("won")
            resulted = f_pos is not None or won is not None
            price_final = u.get("sp") if u.get("sp") is not None else extra["price"]
            starts = u.get("jwN")
            row = {"resulted": resulted, "won": (won == 1), "price_final": price_final, "starts": starts}
            for key in ("A", "B"):
                included = extra["include_in_a"] if key == "A" else extra["include_in_b"]
                if not included:
                    continue
                n_total[key] += 1
                if starts is not None:
                    n_with_jwn[key] += 1
                for floor in floors:
                    if floor == 0 or (starts is not None and starts >= floor):
                        picks_by_floor[floor][key].append(row)

    print(f"Backtest window: {dates[0]} to {dates[-1]} ({len(dates)} dates, today={TODAY})")
    print(f"Candidates with real jwN (jockey_starts_90d) data: "
          f"A {n_with_jwn['A']}/{n_total['A']}, B {n_with_jwn['B']}/{n_total['B']}")
    print("(jwN only populates from 2026-09-17 onward - see this script's own docstring)")

    for key, name in (("A", "High volume (Tracker A)"), ("B", "Low volume (Tracker B)")):
        print(f"\n=== {name}: jockey_starts_90d floor sweep (on top of current GAP_MAX=5/JW_MIN=20) ===")
        for floor in floors:
            s = summarize(picks_by_floor[floor][key])
            label = "no floor (baseline)" if floor == 0 else f"starts>={floor}"
            if s is None:
                print(f"  {label}: no resulted picks")
                continue
            print(
                f"  {label}: n={s['n']:4d}  win%={s['win_pct']:5.1f}  "
                f"flatROI%={s['flat_roi_pct']:+6.1f}  propROI%={s['prop_roi_pct']:+6.1f}"
            )


if __name__ == "__main__":
    main()
