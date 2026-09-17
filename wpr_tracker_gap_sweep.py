"""One-off scratch analysis: sweep speedmap_jockey_tracker.py's GAP_MAX
(currently 4.0) to see what a change to 5.0 (or other values) would do to
each tracker's pick volume, win rate, and ROI. Read-only against
toprate_data.json/toprate_runners.csv - writes nothing, never touches
tracker_high_volume.csv/tracker_low_volume.csv or any production file.

Reuses speedmap_jockey_tracker.build_candidates() itself (monkey-patching
its module-level GAP_MAX before each call) rather than re-implementing the
solo-only/price-floor/contested-exception logic here, so this can't drift
from the real rule.

Caveat: toprate_data.json only holds the live TOPRATE_RACES_WINDOW_DAYS
window (25 days), much smaller than the n=297/271 the GAP_MAX 6->4 sweep
documented in speedmap_jockey_tracker.py's own comments was run against
(a longer, session-long backtest, never committed). Numbers here are
directional, not a replacement for that scale of sample.
"""
import json
from datetime import date

import pandas as pd

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


def run_sweep(gap_values):
    with open(sjt.DATA_JSON) as f:
        data = json.load(f)
    pfm_rank_by_rid, pfm_score_by_rid = sjt._load_pfm_lookup()
    bush_keys = sjt._bush_meeting_keys(data)

    dates = sorted({r.get("date") for r in data.get("RACES", []) if r.get("date") and r.get("date") <= TODAY})
    print(f"Backtest window: {dates[0]} to {dates[-1]} ({len(dates)} dates, today={TODAY})")

    results = {}
    for gap in gap_values:
        sjt.GAP_MAX = gap
        picks_a, picks_b = [], []
        for d in dates:
            for r, u, extra in sjt.build_candidates(data, pfm_rank_by_rid, pfm_score_by_rid, d, bush_keys):
                f_pos = u.get("f")
                won = u.get("won")
                resulted = f_pos is not None or won is not None
                price_final = u.get("sp") if u.get("sp") is not None else extra["price"]
                row = {
                    "resulted": resulted,
                    "won": (won == 1),
                    "price_final": price_final,
                }
                if extra["include_in_a"]:
                    picks_a.append(row)
                if extra["include_in_b"]:
                    picks_b.append(row)
        results[gap] = {"A": summarize(picks_a), "B": summarize(picks_b)}
    sjt.GAP_MAX = 4.0  # restore, in case anything else in-process reads it
    return results


if __name__ == "__main__":
    gap_values = [3.0, 4.0, 5.0, 6.0]
    results = run_sweep(gap_values)
    for tracker in ("A", "B"):
        name = "High volume (Tracker A)" if tracker == "A" else "Low volume (Tracker B)"
        print(f"\n=== {name} ===")
        for gap in gap_values:
            s = results[gap][tracker]
            if s is None:
                print(f"  GAP_MAX={gap}: no resulted picks")
                continue
            print(
                f"  GAP_MAX={gap}: n={s['n']:4d}  win%={s['win_pct']:5.1f}  "
                f"flatROI%={s['flat_roi_pct']:+6.1f}  propROI%={s['prop_roi_pct']:+6.1f}"
            )
