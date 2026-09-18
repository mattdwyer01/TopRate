"""One-off scratch analysis: sweep speedmap_jockey_tracker.py's
CONTESTED_PRICE_FLOOR (currently $6.0) to see whether lowering it recovers
more volume from contested races that currently stay silent. Real user
question, 2026-09-19: "Any more volume opportunities?" -> "Yes" (to
sweeping this first, the cheaper/more direct option offered alongside
checking whether bush meetings are viable at all).

Read-only against toprate_data.json/toprate_runners.csv - writes nothing,
never touches tracker_high_volume.csv/tracker_low_volume.csv or any
production file.

Unlike GAP_MAX/JW_FLOOR/JW_RELATIVE_TOP_PCT/PFM_A_FLOOR, this constant
does NOT affect which pool (a_pool/b_pool) a runner lands in - it only
decides, for a race ALREADY established as contested (2+ pool members,
solo-only already failed), whether that contested group fires on all of
them or stays silent. Since it can't change a race's solo-vs-contested
classification, a plain monkey-patch of the real build_candidates() -
same technique as wpr_tracker_gap_sweep.py - is faithful here (no
population-level reimplementation needed, unlike the GAP_MAX/JW_FLOOR/
PFM_A_FLOOR sweeps whose parameters DO affect pool membership).
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
        "win_pct": round(100 * wins / len(resulted), 1),
        "flat_roi_pct": round(100 * (flat_returned - flat_staked) / flat_staked, 1),
        "prop_roi_pct": round(100 * (prop_returned - prop_staked) / prop_staked, 1),
    }


def fmt(r):
    if r is None:
        return "no results"
    return f"n={r['n']:>4} win%={r['win_pct']:>5} flatROI={r['flat_roi_pct']:>+6}% propROI={r['prop_roi_pct']:>+6}%"


def main():
    with open(sjt.DATA_JSON) as f:
        data = json.load(f)
    pfm_rank_by_rid, pfm_score_by_rid = sjt._load_pfm_lookup()
    bush_keys = sjt._bush_meeting_keys(data)
    dates = sorted({r.get("date") for r in data.get("RACES", []) if r.get("date") and r.get("date") <= TODAY})
    print(f"Backtest window: {dates[0]} to {dates[-1]} ({len(dates)} dates, today={TODAY})")

    original_floor = sjt.CONTESTED_PRICE_FLOOR
    try:
        for floor in [None, 3.0, 4.0, 5.0, 6.0, 8.0, 10.0]:
            sjt.CONTESTED_PRICE_FLOOR = floor if floor is not None else -1.0  # -1: every price clears it (floor disabled)
            picks_a, picks_b = [], []
            for d in dates:
                for r, u, extra in sjt.build_candidates(data, pfm_rank_by_rid, pfm_score_by_rid, d, bush_keys):
                    f_pos = u.get("f")
                    won = u.get("won")
                    resulted = f_pos is not None or won is not None
                    price_final = u.get("sp") if u.get("sp") is not None else extra["price"]
                    row = {"resulted": resulted, "won": (won == 1), "price_final": price_final}
                    if extra["include_in_a"]:
                        picks_a.append(row)
                    if extra["include_in_b"]:
                        picks_b.append(row)
            label = f"floor={'disabled' if floor is None else floor}"
            r = {"A": summarize(picks_a), "B": summarize(picks_b)}
            print(f"{label:<16} A: {fmt(r['A'])}   B: {fmt(r['B'])}")
    finally:
        sjt.CONTESTED_PRICE_FLOOR = original_floor  # restore, in case anything else in-process reads it


if __name__ == "__main__":
    main()
