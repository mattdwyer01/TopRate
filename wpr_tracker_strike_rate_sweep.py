"""One-off scratch analysis: sweep speedmap_jockey_tracker.py's rule knobs
(GAP_MAX, JW_MIN, TAGS) looking for a real strike-rate improvement over the
current settings (GAP_MAX=4, JW_MIN=14, TAGS=favoured+neutral) - real user
request, 2026-09-19 ("strike rate increase", after being warned this can
pull against ROI). Read-only against toprate_data.json/toprate_runners.csv -
writes nothing, never touches tracker_high_volume.csv/tracker_low_volume.csv
or any production file.

Reuses speedmap_jockey_tracker.build_candidates() itself (monkey-patching
its module-level GAP_MAX/JW_MIN/TAGS before each call) rather than
re-implementing the solo-only/price-floor/contested-exception logic here,
so this can't drift from the real rule.

Caveat: toprate_data.json only holds the live TOPRATE_RACES_WINDOW_DAYS
window (about a month by the time this runs), much smaller than the
n=297/271 the GAP_MAX 6->4 sweep documented in speedmap_jockey_tracker.py's
own comments was run against (a longer, session-long backtest, never
committed). Numbers here are directional, not a replacement for that scale
of sample - and every cell here still needs enough resulted picks (n) to
mean anything; a high win% on n=8 is noise, not a finding.
"""
import json
from datetime import date

import speedmap_jockey_tracker as sjt

TODAY = date.today().isoformat()

DEFAULT_GAP_MAX = sjt.GAP_MAX
DEFAULT_JW_MIN = sjt.JW_MIN
DEFAULT_TAGS = sjt.TAGS


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


def run_one(data, pfm_rank_by_rid, pfm_score_by_rid, dates, bush_keys, gap_max, jw_min, tags):
    sjt.GAP_MAX = gap_max
    sjt.JW_MIN = jw_min
    sjt.TAGS = tags
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
    return {"A": summarize(picks_a), "B": summarize(picks_b)}


def fmt_row(label, s):
    if s is None:
        return f"  {label}: no resulted picks"
    return (
        f"  {label}: n={s['n']:4d}  win%={s['win_pct']:5.1f}  "
        f"flatROI%={s['flat_roi_pct']:+6.1f}  propROI%={s['prop_roi_pct']:+6.1f}"
    )


def main():
    with open(sjt.DATA_JSON) as f:
        data = json.load(f)
    pfm_rank_by_rid, pfm_score_by_rid = sjt._load_pfm_lookup()
    bush_keys = sjt._bush_meeting_keys(data)
    dates = sorted({r.get("date") for r in data.get("RACES", []) if r.get("date") and r.get("date") <= TODAY})
    print(f"Backtest window: {dates[0]} to {dates[-1]} ({len(dates)} dates, today={TODAY})")

    baseline = run_one(data, pfm_rank_by_rid, pfm_score_by_rid, dates, bush_keys,
                        DEFAULT_GAP_MAX, DEFAULT_JW_MIN, DEFAULT_TAGS)
    print("\n=== Baseline (current production settings) ===")
    print(fmt_row("A (high volume)", baseline["A"]))
    print(fmt_row("B (low volume)", baseline["B"]))

    print("\n=== Sweep 1: GAP_MAX (tighter = fewer, more clear-favourite-only picks) ===")
    for gap in [1.5, 2.0, 2.5, 3.0, 3.5, 4.0]:
        r = run_one(data, pfm_rank_by_rid, pfm_score_by_rid, dates, bush_keys, gap, DEFAULT_JW_MIN, DEFAULT_TAGS)
        print(f"GAP_MAX={gap}")
        print(fmt_row("  A", r["A"]))
        print(fmt_row("  B", r["B"]))

    print("\n=== Sweep 2: JW_MIN (higher = require a stronger jockey) ===")
    for jw in [14.0, 16.0, 18.0, 20.0, 22.0, 25.0, 30.0]:
        r = run_one(data, pfm_rank_by_rid, pfm_score_by_rid, dates, bush_keys, DEFAULT_GAP_MAX, jw, DEFAULT_TAGS)
        print(f"JW_MIN={jw}")
        print(fmt_row("  A", r["A"]))
        print(fmt_row("  B", r["B"]))

    print("\n=== Sweep 3: TAGS favoured-only (drop 'neutral' speed-map tag) ===")
    r = run_one(data, pfm_rank_by_rid, pfm_score_by_rid, dates, bush_keys,
                DEFAULT_GAP_MAX, DEFAULT_JW_MIN, ("favoured",))
    print("TAGS=favoured-only")
    print(fmt_row("  A", r["A"]))
    print(fmt_row("  B", r["B"]))

    print("\n=== Sweep 4: best single-lever combo (tightest GAP_MAX + JW_MIN together) ===")
    for gap in [2.0, 2.5, 3.0]:
        for jw in [18.0, 22.0, 25.0]:
            r = run_one(data, pfm_rank_by_rid, pfm_score_by_rid, dates, bush_keys, gap, jw, DEFAULT_TAGS)
            print(f"GAP_MAX={gap}, JW_MIN={jw}")
            print(fmt_row("  A", r["A"]))
            print(fmt_row("  B", r["B"]))

    sjt.GAP_MAX = DEFAULT_GAP_MAX
    sjt.JW_MIN = DEFAULT_JW_MIN
    sjt.TAGS = DEFAULT_TAGS


if __name__ == "__main__":
    main()
