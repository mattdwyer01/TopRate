"""One-off scratch analysis: should Tracker A (high volume) get a minimum
ABSOLUTE floor on TopRate rating (trr) or form factor (pfm_score), on top
of its existing rule (speed_map tag, GAP_MAX, race-relative jockey rank,
JW_STARTS_MIN)? Real user question, 2026-09-19. Tracker B already has its
own, race-RELATIVE version of this idea (must be #1 in-race by both trr
and pfm_score) - this tests an ABSOLUTE floor for A instead, since A
deliberately has no rating-agreement requirement at all today.

Read-only against toprate_data.json/toprate_runners.csv - writes nothing.
Re-implements build_candidates()'s race loop with the new floor check
added INSIDE the qualifying loop (not a post-filter on its output) -
removing a candidate can change whether a race resolves as solo, which a
simple post-filter would miss (the exact class of bug already found once
this session when a threshold change reshuffled solo-vs-contested
races - see CLAUDE.md's JW_MIN entry).

Checked distributions among Tracker A's CURRENT qualifiers before picking
floor candidates: trr min 91.92, p10 95.99, p25 97.33, median 98.61, p75
99.49, max 100.0 (already compressed near the top - GAP_MAX=5 already
implicitly filters for "close to this race's own top rating", which
correlates with a generally high absolute trr too); pfm_score min 7, p10
24, p25 41, median 65, p75 96, max 100 (genuinely wide spread, real room
for a floor to bite).
"""
import json
from datetime import date

import speedmap_jockey_tracker as sjt

TODAY = date.today().isoformat()
GAP_MAX = 5.0
JW_FLOOR = 10.0
JW_RELATIVE_TOP_PCT = 10
JW_STARTS_MIN = 25


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


def run_one(data, pfm_rank_by_rid, pfm_score_by_rid, dates, bush_keys, trr_floor, pfm_floor):
    """Only affects Tracker A - Tracker B keeps its existing, unrelated
    rating-agreement mechanism untouched, computed exactly as production
    does. trr_floor/pfm_floor of None means no floor (current production
    behaviour for A)."""
    picks_a, picks_b = [], []
    for d in dates:
        for r in data.get("RACES", []):
            if r.get("date") != d:
                continue
            if (r.get("date"), r.get("venue")) in bush_keys:
                continue
            runners = [u for u in r.get("runners", []) if not u.get("scr")]
            valid = []
            for u in runners:
                cb = u.get("wpjcb") or {}
                sm = cb.get("speed_map")
                if sm is not None:
                    valid.append((u, sm))
            if len(valid) < 2:
                continue
            race_mean = sum(sm for _, sm in valid) / len(valid)
            jw_field = [u.get("jw") for u in runners if u.get("jw") is not None]
            jw_cutoff_rank = max(1, round(len(jw_field) * JW_RELATIVE_TOP_PCT / 100))

            trr_vals = [u.get("trr") for u in runners]
            wpr_vals = [u.get("wpjp") for u in runners]
            top_wpr = max((v for v in wpr_vals if v is not None), default=None)

            race_qualifiers_a = []
            race_qualifiers_b = []
            for u, sm in valid:
                demeaned = sm - race_mean
                if demeaned <= -sjt.DEMEAN_THRESHOLD:
                    tag = "unfavoured"
                elif demeaned >= sjt.DEMEAN_THRESHOLD:
                    tag = "favoured"
                else:
                    tag = "neutral"
                if tag not in sjt.TAGS:
                    continue
                wpjp = u.get("wpjp")
                gap = (top_wpr - wpjp) if (wpjp is not None and top_wpr is not None) else None
                if gap is None or gap > GAP_MAX:
                    continue
                jw = u.get("jw")
                if jw is None or jw <= JW_FLOOR:
                    continue
                if sjt._rank_desc(jw, jw_field) > jw_cutoff_rank:
                    continue
                jw_starts = u.get("jwN")
                if jw_starts is not None and jw_starts < JW_STARTS_MIN:
                    continue
                price = u.get("sp") if u.get("sp") is not None else u.get("fx")

                rid = str(u.get("rid", ""))
                trr_rank = sjt._rank_desc(u.get("trr"), trr_vals)
                pfm_rank = pfm_rank_by_rid.get(rid)

                # Tracker B: unaffected, exactly as production.
                if trr_rank == 1 and pfm_rank == 1:
                    race_qualifiers_b.append((u, price))

                # Tracker A: apply the new absolute floor(s) being tested.
                # Written include-style (not "exclude if val is None or val <
                # floor") deliberately: pfm_score_by_rid can hold NaN (a
                # pandas artifact, not None) for a missing score, and NaN
                # fails BOTH "is None" and "< floor" comparisons, so an
                # exclude-style check silently lets it through - found via a
                # real discrepancy against production's own (correct,
                # include-style) check after this script had already been
                # used to pick PFM_A_FLOOR=65 - re-verified afterward that
                # the conclusion still held once fixed (see CLAUDE.md).
                trr_val = u.get("trr")
                pfm_val = pfm_score_by_rid.get(rid)
                if trr_floor is not None and not (trr_val is not None and trr_val >= trr_floor):
                    continue
                if pfm_floor is not None and not (pfm_val is not None and pfm_val >= pfm_floor):
                    continue
                race_qualifiers_a.append((u, price))

            def resolve(qualifiers):
                if len(qualifiers) == 1:
                    u, price = qualifiers[0]
                    if price is not None and price >= sjt.PRICE_MIN:
                        return {str(u.get("rid", ""))}
                    return set()
                if len(qualifiers) > 1:
                    prices = [p for _, p in qualifiers]
                    if all(p is not None and p > sjt.CONTESTED_PRICE_FLOOR for p in prices):
                        return {str(u.get("rid", "")) for u, _ in qualifiers}
                return set()

            include_a_rids = resolve(race_qualifiers_a)
            include_b_rids = resolve(race_qualifiers_b)
            info = {str(u.get("rid", "")): (u, price) for u, price in race_qualifiers_a + race_qualifiers_b}

            for rid in include_a_rids | include_b_rids:
                u, price = info[rid]
                f_pos = u.get("f")
                won = u.get("won")
                resulted = f_pos is not None or won is not None
                price_final = u.get("sp") if u.get("sp") is not None else price
                row = {"resulted": resulted, "won": (won == 1), "price_final": price_final}
                if rid in include_a_rids:
                    picks_a.append(row)
                if rid in include_b_rids:
                    picks_b.append(row)
    return {"A": summarize(picks_a), "B": summarize(picks_b)}


def main():
    with open(sjt.DATA_JSON) as f:
        data = json.load(f)
    pfm_rank_by_rid, pfm_score_by_rid = sjt._load_pfm_lookup()
    bush_keys = sjt._bush_meeting_keys(data)
    dates = sorted({r.get("date") for r in data.get("RACES", []) if r.get("date") and r.get("date") <= TODAY})
    print(f"Backtest window: {dates[0]} to {dates[-1]} ({len(dates)} dates, today={TODAY})")

    print("\n=== Baseline: no rating floor on A (current production) ===")
    r = run_one(data, pfm_rank_by_rid, pfm_score_by_rid, dates, bush_keys, None, None)
    print("  A:", r["A"], " B:", r["B"])

    print("\n=== TopRate rating (trr) floor sweep, A only ===")
    for floor in [90, 95, 97, 98, 99]:
        r = run_one(data, pfm_rank_by_rid, pfm_score_by_rid, dates, bush_keys, floor, None)
        print(f"trr >= {floor}: A: {r['A']}")

    print("\n=== Form factor (pfm_score) floor sweep, A only ===")
    for floor in [20, 40, 60, 70, 80, 90]:
        r = run_one(data, pfm_rank_by_rid, pfm_score_by_rid, dates, bush_keys, None, floor)
        print(f"pfm >= {floor}: A: {r['A']}")


if __name__ == "__main__":
    main()
