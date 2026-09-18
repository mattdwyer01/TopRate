"""One-off scratch analysis: replace the tracker's absolute jockey_win_pct_90d
floor (JW_MIN) with a RACE-RELATIVE rule instead - "in the top X% of jockey
win% among this race's own field, with an absolute floor so a jockey below
that floor never qualifies even in a race full of weak riders." Real user
proposal, 2026-09-19: "being in the top x% of jockey sr in the race, rather
than 14% and above... floor of at least above 10%".

Read-only against toprate_data.json/toprate_runners.csv - writes nothing,
never touches tracker_high_volume.csv/tracker_low_volume.csv or any
production file. Reuses speedmap_jockey_tracker's own building blocks
(_bush_meeting_keys, _load_pfm_lookup, _rank_desc) but re-implements the
race-loop qualifying check itself with the jw test swapped out, since
build_candidates() has no parameter for this - can't monkey-patch a rule
shape change the way the GAP_MAX/JW_MIN value sweeps could.

Population for "in the race": every non-scratched runner with a real jw
value (not just the ones that already pass speed_map/gap - the whole
point of a race-relative rule is comparing against the WHOLE field's
jockey quality, not an already-filtered subset).
"""
import json
from datetime import date

import speedmap_jockey_tracker as sjt

TODAY = date.today().isoformat()

FLOOR = 10.0  # absolute floor per the user's request - never qualifies below this
GAP_MAX = 5.0  # current production value, held fixed for this sweep


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


def qualifies_relative(jw, jw_field, top_pct):
    """jw_field: list of jw values (non-None) for every runner in the race.
    Top X% by rank, ties counted generously (a tie for the cutoff rank
    still qualifies) - same convention as _rank_desc elsewhere in this
    codebase."""
    if jw is None or jw <= FLOOR:
        return False
    n = len(jw_field)
    rank = 1 + sum(1 for v in jw_field if v > jw)
    cutoff_rank = max(1, round(n * top_pct / 100))
    return rank <= cutoff_rank


def run_one(data, pfm_rank_by_rid, pfm_score_by_rid, dates, bush_keys, jw_rule):
    """jw_rule(jw, jw_field) -> bool. Re-implements build_candidates' race
    loop with only the jw check swapped out - everything else (speed_map
    tag, GAP_MAX, solo-only, price floor, contested exception, B's rating
    agreement) matches production exactly."""
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

            trr_vals = [u.get("trr") for u in runners]
            wpr_vals = [u.get("wpjp") for u in runners]
            top_wpr = max((v for v in wpr_vals if v is not None), default=None)

            race_qualifiers = []
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
                if not jw_rule(jw, jw_field):
                    continue
                price = u.get("sp") if u.get("sp") is not None else u.get("fx")
                race_qualifiers.append((u, price))

            if not race_qualifiers:
                continue

            info_by_rid = {}
            b_pool = []
            for (u, price) in race_qualifiers:
                rid = str(u.get("rid", ""))
                trr_rank = sjt._rank_desc(u.get("trr"), trr_vals)
                pfm_rank = pfm_rank_by_rid.get(rid)
                info_by_rid[rid] = (u, price, trr_rank, pfm_rank)
                if trr_rank == 1 and pfm_rank == 1:
                    b_pool.append(rid)

            solo_a = race_qualifiers[0] if len(race_qualifiers) == 1 else None
            include_a_rids = set()
            if solo_a is not None:
                if solo_a[1] is not None and solo_a[1] >= sjt.PRICE_MIN:
                    include_a_rids = {str(solo_a[0].get("rid", ""))}
            elif len(race_qualifiers) > 1:
                prices = [q[1] for q in race_qualifiers]
                if all(p is not None and p > sjt.CONTESTED_PRICE_FLOOR for p in prices):
                    include_a_rids = {str(q[0].get("rid", "")) for q in race_qualifiers}

            solo_b_rid = b_pool[0] if len(b_pool) == 1 else None
            include_b_rids = set()
            if solo_b_rid is not None:
                if info_by_rid[solo_b_rid][1] is not None and info_by_rid[solo_b_rid][1] >= sjt.PRICE_MIN:
                    include_b_rids = {solo_b_rid}
            elif len(b_pool) > 1:
                prices = [info_by_rid[rid][1] for rid in b_pool]
                if all(p is not None and p > sjt.CONTESTED_PRICE_FLOOR for p in prices):
                    include_b_rids = set(b_pool)

            for rid in include_a_rids | include_b_rids:
                u, price, _, _ = info_by_rid[rid]
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

    # Baseline: current production rule (absolute JW_MIN=14, GAP_MAX=5).
    def absolute_rule(jw, jw_field):
        return jw is not None and jw >= 14.0
    baseline = run_one(data, pfm_rank_by_rid, pfm_score_by_rid, dates, bush_keys, absolute_rule)
    print("\n=== Baseline: absolute JW_MIN=14 (current production) ===")
    for k in ("A", "B"):
        print(f"  {k}: {baseline[k]}")

    print(f"\n=== Relative rule: top X% of jockey win% in the race, floor jw>{FLOOR} ===")
    for top_pct in [10, 15, 20, 25, 30, 40, 50]:
        def rule(jw, jw_field, top_pct=top_pct):
            return qualifies_relative(jw, jw_field, top_pct)
        r = run_one(data, pfm_rank_by_rid, pfm_score_by_rid, dates, bush_keys, rule)
        print(f"top {top_pct}%:")
        print(f"  A: {r['A']}")
        print(f"  B: {r['B']}")


if __name__ == "__main__":
    main()
