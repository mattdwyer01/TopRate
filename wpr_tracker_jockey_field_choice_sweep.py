"""One-off scratch analysis: does ranking jockeys by TopRate's own composite
jockey_rating (jrt, ~50-100 scale) work better than the currently-shipped
jockey_win_pct_90d (jw, raw win%) for the tracker's race-relative rank rule?
Real user question, 2026-09-19: "Is it better to rank jockeys on win strike
rate, or toprate jockey rating?"

Read-only against toprate_data.json/toprate_runners.csv - writes nothing,
never touches tracker_high_volume.csv/tracker_low_volume.csv or any
production file. Same re-implementation approach as
wpr_tracker_jockey_relative_rank_sweep.py (a rule-SHAPE/field change can't
be monkey-patched the way a plain constant sweep could).

Relevant prior finding, NOT the same question but adjacent: wpr_projection.
py's own "own_jockey" experiment (Aug 2026) - using jockey_rating applied
retroactively as an own-history upgrade/downgrade term in the WPR
projection itself - measurably WORSENED held-out MAE (+0.12) despite good
coverage. That was predicting a HORSE's rating from a JOCKEY change, a
different question from this one (ranking jockeys against each other
within a single race) - not conclusive here, but worth knowing going in.

jrt's distribution (checked before running this): min 50.2, p10 76.4,
p25 79.4, median 82.7, p75 86.8, p90 89.9, max 100.0 - a compressed
50-100 composite scale, not a raw percentage like jw (median 10.0).
"""
import json
from datetime import date

import speedmap_jockey_tracker as sjt

TODAY = date.today().isoformat()
GAP_MAX = 5.0


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


def run_one(data, pfm_rank_by_rid, pfm_score_by_rid, dates, bush_keys, field_key, floor, top_pct):
    """field_key: 'jw' or 'jrt'. Re-implements build_candidates()'s race
    loop with the ranking/floor field swapped - everything else (speed_map
    tag, GAP_MAX, solo-only, price floor, contested exception, B's rating
    agreement) matches production exactly. JW_STARTS_MIN deliberately
    NOT applied here - isolating the ranking-field question alone."""
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
            field_vals = [u.get(field_key) for u in runners if u.get(field_key) is not None]

            trr_vals = [u.get("trr") for u in runners]
            wpr_vals = [u.get("wpjp") for u in runners]
            top_wpr = max((v for v in wpr_vals if v is not None), default=None)
            cutoff_rank = max(1, round(len(field_vals) * top_pct / 100))

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
                val = u.get(field_key)
                if val is None or val <= floor:
                    continue
                rank = sjt._rank_desc(val, field_vals)
                if rank is None or rank > cutoff_rank:
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

    print("\n=== jw (win%), top 10%, floor 10 - CURRENT PRODUCTION ===")
    r = run_one(data, pfm_rank_by_rid, pfm_score_by_rid, dates, bush_keys, "jw", 10.0, 10)
    print("  A:", r["A"])
    print("  B:", r["B"])

    print("\n=== jrt (jockey_rating), various top X% / floor combos ===")
    for top_pct in [10, 15, 20]:
        for floor in [0, 75, 80]:
            r = run_one(data, pfm_rank_by_rid, pfm_score_by_rid, dates, bush_keys, "jrt", floor, top_pct)
            print(f"top {top_pct}%, floor {floor}:")
            print("  A:", r["A"])
            print("  B:", r["B"])


if __name__ == "__main__":
    main()
