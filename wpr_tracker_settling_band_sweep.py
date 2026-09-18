"""One-off scratch analysis: does restricting the tracker's shared base
rule to a subset of `psBand` (predictedSettlingBand: Leader/On-pace/
Midfield/Back, a runner's ABSOLUTE projected running position) improve
win rate at the cost of volume? Real user question, 2026-09-19: "What
about projected settling category?" -> "Additional restriction".

`psBand` is a DIFFERENT signal from the tracker's existing speed_map
demeaned tag (favoured/neutral/unfavoured - a runner's pace advantage
RELATIVE to this race's own field mean), currently unused by the tracker
rule entirely. Coverage in the live payload: Midfield 47.9%, On-pace
28.8%, Back 18.8%, Leader 2.2%, null 2.3% (15,074 non-scratched runners
checked).

Read-only against toprate_data.json/toprate_runners.csv - writes nothing.
Re-implements build_candidates()'s race loop with the psBand check added
INSIDE the shared race_qualifiers loop (same population-level precedent
as every prior sweep this session that could change pool membership -
this one affects BOTH a_pool and b_pool, since it sits in the shared
base rule alongside speed_map/gap/jw, not in either tracker's own extra
condition). A null psBand FAILS this deliberately (same convention as
PFM_A_FLOOR: a genuine backtested restriction, not a thin-sample guard
like JW_STARTS_MIN, so there's no "unknown passes" precedent here).
"""
import json
from datetime import date

import speedmap_jockey_tracker as sjt

TODAY = date.today().isoformat()
GAP_MAX = sjt.GAP_MAX
JW_FLOOR = sjt.JW_FLOOR
JW_RELATIVE_TOP_PCT = sjt.JW_RELATIVE_TOP_PCT
JW_STARTS_MIN = sjt.JW_STARTS_MIN
PFM_A_FLOOR = sjt.PFM_A_FLOOR
PRICE_MIN = sjt.PRICE_MIN
CONTESTED_PRICE_FLOOR = sjt.CONTESTED_PRICE_FLOOR


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


def run_one(data, pfm_rank_by_rid, pfm_score_by_rid, dates, bush_keys, allowed_bands):
    """allowed_bands: None (no restriction, current production) or a set
    of psBand strings a runner must be in to qualify at all."""
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

            trr_vals = [u.get("trr") for u in runners]
            wpr_vals = [u.get("wpjp") for u in runners]
            top_wpr = max((v for v in wpr_vals if v is not None), default=None)
            jw_field = [u.get("jw") for u in runners if u.get("jw") is not None]
            jw_cutoff_rank = max(1, round(len(jw_field) * JW_RELATIVE_TOP_PCT / 100))

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
                if jw is None or jw <= JW_FLOOR:
                    continue
                if sjt._rank_desc(jw, jw_field) > jw_cutoff_rank:
                    continue
                jw_starts = u.get("jwN")
                if jw_starts is not None and jw_starts < JW_STARTS_MIN:
                    continue
                # New restriction being tested - a null psBand fails,
                # same as an out-of-set band (see module docstring).
                if allowed_bands is not None and u.get("psBand") not in allowed_bands:
                    continue
                price = u.get("sp") if u.get("sp") is not None else u.get("fx")
                race_qualifiers.append((u, price))

            if not race_qualifiers:
                continue

            info_by_rid = {}
            a_pool = []
            b_pool = []
            for (u, price) in race_qualifiers:
                rid = str(u.get("rid", ""))
                trr_rank = sjt._rank_desc(u.get("trr"), trr_vals)
                pfm_rank = pfm_rank_by_rid.get(rid)
                info_by_rid[rid] = (u, price, trr_rank, pfm_rank)
                pfm_score = pfm_score_by_rid.get(rid)
                if pfm_score is not None and pfm_score >= PFM_A_FLOOR:
                    a_pool.append(rid)
                if trr_rank == 1 and pfm_rank == 1:
                    b_pool.append(rid)

            def resolve(pool):
                if len(pool) == 1:
                    rid = pool[0]
                    price = info_by_rid[rid][1]
                    if price is not None and price >= PRICE_MIN:
                        return {rid}
                    return set()
                if len(pool) > 1:
                    prices = [info_by_rid[rid][1] for rid in pool]
                    if all(p is not None and p > CONTESTED_PRICE_FLOOR for p in prices):
                        return set(pool)
                return set()

            include_a_rids = resolve(a_pool)
            include_b_rids = resolve(b_pool)

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

    configs = [
        ("no restriction (current production)", None),
        ("Leader only", {"Leader"}),
        ("Leader + On-pace", {"Leader", "On-pace"}),
        ("Leader + On-pace + Midfield (excl. Back)", {"Leader", "On-pace", "Midfield"}),
        ("On-pace only", {"On-pace"}),
        ("On-pace + Midfield", {"On-pace", "Midfield"}),
        ("Midfield only", {"Midfield"}),
        ("Back only", {"Back"}),
    ]
    for label, allowed in configs:
        r = run_one(data, pfm_rank_by_rid, pfm_score_by_rid, dates, bush_keys, allowed)
        print(f"{label:<42} A: {fmt(r['A'])}   B: {fmt(r['B'])}")


if __name__ == "__main__":
    main()
