"""One-off scratch analysis: combined sweep of PFM_A_FLOOR (Tracker A's
absolute form-factor floor) and JW_RELATIVE_TOP_PCT (the shared race-
relative jockey-win% rank cutoff, feeds both trackers) - real user
question, 2026-09-19: "How to get more volume?" then "Run a combined
sweep on PFM_A_FLOOR and JW_RELATIVE_TOP_PCT".

Read-only against toprate_data.json/toprate_runners.csv - writes nothing.
Re-implements build_candidates()'s race loop with BOTH parameters swept
INSIDE the qualifying loop (not a post-filter on already-resolved output) -
either one can change whether a race resolves as solo vs contested for a
tracker (the same population-level effect already found/documented twice
this session - see CLAUDE.md's JW_MIN and PFM_A_FLOOR entries), so a
post-filter would silently misreport which picks a looser/tighter setting
would actually have produced.

JW_RELATIVE_TOP_PCT widens the shared base-rule population feeding BOTH
trackers (a_pool AND b_pool both derive from race_qualifiers), so unlike
PFM_A_FLOOR (Tracker A only), this axis moves both trackers' volume.
"""
import json
from datetime import date

import speedmap_jockey_tracker as sjt

TODAY = date.today().isoformat()
GAP_MAX = sjt.GAP_MAX
JW_FLOOR = sjt.JW_FLOOR
JW_STARTS_MIN = sjt.JW_STARTS_MIN
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


def run_one(data, pfm_rank_by_rid, pfm_score_by_rid, dates, bush_keys, pfm_a_floor, jw_top_pct):
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
            jw_cutoff_rank = max(1, round(len(jw_field) * jw_top_pct / 100))

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
                # Include-style, NaN-safe (see CLAUDE.md's PFM_A_FLOOR entry
                # for why this must not be written exclude-style).
                pfm_score = pfm_score_by_rid.get(rid)
                if pfm_a_floor is None or (pfm_score is not None and pfm_score >= pfm_a_floor):
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

    print(f"\n=== Baseline: current production (PFM_A_FLOOR={sjt.PFM_A_FLOOR}, JW_RELATIVE_TOP_PCT={sjt.JW_RELATIVE_TOP_PCT}) ===")
    r = run_one(data, pfm_rank_by_rid, pfm_score_by_rid, dates, bush_keys, sjt.PFM_A_FLOOR, sjt.JW_RELATIVE_TOP_PCT)
    print("  A:", fmt(r["A"]))
    print("  B:", fmt(r["B"]))

    pfm_floors = [None, 50, 55, 60, 65, 70, 75]
    jw_pcts = [10, 15, 20, 25, 30]

    print("\n=== Combined sweep (rows: PFM_A_FLOOR, cols: JW_RELATIVE_TOP_PCT) ===")
    for pfm_floor in pfm_floors:
        for jw_pct in jw_pcts:
            r = run_one(data, pfm_rank_by_rid, pfm_score_by_rid, dates, bush_keys, pfm_floor, jw_pct)
            label = f"pfm>={pfm_floor if pfm_floor is not None else 'none'}, jw_top{jw_pct}%"
            print(f"{label:<26} A: {fmt(r['A'])}   B: {fmt(r['B'])}")


if __name__ == "__main__":
    main()
