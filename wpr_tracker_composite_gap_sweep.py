"""One-off scratch analysis: does replacing the tracker's WPR-based gap
check (GAP_MAX, "how close is this runner to the race's own top-projected
WPR") with the Race tab "Combo" composite score change the tracker's
actual ROI/win%? Real user question, 2026-09-19, direct follow-up to
shipping the Combo score on the Race tab: "do trackers need to be
updated to replace wpr 5 rule with new score instead?" -> "Test it".

RE-RUN (2026-09-19, same day) with Combo's REWEIGHTED formula (0.45*wpr +
0.30*trr + 0.25*pfm, down from the original 0.20/0.70/0.10 that this
script's first run tested and rejected) - real user follow-up: "could we
use this new combo in the tracker? is 10 pts margin still accurate?".
The original run found every composite-gap threshold worse than WPR on
ROI for both trackers, attributed to the 70%-trr weight's favourite-bias
pull; the reweighted version leans far less on trr (30%, less than half),
so that specific risk is smaller here - re-verified rather than assumed
carried over. Also re-checks whether ~10 (the Race tab's own matched
margin, calibrated against the GENERAL race field in toprate_runners.csv)
still describes a sensible threshold for the tracker's own, differently-
gated population (JW_FLOOR/JW_RELATIVE_TOP_PCT/speed_map-filtered, not
the whole field) - swept broadly rather than assumed.

This is a DIFFERENT question from the Combo score's own validation
(wpr_composite_score_capture_test.py measured "is the winner in the
shortlist" against toprate_runners.csv's full pfm-covered window, not
gated by speed_map). The tracker's OWN rule needs speed_map (from
wpjcb.speed_map), which only exists from 2026-08-22 onward - so this test
is gated the same way every prior tracker sweep this session was, even
though the Combo score itself isn't.

Read-only against toprate_data.json/toprate_runners.csv - writes nothing.
Re-implements build_candidates()'s race loop with ONLY the gap check's
underlying score swapped (composite instead of raw wpjp) - every other
condition (speed_map tag, JW_FLOOR/JW_RELATIVE_TOP_PCT, JW_STARTS_MIN,
PFM_A_FLOOR for A, trr/pfm rank-agreement for B, PRICE_MIN,
CONTESTED_PRICE_FLOOR) stays exactly as current production. Composite
score uses the EXACT SAME formula/weights/rescale constants as the
currently-shipped frontend/src/lib/raceModel.ts's compositeScore() -
population mean/std for rescaling reused as printed by
wpr_composite_score_capture_test.py. Since GAP_MAX's meaning doesn't
carry over to the composite's different scale, this sweeps a range of
composite-gap thresholds rather than assuming any single number.
"""
import json
from datetime import date

import speedmap_jockey_tracker as sjt

TODAY = date.today().isoformat()
JW_FLOOR = sjt.JW_FLOOR
JW_RELATIVE_TOP_PCT = sjt.JW_RELATIVE_TOP_PCT
JW_STARTS_MIN = sjt.JW_STARTS_MIN
PFM_A_FLOOR = sjt.PFM_A_FLOOR
PRICE_MIN = sjt.PRICE_MIN
CONTESTED_PRICE_FLOOR = sjt.CONTESTED_PRICE_FLOOR

# Matches frontend/src/lib/raceModel.ts exactly (reweighted 2026-09-19 -
# see that file's own comment for the full history).
COMPOSITE_WEIGHT_WPR = 0.45
COMPOSITE_WEIGHT_TRR = 0.30
COMPOSITE_WEIGHT_PFM = 0.25
WPR_POP_MEAN, WPR_POP_STD = 72.57, 10.48
TRR_POP_MEAN, TRR_POP_STD = 96.26, 2.71
PFM_POP_MEAN, PFM_POP_STD = 38.35, 30.88


def composite_score(wpr, trr, pfm):
    if wpr is None:
        return None
    weighted_sum = COMPOSITE_WEIGHT_WPR * wpr
    weight_total = COMPOSITE_WEIGHT_WPR
    if trr is not None:
        trr_rescaled = WPR_POP_MEAN + ((trr - TRR_POP_MEAN) / TRR_POP_STD) * WPR_POP_STD
        weighted_sum += COMPOSITE_WEIGHT_TRR * trr_rescaled
        weight_total += COMPOSITE_WEIGHT_TRR
    if pfm is not None:
        pfm_rescaled = WPR_POP_MEAN + ((pfm - PFM_POP_MEAN) / PFM_POP_STD) * WPR_POP_STD
        weighted_sum += COMPOSITE_WEIGHT_PFM * pfm_rescaled
        weight_total += COMPOSITE_WEIGHT_PFM
    return weighted_sum / weight_total


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


def run_one(data, pfm_rank_by_rid, pfm_score_by_rid, dates, bush_keys, use_composite, gap_max):
    """use_composite=False reproduces current production exactly (for
    verification). use_composite=True swaps the gap check's score to the
    composite, everything else unchanged."""
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
            jw_field = [u.get("jw") for u in runners if u.get("jw") is not None]
            jw_cutoff_rank = max(1, round(len(jw_field) * JW_RELATIVE_TOP_PCT / 100))

            if use_composite:
                score_by_rid = {
                    str(u.get("rid", "")): composite_score(
                        u.get("wpjp"), u.get("trr"), pfm_score_by_rid.get(str(u.get("rid", "")))
                    )
                    for u in runners
                }
                score_vals = list(score_by_rid.values())
            else:
                score_by_rid = {str(u.get("rid", "")): u.get("wpjp") for u in runners}
                score_vals = list(score_by_rid.values())
            top_score = max((v for v in score_vals if v is not None), default=None)

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
                rid = str(u.get("rid", ""))
                own_score = score_by_rid.get(rid)
                gap = (top_score - own_score) if (own_score is not None and top_score is not None) else None
                if gap is None or gap > gap_max:
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
                pfm_score = pfm_score_by_rid.get(rid)
                if pfm_score is not None and pfm_score >= PFM_A_FLOOR:
                    a_pool.append(rid)
                if trr_rank == 1 and pfm_rank == 1:
                    b_pool.append(rid)

            def resolve(pool):
                if len(pool) == 1:
                    rid = pool[0]
                    p = info_by_rid[rid][1]
                    if p is not None and p >= PRICE_MIN:
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


def main():
    with open(sjt.DATA_JSON) as f:
        data = json.load(f)
    pfm_rank_by_rid, pfm_score_by_rid = sjt._load_pfm_lookup()
    bush_keys = sjt._bush_meeting_keys(data)
    dates = sorted({r.get("date") for r in data.get("RACES", []) if r.get("date") and r.get("date") <= TODAY})
    print(f"Backtest window: {dates[0]} to {dates[-1]} ({len(dates)} dates, today={TODAY})")

    print(f"\n=== Verify: reproduce current production exactly (GAP_MAX={sjt.GAP_MAX}, raw WPR) ===")
    r = run_one(data, pfm_rank_by_rid, pfm_score_by_rid, dates, bush_keys, False, sjt.GAP_MAX)
    print("  A:", fmt(r["A"]), "  B:", fmt(r["B"]))

    print("\n=== Composite-score gap sweep (replaces WPR-based GAP_MAX check) ===")
    for gap_max in [3, 4, 5, 6, 7.5, 10, 12.5, 15, 20]:
        r = run_one(data, pfm_rank_by_rid, pfm_score_by_rid, dates, bush_keys, True, gap_max)
        print(f"  composite gap<={gap_max:<5} A: {fmt(r['A'])}   B: {fmt(r['B'])}")


if __name__ == "__main__":
    main()
