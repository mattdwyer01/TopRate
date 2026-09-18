"""One-off scratch analysis: direct follow-up to
wpr_combo_jockey_map_combo_test.py (Combo gap<=5/10 + jockey floor + "not
a bad map" alone found no profitable cell) - real user question,
2026-09-19: "And either being an overlay, or within n% of the price (so
not too much of an underlay)". Adds a FOURTH condition: exclude only the
WORST underlays (market price far below Combo's own fair price - the
market is much more confident than the model, which this repo's own
raceModel.ts already treats as a soft warning sign via
driftedToOverlay's MATERIAL_UNDERLAY_AT_OPEN_RATIO=0.85 concept), while
still allowing genuine overlays (market price > fair price) AND mild
underlays.

Fair price/model_prob computed via the SAME softmax formula
wpr_projection.py's compute_edge_scores() uses in production (beta=0.15
from wpr_models/config.json - see wpr_combo_price_overlay_test.py's own
sanity-checking of this), over the race's own Combo-scored-and-priced
runners (not just the jw/map-qualifying subset - fair price is a
property of the whole race's Combo distribution). price_ratio =
market_price / combo_fair_price; ratio > 1 is an overlay (market longer
than fair, unconditionally kept); ratio in [1-n/100, 1] is an underlay
within n% of fair (kept); ratio < 1-n/100 is a "bad" underlay (excluded).
n=0 means "overlay or exactly fair only, no underlay tolerance at all".

Uses toprate_data.json (speed_map isn't in toprate_runners.csv - same
~25-date window and same combo_score()/TAGS/DEMEAN_THRESHOLD as
wpr_combo_jockey_map_combo_test.py, 'ff' confirmed numerically identical
to pfm_score there). Read-only - writes nothing.
"""
import json
from datetime import date

DATA_JSON = "toprate_data.json"
TODAY = date.today().isoformat()
BETA = 0.15  # wpr_models/config.json's "beta" - matches production.

COMPOSITE_WEIGHT_WPR = 0.50
COMPOSITE_WEIGHT_TRR = 0.25
COMPOSITE_WEIGHT_PFM = 0.25
WPR_POP_MEAN, WPR_POP_STD = 72.57, 10.48
TRR_POP_MEAN, TRR_POP_STD = 96.26, 2.71
PFM_POP_MEAN, PFM_POP_STD = 38.35, 30.88
DEMEAN_THRESHOLD = 0.5
TAGS = ("favoured", "neutral")


def combo_score(wpr, trr, pfm):
    if wpr is None:
        return None
    weighted_sum = COMPOSITE_WEIGHT_WPR * wpr
    weight_total = COMPOSITE_WEIGHT_WPR
    if trr is not None:
        trr_r = WPR_POP_MEAN + ((trr - TRR_POP_MEAN) / TRR_POP_STD) * WPR_POP_STD
        weighted_sum += COMPOSITE_WEIGHT_TRR * trr_r
        weight_total += COMPOSITE_WEIGHT_TRR
    if pfm is not None:
        pfm_r = WPR_POP_MEAN + ((pfm - PFM_POP_MEAN) / PFM_POP_STD) * WPR_POP_STD
        weighted_sum += COMPOSITE_WEIGHT_PFM * pfm_r
        weight_total += COMPOSITE_WEIGHT_PFM
    return weighted_sum / weight_total


def stake_for(price, return_units=4.0):
    return return_units / price


def roi_stats(rows):
    n = len(rows)
    if n == 0:
        return float("nan"), float("nan"), float("nan"), float("nan")
    wins = sum(1 for r in rows if r["won"])
    flat_returned = sum(r["price"] for r in rows if r["won"])
    flat_roi = 100 * (flat_returned - n) / n
    prop_staked = sum(stake_for(r["price"]) for r in rows)
    prop_returned = 4.0 * wins
    prop_roi = 100 * (prop_returned - prop_staked) / prop_staked
    return 100 * wins / n, sum(r["price"] for r in rows) / n, flat_roi, prop_roi


def main():
    with open(DATA_JSON) as f:
        data = json.load(f)

    all_rows = []
    n_races = 0
    for r in data.get("RACES", []):
        d = r.get("date")
        if not d or d > TODAY:
            continue
        runners = [u for u in r.get("runners", []) if not u.get("scr")]
        if len(runners) < 2:
            continue

        scored = []
        for u in runners:
            c = combo_score(u.get("wpjp"), u.get("trr"), u.get("ff"))
            if c is not None:
                scored.append((u, c))
        if len(scored) < 2:
            continue
        top_combo = max(c for _, c in scored)

        sm_vals = [u.get("wpjcb", {}).get("speed_map") for u, _ in scored]
        sm_vals = [v for v in sm_vals if v is not None]
        sm_mean = sum(sm_vals) / len(sm_vals) if sm_vals else 0.0

        # Fair price/model_prob: softmax over the race's own combo-scored
        # AND priced runners (a property of the whole race, independent
        # of which runner we later bet on) - mirrors compute_edge_scores.
        priced_scored = []
        for u, c in scored:
            price = u.get("sp") if u.get("sp") is not None else u.get("fx")
            if price is not None and price > 1.0:
                priced_scored.append((u, c, price))
        fair_price_by_rid = {}
        if len(priced_scored) >= 2:
            max_c = max(c for _, c, _ in priced_scored)
            exps = [(u, pow(2.718281828, BETA * (c - max_c))) for u, c, _ in priced_scored]
            sum_e = sum(e for _, e in exps)
            for u, e in exps:
                prob = e / sum_e
                fair_price_by_rid[u.get("rid")] = min(1.0 / prob, 999.0) if prob > 0 else None

        n_races += 1
        for u, c in scored:
            f_pos = u.get("f")
            won = u.get("won")
            if f_pos is None and won is None:
                continue
            price = u.get("sp") if u.get("sp") is not None else u.get("fx")
            if price is None or price <= 1.0:
                continue
            gap = top_combo - c
            jw = u.get("jw")
            sm = u.get("wpjcb", {}).get("speed_map")
            demeaned = (sm - sm_mean) if sm is not None else None
            if demeaned is None:
                tag = "unknown"
            elif demeaned <= -DEMEAN_THRESHOLD:
                tag = "unfavoured"
            elif demeaned >= DEMEAN_THRESHOLD:
                tag = "favoured"
            else:
                tag = "neutral"
            fair_price = fair_price_by_rid.get(u.get("rid"))
            price_ratio = (price / fair_price) if fair_price else None
            all_rows.append({
                "gap": gap, "jw": jw, "tag": tag, "won": (won == 1), "price": price,
                "price_ratio": price_ratio,
            })

    print(f"Resulted races contributing: {n_races}, runner-rows with a known result+price: {len(all_rows)}")
    has_ratio = sum(1 for r in all_rows if r["price_ratio"] is not None)
    print(f"Rows with a computable fair-price ratio: {has_ratio}")

    gap_thresholds = [5, 10]
    jw_floor = 18  # the sweet spot from wpr_combo_jockey_filter_test.py
    underlay_tolerances = [0, 5, 10, 15, 20, 25, None]  # None = no price condition at all

    print(f"\nFixed: jw>=18, map filter (tag in favoured/neutral) - sweeping gap threshold x underlay tolerance")
    print(f"{'gap<=':>6}  {'underlay tol':>13}  {'n':>6}  {'win %':>6}  {'avg price':>9}  "
          f"{'flat ROI':>9}  {'prop ROI':>9}")
    for gap_t in gap_thresholds:
        base = [r for r in all_rows if r["gap"] <= gap_t
                and r["jw"] is not None and r["jw"] >= jw_floor
                and r["tag"] in TAGS]
        for tol in underlay_tolerances:
            if tol is None:
                sub = base
                label = "none (no filter)"
            else:
                sub = [r for r in base if r["price_ratio"] is not None
                       and r["price_ratio"] >= (1 - tol / 100)]
                label = f"<= {tol}% under fair"
            win_pct, avg_price, flat_roi, prop_roi = roi_stats(sub)
            print(f"{gap_t:>6}  {label:>13}  {len(sub):>6}  {win_pct:>5.1f}%  ${avg_price:>8.2f}  "
                  f"{flat_roi:>+8.1f}%  {prop_roi:>+8.1f}%")

    # Robustness check on the two "overlay/fair-only" (0% underlay
    # tolerance) cells, the best-looking rows above - same two checks
    # every apparently-positive Combo result in this file's history gets.
    # FAILS the exclude-3-biggest-winners check clearly for both (the
    # classic fragility signature already documented repeatedly here) -
    # do not treat these as findings.
    print("\n=== Robustness check: gap<=5/10, jw>=18, map filter, overlay-or-fair-only (ratio>=1.0) ===")
    for gap_t in [5, 10]:
        sub = [r for r in all_rows if r["gap"] <= gap_t
               and r["jw"] is not None and r["jw"] >= jw_floor
               and r["tag"] in TAGS and r["price_ratio"] is not None and r["price_ratio"] >= 1.0]
        winners = sorted([r for r in sub if r["won"]], key=lambda r: -r["price"])
        excl = [r for r in sub if r not in winners[:3]]
        e_flat, e_prop = roi_stats(excl)[2], roi_stats(excl)[3]
        overall_flat, overall_prop = roi_stats(sub)[2], roi_stats(sub)[3]
        print(f"gap<={gap_t} (n={len(sub)}): overall flat={overall_flat:+.1f}%/prop={overall_prop:+.1f}%  "
              f"excl-top3-winners flat={e_flat:+.1f}%/prop={e_prop:+.1f}%")


if __name__ == "__main__":
    main()
