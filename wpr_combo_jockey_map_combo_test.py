"""One-off scratch analysis: direct follow-up to
wpr_combo_jockey_filter_test.py's finding (a jockey-quality floor on
Combo's own #1 pick is the first Combo-related result this session that
survives robustness checks, though still modest) - real user question,
2026-09-19: "What about combo being within 5 or 10 and good jockey, and
not a bad map". Combines THREE conditions, none of them requiring
solo-only the way speedmap_jockey_tracker.py's own tracker rule does:
  1. Combo gap-from-top <= 5 or <= 10 (not #1-pick-only this time - every
     qualifying runner in the pool, same inner5/outer10 pools as
     wpr_combo_5v10_exotics_capture_test.py)
  2. "good jockey" - jockey_win_pct_90d floor (swept, informed by the
     prior test's own jw>=18/20 sweet spot)
  3. "not a bad map" - speed_map ADJ_TERM demeaned against the race,
     tag != "unfavoured" (matches speedmap_jockey_tracker.py's own TAGS =
     ("favoured", "neutral") and DEMEAN_THRESHOLD=0.5 exactly)

speed_map only exists in toprate_data.json (NOT toprate_runners.csv -
see speedmap_jockey_tracker.py's own _load_pfm_lookup() docstring for why
pfm_score has to be read from the CSV instead), and only populates from
2026-08-22 onward - so this is a MUCH smaller population (~25 dates) than
wpr_combo_jockey_filter_test.py's 121-date one, expect noisier numbers.
Combo computed from toprate_data.json's own abbreviated runner fields
(wpjp=projectedWpr, trr=toprateRating, ff=formFactor - confirmed
numerically equivalent to toprate_runners.csv's pfm_score for the same
run_id, just a different name in the two data representations) using the
CURRENTLY-shipped 0.50/0.25/0.25 weights and the same fixed rescale
constants every other script this session uses. Price is sp (starting
price) falling back to fx (fixed), matching speedmap_jockey_tracker.py's
own price_final convention.

Read-only against toprate_data.json - writes nothing.
"""
import json
from datetime import date

DATA_JSON = "toprate_data.json"
TODAY = date.today().isoformat()

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

    rows_by_config = {}
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

        n_races += 1
        for u, c in scored:
            f_pos = u.get("f")
            won = u.get("won")
            if f_pos is None and won is None:
                continue  # not resulted
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
            rows_by_config.setdefault("__all__", []).append({
                "gap": gap, "jw": jw, "tag": tag, "won": (won == 1), "price": price,
            })

    all_rows = rows_by_config["__all__"]
    print(f"Resulted races contributing: {n_races}, runner-rows: {len(all_rows)}")

    gap_thresholds = [5, 10]
    jw_floors = [None, 14, 18, 20]
    print(f"\n{'gap<=':>6}  {'jw>=':>5}  {'map filter':>10}  {'n':>6}  {'win %':>6}  "
          f"{'avg price':>9}  {'flat ROI':>9}  {'prop ROI':>9}")
    for gap_t in gap_thresholds:
        for jw_f in jw_floors:
            for map_filter in [False, True]:
                sub = [r for r in all_rows if r["gap"] <= gap_t]
                if jw_f is not None:
                    sub = [r for r in sub if r["jw"] is not None and r["jw"] >= jw_f]
                if map_filter:
                    sub = [r for r in sub if r["tag"] in TAGS]
                win_pct, avg_price, flat_roi, prop_roi = roi_stats(sub)
                jw_label = "none" if jw_f is None else f">={jw_f}"
                map_label = "excl.unfav" if map_filter else "any"
                print(f"{gap_t:>6}  {jw_label:>5}  {map_label:>10}  {len(sub):>6}  {win_pct:>5.1f}%  "
                      f"${avg_price:>8.2f}  {flat_roi:>+8.1f}%  {prop_roi:>+8.1f}%")

    # Supplementary: does "not a bad map" help the SPECIFIC population
    # wpr_combo_jockey_filter_test.py already found promising (Combo's
    # own #1 pick + jockey floor, not the whole gap-pool above)? Note
    # this reuses the SAME smaller 25-day speed_map-gated window as the
    # gap-pool test above, not that script's full 121-date one - not
    # directly comparable to those numbers, only to each other (with vs
    # without the map filter, same population otherwise).
    print("\n=== Supplementary: Combo's #1 pick only (not the whole gap-pool), by jw floor, map filter on/off ===")
    print("(same 25-day speed_map-gated window as above - NOT directly comparable to")
    print(" wpr_combo_jockey_filter_test.py's own 121-date numbers for the same jw floors)")
    print(f"{'jw>=':>5}  {'map filter':>10}  {'n':>6}  {'win %':>6}  {'avg price':>9}  {'flat ROI':>9}  {'prop ROI':>9}")
    top_pick_rows = [r for r in all_rows if r["gap"] <= 0.001]
    for jw_f in jw_floors:
        for map_filter in [False, True]:
            sub = top_pick_rows
            if jw_f is not None:
                sub = [r for r in sub if r["jw"] is not None and r["jw"] >= jw_f]
            if map_filter:
                sub = [r for r in sub if r["tag"] in TAGS]
            win_pct, avg_price, flat_roi, prop_roi = roi_stats(sub)
            jw_label = "none" if jw_f is None else f">={jw_f}"
            map_label = "excl.unfav" if map_filter else "any"
            print(f"{jw_label:>5}  {map_label:>10}  {len(sub):>6}  {win_pct:>5.1f}%  "
                  f"${avg_price:>8.2f}  {flat_roi:>+8.1f}%  {prop_roi:>+8.1f}%")


if __name__ == "__main__":
    main()
