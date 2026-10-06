"""One-off scratch analysis: for the Race tab's Combo score, how does
capture rate for win/quinella/trifecta/first-four compare between the
INNER 5-point gap-from-top pool and the OUTER 10-point pool (the same two
thresholds now drawn as the dotted/solid reference lines on the Race tab -
see raceModel.ts's COMBO_INNER_GAP_FROM_TOP/COMPOSITE_MAX_GAP_FROM_TOP)?
Real user question, 2026-09-19: "What's the analysis on 1st, quinella,
tri, f4 for within 5 pts vs 10 pts. With tri & f4, could it be a standout
where within 5 pts is in for all positions and then within 10 pts is just
in for the last 1 or 2 places" - i.e., a "banker(s) for the top spot(s),
wider net for the minor placings" exotic-bet structure: does relaxing
ONLY the last 1-2 required positions from the tight (5pt) pool to the
wide (10pt) pool capture nearly as well as boxing the whole wide pool for
every position, while banking on fewer runners for the positions that
matter most?

Direct follow-up, same day: "What about adding a price floor and only
win betting those within 5 or 10 pts of top rated" - a completely
different bet shape from the exotics above (no #1-pick-only or edge-vs-
market framing either, unlike wpr_combo_top_pick_margin_analysis.py/
wpr_combo_price_overlay_test.py): back EVERY runner in the inner5 or
outer10 pool to WIN, restricted to a price floor, and see if that's ever
profitable. Added as a second analysis section, reusing this script's
existing inner5/outer10 pool definitions.

Read-only against toprate_runners.csv - writes nothing. Same complete-case
population as wpr_composite_score_capture_test.py (every non-scratched
runner in the race has wprp_proj/pfm_score/toprate_rating - no price
requirement, since this is pure capture rate, not ROI), using the
CURRENTLY-SHIPPED Combo weighting (0.50*wpr + 0.25*toprateRating(rescaled)
+ 0.25*formFactor(rescaled), matching raceModel.ts as of 2026-09-19 - NOT
the earlier 0.45/0.30/0.25 wpr_combo_race_tab_capture_analysis.py used).

For each race: inner5 = runners with combo_gap <= 5 (top rated's own gap
is 0, so always included); outer10 = runners with combo_gap <= 10
(superset of inner5, since 5 < 10). A race is only counted toward a given
exotic's capture rate if all the runners that exotic needs (2 for
quinella, 3 for trifecta, 4 for first-four) actually have a known finish
position (no fewer than that many finishers, e.g. a race abandoned after
2 runners can't have a real trifecta).

Hybrid variants (the actual question): for trifecta, "relax last 1" means
1st and 2nd must be in inner5, 3rd only needs to be in outer10; "relax
last 2" means only 1st must be in inner5, 2nd and 3rd only need outer10.
Same pattern for first-four (relax last 1/2/3) and quinella (relax last
1, i.e. only 1st needs inner5, 2nd just needs outer10) - the pure inner5
and pure outer10 rows are the two ends of this same spectrum, included
for comparison. avg pool size (avg n runners in inner5 / outer10 per
race) reported alongside, since that's the real "how many selections do I
need" cost of each pool - the hybrid's own effective cost isn't a single
number (it's inner5-sized for the strict positions, outer10-sized for the
relaxed ones), so both raw pool sizes are shown for reference instead of
inventing a blended one.
"""
import pandas as pd

CSV = "toprate_runners.csv"

# Matches frontend/src/lib/raceModel.ts exactly as currently shipped.
COMPOSITE_WEIGHT_WPR = 0.50
COMPOSITE_WEIGHT_TRR = 0.25
COMPOSITE_WEIGHT_PFM = 0.25
COMBO_INNER_GAP_FROM_TOP = 5
COMPOSITE_MAX_GAP_FROM_TOP = 10


def zscore_rescale(series: pd.Series, target_mean: float, target_std: float) -> pd.Series:
    z = (series - series.mean()) / series.std()
    return target_mean + z * target_std


def main():
    df = pd.read_csv(CSV, low_memory=False)
    df = df[df["scratched"] != 1]
    wpr_mean, wpr_std = df["wprp_proj"].mean(), df["wprp_proj"].std()

    df["complete"] = df["wprp_proj"].notna() & df["pfm_score"].notna() & df["toprate_rating"].notna()
    race_complete = df.groupby("race_id")["complete"].all()
    complete_race_ids = set(race_complete[race_complete].index)
    cdf = df[df["race_id"].isin(complete_race_ids)].copy()
    cdf = cdf[cdf["resulted"] == 1]
    print(f"Complete-case, resulted races: {cdf['race_id'].nunique()} races, "
          f"{cdf['date'].nunique()} dates ({cdf['date'].min()} to {cdf['date'].max()}), "
          f"{len(cdf)} runners")

    cdf["pfm_rescaled"] = zscore_rescale(cdf["pfm_score"], wpr_mean, wpr_std)
    cdf["trr_rescaled"] = zscore_rescale(cdf["toprate_rating"], wpr_mean, wpr_std)
    cdf["combo"] = (
        COMPOSITE_WEIGHT_WPR * cdf["wprp_proj"]
        + COMPOSITE_WEIGHT_TRR * cdf["trr_rescaled"]
        + COMPOSITE_WEIGHT_PFM * cdf["pfm_rescaled"]
    )
    cdf["combo_top"] = cdf.groupby("race_id")["combo"].transform("max")
    cdf["combo_gap"] = cdf["combo_top"] - cdf["combo"]
    cdf["in_inner5"] = cdf["combo_gap"] <= COMBO_INNER_GAP_FROM_TOP
    cdf["in_outer10"] = cdf["combo_gap"] <= COMPOSITE_MAX_GAP_FROM_TOP

    avg_inner5 = cdf.groupby("race_id")["in_inner5"].sum().mean()
    avg_outer10 = cdf.groupby("race_id")["in_outer10"].sum().mean()
    print(f"Avg selections per race: inner5={avg_inner5:.2f}  outer10={avg_outer10:.2f}\n")

    by_place = {}
    for place in [1, 2, 3, 4]:
        rows = cdf[cdf["finish_position"] == place]
        by_place[place] = rows.groupby("race_id")["run_id"].apply(lambda s: s.iloc[0] if len(s) else None).to_dict()

    inner5_lookup = cdf.set_index(["race_id", "run_id"])["in_inner5"]
    outer10_lookup = cdf.set_index(["race_id", "run_id"])["in_outer10"]

    def in_pool(pool_lookup, rid, run_id):
        try:
            return bool(pool_lookup.loc[(rid, run_id)])
        except KeyError:
            return False

    race_ids = cdf["race_id"].unique()

    # required: list of pool_lookup functions, one per required placegetter,
    # in finish-position order (1st, 2nd, ...). e.g. [inner5, inner5, outer10]
    # for trifecta "relax last 1".
    def capture_rate(required_pools):
        n_places = len(required_pools)
        hits = 0
        n = 0
        for rid in race_ids:
            placegetters = [by_place[p].get(rid) for p in range(1, n_places + 1)]
            if any(pg is None for pg in placegetters):
                continue
            n += 1
            if all(in_pool(pool, rid, pg) for pool, pg in zip(required_pools, placegetters)):
                hits += 1
        return (100 * hits / n if n else float("nan")), n

    print("=== WIN (1st only) ===")
    for label, pools in [("inner5", [inner5_lookup]), ("outer10", [outer10_lookup])]:
        rate, n = capture_rate(pools)
        print(f"  {label:>10}: {rate:5.1f}%  (n={n})")

    print("\n=== QUINELLA (1st & 2nd) ===")
    variants = [
        ("inner5 / inner5", [inner5_lookup, inner5_lookup]),
        ("inner5 / outer10 (relax last 1)", [inner5_lookup, outer10_lookup]),
        ("outer10 / outer10", [outer10_lookup, outer10_lookup]),
    ]
    for label, pools in variants:
        rate, n = capture_rate(pools)
        print(f"  {label:<34}: {rate:5.1f}%  (n={n})")

    print("\n=== TRIFECTA (1st, 2nd, 3rd) ===")
    variants = [
        ("inner5 / inner5 / inner5", [inner5_lookup] * 3),
        ("inner5 / inner5 / outer10 (relax last 1)", [inner5_lookup, inner5_lookup, outer10_lookup]),
        ("inner5 / outer10 / outer10 (relax last 2)", [inner5_lookup, outer10_lookup, outer10_lookup]),
        ("outer10 / outer10 / outer10", [outer10_lookup] * 3),
    ]
    for label, pools in variants:
        rate, n = capture_rate(pools)
        print(f"  {label:<42}: {rate:5.1f}%  (n={n})")

    print("\n=== FIRST FOUR (1st, 2nd, 3rd, 4th) ===")
    variants = [
        ("inner5 x4", [inner5_lookup] * 4),
        ("inner5,inner5,inner5,outer10 (relax last 1)", [inner5_lookup] * 3 + [outer10_lookup]),
        ("inner5,inner5,outer10,outer10 (relax last 2)", [inner5_lookup] * 2 + [outer10_lookup] * 2),
        ("inner5,outer10,outer10,outer10 (relax last 3)", [inner5_lookup] * 1 + [outer10_lookup] * 3),
        ("outer10 x4", [outer10_lookup] * 4),
    ]
    for label, pools in variants:
        rate, n = capture_rate(pools)
        print(f"  {label:<46}: {rate:5.1f}%  (n={n})")

    # Real user follow-up: "what about adding a price floor and only win
    # betting those within 5 or 10 pts of top rated" - back EVERY runner
    # in the inner5/outer10 pool to WIN (not just the #1 pick), crossed
    # with a price floor. price = starting_price_sp falling back to
    # fixed_win_price, this session's established convention throughout.
    cdf["price"] = cdf["starting_price_sp"].fillna(cdf["fixed_win_price"])

    def stake_for(price: float, return_units: float = 4.0) -> float:
        return return_units / price

    def roi_stats(sub: pd.DataFrame) -> tuple:
        n = len(sub)
        if n == 0:
            return float("nan"), float("nan")
        flat_returned = sub.loc[sub["won"] == 1, "price"].sum()
        flat_roi = 100 * (flat_returned - n) / n
        prop_staked = sub["price"].apply(stake_for).sum()
        prop_returned = 4.0 * sub["won"].sum()
        prop_roi = 100 * (prop_returned - prop_staked) / prop_staked
        return flat_roi, prop_roi

    # NOTE: the one apparently-positive cell in this sweep (inner5,
    # floor>=10: n=248, flat ROI +1.6%, prop ROI +5.1%) does NOT survive
    # the same two robustness checks every other apparently-positive
    # result in this file's history has failed - checked directly rather
    # than reported at face value: excluding the 3 biggest-priced winners
    # (Ozzy The Equaliser $17, Pretty Perky $16, Or Am I $15) flips it to
    # -16.7%/-9.1%, and a first-half/second-half date split (52 dates,
    # 2026-07-24 to 2026-09-18) shows -36.9% vs +38.9% - the "profit"
    # is a handful of longshot winners clustered in one half of the
    # window, not a stable edge. Left in the sweep output below since the
    # raw numbers are still worth seeing, but do not treat floor>=10 as a
    # finding without re-running these same two checks on fresh data.
    floors = [None, 2, 2.5, 3, 4, 5, 6, 8, 10]
    for pool_col, pool_label in [("in_inner5", "INNER5 (gap<=5)"), ("in_outer10", "OUTER10 (gap<=10)")]:
        pool_df = cdf[cdf[pool_col] & cdf["price"].notna() & (cdf["price"] > 1.0)]
        print(f"\n=== Win-betting every runner in {pool_label}, by price floor ===")
        print(f"{'floor':>7}  {'n bets':>7}  {'win %':>6}  {'avg price':>9}  {'flat ROI':>9}  {'prop ROI':>9}")
        for floor in floors:
            sub = pool_df if floor is None else pool_df[pool_df["price"] >= floor]
            if len(sub) == 0:
                continue
            flat_roi, prop_roi = roi_stats(sub)
            label = "none" if floor is None else f">={floor}"
            print(f"{label:>7}  {len(sub):>7}  {100*sub['won'].mean():>5.1f}%  "
                  f"${sub['price'].mean():>8.2f}  {flat_roi:>+8.1f}%  {prop_roi:>+8.1f}%")


if __name__ == "__main__":
    main()
