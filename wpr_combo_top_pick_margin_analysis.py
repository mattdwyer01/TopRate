"""One-off scratch analysis: for the TOP-RATED runner by Combo score in
each race, does the MARGIN to the 2nd-rated Combo runner predict a
higher win/place strike rate for that top pick? Real user question,
2026-09-19: "Can you do some analysis on top rated combo horses? Strike
rate and place strike rate based on margin to 2nd horse". Then: "any ROI
calc? flat and proportionate" (every margin bucket came back negative -
the market shortens price roughly in step with rising strike rate), then
"what about with some price floors?" - since the losses were driven by
the shortest prices, checks whether excluding them (PRICE_MIN, same
concept as speedmap_jockey_tracker.py's own floor) recovers any edge,
both overall and crossed with the margin buckets above. A follow-up
claim that "gap>=3 with price>=$3 is profitable" was checked directly
rather than assumed: the exact open-ended rule is actually negative
(-7.7% flat ROI, n=498) - the earlier +7.5% was specific to the
NARROWER bucket 3-5 only, and that narrower result didn't survive
excluding the 3 biggest-priced winners (flips to -3.8%) or a first-half/
second-half split (+14.1% -> +0.9%) - the same fragility signature
already found once this session with CONTESTED_PRICE_FLOOR's own
robustness check. Then: "what about by race class or state?" - overall
population (every margin, not bucketed) sliced by state and by a
simplified race_class grouping.

Read-only against toprate_runners.csv - writes nothing. Same complete-
case population as wpr_combo_race_tab_capture_analysis.py (every non-
scratched runner in the race has wprp_proj/pfm_score/toprate_rating AND
a known price - 1,994 races, 56 dates, 2026-07-24 to 2026-09-17), using
the currently-shipped Combo weighting (0.50*wpr + 0.25*toprateRating
(rescaled) + 0.25*formFactor(rescaled)). "Placed" reuses the CSV's own
`placed` column (confirmed: placed=1 whenever won=1, i.e. it already
means "finished top 3", not "top 3 excluding the winner" - no separate
handling needed).

For each race, the "gap to 2nd" is combo(rank 1) - combo(rank 2) among
non-scratched runners - races with fewer than 2 such runners are
excluded (no 2nd to compare against). Bucketed into gap ranges; for each
bucket: n races, the #1 pick's own win rate, place rate, average price,
and ROI (real user follow-up: "any ROI calc? flat and proportionate") -
flat (1 unit per bet, same convention as speedmap_jockey_tracker.py's
own backtests throughout this session) and proportional (staked to
return a fixed 4 units on a win, stake_for(price) = 4/price, matching
that same file's summarize()/stake_for()).
"""
import pandas as pd

CSV = "toprate_runners.csv"


def zscore_rescale(series: pd.Series, target_mean: float, target_std: float) -> pd.Series:
    z = (series - series.mean()) / series.std()
    return target_mean + z * target_std


def stake_for(price: float, return_units: float = 4.0) -> float:
    return return_units / price


def main():
    df = pd.read_csv(CSV, low_memory=False)
    df = df[df["scratched"] != 1]
    df["price"] = df["starting_price_sp"].fillna(df["fixed_win_price"])
    wpr_mean, wpr_std = df["wprp_proj"].mean(), df["wprp_proj"].std()

    df["complete"] = (
        df["wprp_proj"].notna() & df["pfm_score"].notna() & df["toprate_rating"].notna() & df["price"].notna()
    )
    race_complete = df.groupby("race_id")["complete"].all()
    complete_race_ids = set(race_complete[race_complete].index)
    cdf = df[df["race_id"].isin(complete_race_ids)].copy()
    cdf = cdf[cdf["resulted"] == 1]
    print(f"Complete-case, resulted races: {cdf['race_id'].nunique()} races, "
          f"{cdf['date'].nunique()} dates ({cdf['date'].min()} to {cdf['date'].max()}), "
          f"{len(cdf)} runners")

    cdf["pfm_rescaled"] = zscore_rescale(cdf["pfm_score"], wpr_mean, wpr_std)
    cdf["trr_rescaled"] = zscore_rescale(cdf["toprate_rating"], wpr_mean, wpr_std)
    cdf["combo"] = 0.50 * cdf["wprp_proj"] + 0.25 * cdf["trr_rescaled"] + 0.25 * cdf["pfm_rescaled"]
    cdf["combo_rank"] = cdf.groupby("race_id")["combo"].rank(method="first", ascending=False)

    top1 = cdf[cdf["combo_rank"] == 1].set_index("race_id")
    top2 = cdf[cdf["combo_rank"] == 2].set_index("race_id")
    races_with_2 = top1.index.intersection(top2.index)
    top1 = top1.loc[races_with_2]
    top2 = top2.loc[races_with_2]

    gap = top1["combo"] - top2["combo"].reindex(top1.index)
    result = pd.DataFrame({
        "gap": gap,
        "won": top1["won"],
        "placed": top1["placed"],
        "price": top1["price"],
        "state": top1["state"],
        "race_class": top1["race_class"],
    })

    def class_bucket(v):
        if not isinstance(v, str):
            return "Unknown"
        vl = v.lower()
        if vl.startswith("maiden"):
            return "Maiden"
        if vl.startswith("open"):
            return "Open"
        if vl.startswith("class"):
            return "Class"
        if vl.startswith("benchmark"):
            return "Benchmark"
        if vl.startswith("restricted"):
            return "Restricted"
        return "Other"

    result["class_bucket"] = result["race_class"].apply(class_bucket)
    def roi_stats(sub: pd.DataFrame) -> tuple:
        n = len(sub)
        flat_returned = sub.loc[sub["won"] == 1, "price"].sum()
        flat_roi = 100 * (flat_returned - n) / n
        prop_staked = sub["price"].apply(stake_for).sum()
        prop_returned = 4.0 * sub["won"].sum()
        prop_roi = 100 * (prop_returned - prop_staked) / prop_staked
        return flat_roi, prop_roi

    print(f"\nRaces with a defined #1-vs-#2 Combo gap: {len(result)}")
    overall_flat_roi, overall_prop_roi = roi_stats(result)
    print(f"Overall top-Combo-pick win rate: {100*result['won'].mean():.1f}%  "
          f"place rate: {100*result['placed'].mean():.1f}%  avg price: ${result['price'].mean():.2f}  "
          f"flat ROI: {overall_flat_roi:+.1f}%  prop ROI: {overall_prop_roi:+.1f}%")

    bins = [0, 1, 2, 3, 5, 7, 10, 15, float("inf")]
    labels = ["0-1", "1-2", "2-3", "3-5", "5-7", "7-10", "10-15", "15+"]
    result["bucket"] = pd.cut(result["gap"], bins=bins, labels=labels, right=False)

    print("\n=== Top-Combo-pick win/place strike rate and ROI by margin to 2nd ===")
    print(f"{'gap bucket':>10}  {'n races':>7}  {'win %':>6}  {'place %':>7}  {'avg price':>9}  "
          f"{'flat ROI':>9}  {'prop ROI':>9}")
    for label in labels:
        sub = result[result["bucket"] == label]
        if len(sub) == 0:
            continue
        flat_roi, prop_roi = roi_stats(sub)
        print(f"{label:>10}  {len(sub):>7}  {100*sub['won'].mean():>5.1f}%  "
              f"{100*sub['placed'].mean():>6.1f}%  ${sub['price'].mean():>8.2f}  "
              f"{flat_roi:>+8.1f}%  {prop_roi:>+8.1f}%")

    floors = [None, 2, 2.5, 3, 4, 5, 6, 8, 10]
    print("\n=== Price floor sweep, overall (no margin segmentation) ===")
    print(f"{'floor':>7}  {'n races':>7}  {'win %':>6}  {'place %':>7}  {'avg price':>9}  "
          f"{'flat ROI':>9}  {'prop ROI':>9}")
    for floor in floors:
        sub = result if floor is None else result[result["price"] >= floor]
        if len(sub) == 0:
            continue
        flat_roi, prop_roi = roi_stats(sub)
        label = "none" if floor is None else f">={floor}"
        print(f"{label:>7}  {len(sub):>7}  {100*sub['won'].mean():>5.1f}%  "
              f"{100*sub['placed'].mean():>6.1f}%  ${sub['price'].mean():>8.2f}  "
              f"{flat_roi:>+8.1f}%  {prop_roi:>+8.1f}%")

    print("\n=== Price floor sweep, crossed with margin bucket ===")
    print(f"{'bucket':>10}  {'floor':>6}  {'n races':>7}  {'win %':>6}  {'place %':>7}  "
          f"{'avg price':>9}  {'flat ROI':>9}  {'prop ROI':>9}")
    for label in labels:
        bucket_sub = result[result["bucket"] == label]
        if len(bucket_sub) == 0:
            continue
        for floor in [None, 3, 4, 5]:
            sub = bucket_sub if floor is None else bucket_sub[bucket_sub["price"] >= floor]
            if len(sub) == 0:
                continue
            flat_roi, prop_roi = roi_stats(sub)
            floor_label = "none" if floor is None else f">={floor}"
            print(f"{label:>10}  {floor_label:>6}  {len(sub):>7}  {100*sub['won'].mean():>5.1f}%  "
                  f"{100*sub['placed'].mean():>6.1f}%  ${sub['price'].mean():>8.2f}  "
                  f"{flat_roi:>+8.1f}%  {prop_roi:>+8.1f}%")

    # Real user follow-up: "what about by race class or state?" - overall
    # top-Combo-pick population (every margin, not bucketed), sliced by
    # state and by a simplified race_class grouping (the raw field has
    # dozens of specific Benchmark/Restricted rating values - grouped into
    # Maiden/Open/Class/Benchmark/Restricted/Other/Unknown for a readable
    # breakdown, not because the specific rating doesn't matter, just to
    # keep bucket sizes meaningful).
    print("\n=== Overall top-Combo-pick win/place/ROI by STATE ===")
    print(f"{'state':>6}  {'n races':>7}  {'win %':>6}  {'place %':>7}  {'avg price':>9}  "
          f"{'flat ROI':>9}  {'prop ROI':>9}")
    for state, sub in result.groupby("state"):
        if len(sub) == 0:
            continue
        flat_roi, prop_roi = roi_stats(sub)
        print(f"{state:>6}  {len(sub):>7}  {100*sub['won'].mean():>5.1f}%  "
              f"{100*sub['placed'].mean():>6.1f}%  ${sub['price'].mean():>8.2f}  "
              f"{flat_roi:>+8.1f}%  {prop_roi:>+8.1f}%")

    print("\n=== Overall top-Combo-pick win/place/ROI by RACE CLASS (grouped) ===")
    print(f"{'class':>10}  {'n races':>7}  {'win %':>6}  {'place %':>7}  {'avg price':>9}  "
          f"{'flat ROI':>9}  {'prop ROI':>9}")
    class_order = ["Maiden", "Open", "Class", "Benchmark", "Restricted", "Other", "Unknown"]
    for cb in class_order:
        sub = result[result["class_bucket"] == cb]
        if len(sub) == 0:
            continue
        flat_roi, prop_roi = roi_stats(sub)
        print(f"{cb:>10}  {len(sub):>7}  {100*sub['won'].mean():>5.1f}%  "
              f"{100*sub['placed'].mean():>6.1f}%  ${sub['price'].mean():>8.2f}  "
              f"{flat_roi:>+8.1f}%  {prop_roi:>+8.1f}%")


if __name__ == "__main__":
    main()
