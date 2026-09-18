"""One-off scratch analysis: for the TOP-RATED runner by Combo score in
each race, does the MARGIN to the 2nd-rated Combo runner predict a
higher win/place strike rate for that top pick? Real user question,
2026-09-19: "Can you do some analysis on top rated combo horses? Strike
rate and place strike rate based on margin to 2nd horse".

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
bucket: n races, the #1 pick's own win rate, place rate, and average
price (context - a wider gap plausibly correlates with a shorter price
too, which this checks directly rather than assuming).
"""
import pandas as pd

CSV = "toprate_runners.csv"


def zscore_rescale(series: pd.Series, target_mean: float, target_std: float) -> pd.Series:
    z = (series - series.mean()) / series.std()
    return target_mean + z * target_std


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
    })
    print(f"\nRaces with a defined #1-vs-#2 Combo gap: {len(result)}")
    print(f"Overall top-Combo-pick win rate: {100*result['won'].mean():.1f}%  "
          f"place rate: {100*result['placed'].mean():.1f}%  avg price: ${result['price'].mean():.2f}")

    bins = [0, 1, 2, 3, 5, 7, 10, 15, float("inf")]
    labels = ["0-1", "1-2", "2-3", "3-5", "5-7", "7-10", "10-15", "15+"]
    result["bucket"] = pd.cut(result["gap"], bins=bins, labels=labels, right=False)

    print("\n=== Top-Combo-pick win/place strike rate by margin to 2nd ===")
    print(f"{'gap bucket':>10}  {'n races':>7}  {'win %':>6}  {'place %':>7}  {'avg price':>9}")
    for label in labels:
        sub = result[result["bucket"] == label]
        if len(sub) == 0:
            continue
        print(f"{label:>10}  {len(sub):>7}  {100*sub['won'].mean():>5.1f}%  "
              f"{100*sub['placed'].mean():>6.1f}%  ${sub['price'].mean():>8.2f}")


if __name__ == "__main__":
    main()
