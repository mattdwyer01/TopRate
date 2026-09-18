"""One-off scratch analysis: for the Race (Summary) tab specifically (the
general race listing, NOT the tracker's own gated betting-rule
population), how well does the currently-shipped Combo score (0.45*wpr +
0.30*toprateRating(rescaled) + 0.25*formFactor(rescaled)) find the actual
race result at a margin of 10 and below? Real user question, 2026-09-19:
"only look at margin view, but give me strike rate for finding winner,
quinella, trifecta, first four, and avg number of selections" - a direct
follow-up narrowing the first pass (which also included a top-K view) to
margin-only, and widening "capture" from just the winner to the standard
exotic bet types.

Read-only against toprate_runners.csv - writes nothing. Same population
as wpr_composite_score_capture_test.py (complete-case resulted races
only: every non-scratched runner has wprp_proj/pfm_score/toprate_rating -
avoids asymmetric treatment from pfm_score's partial coverage): 1,994
races, 56 dates (2026-07-24 to 2026-09-17), not gated by speed_map since
this is a Race-tab display question, not the tracker's own betting rule.

Definitions, per race, at margin T (runners with gap-from-top <= T):
  - Winner strike rate: the actual 1st placegetter is in the pool.
  - Quinella strike rate: BOTH the actual 1st and 2nd placegetters are in
    the pool (order-free, matching how a quinella bet pays).
  - Trifecta strike rate: the actual 1st, 2nd, AND 3rd placegetters are
    all in the pool.
  - First four strike rate: the actual 1st, 2nd, 3rd, AND 4th
    placegetters are all in the pool.
Each of these is computed only over races where that many finishing
positions are actually known (a race with only 3 finishers on record
can't contribute to the first-four denominator) - checked directly via
finish_position, not assumed from field size (a big field can still lack
a recorded 4th if results are incomplete).
"""
import pandas as pd

CSV = "toprate_runners.csv"


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
    cdf["combo"] = 0.45 * cdf["wprp_proj"] + 0.30 * cdf["trr_rescaled"] + 0.25 * cdf["pfm_rescaled"]
    cdf["combo_top"] = cdf.groupby("race_id")["combo"].transform("max")
    cdf["combo_gap"] = cdf["combo_top"] - cdf["combo"]

    # Per-race lookup: run_id of the 1st/2nd/3rd/4th placegetter, or None
    # if that placing wasn't recorded for this race.
    by_place = {}
    for place in [1, 2, 3, 4]:
        rows = cdf[cdf["finish_position"] == place]
        by_place[place] = rows.groupby("race_id")["run_id"].apply(lambda s: s.iloc[0] if len(s) else None).to_dict()

    gap_by_race_run = cdf.set_index(["race_id", "run_id"])["combo_gap"]
    race_ids = cdf["race_id"].unique()

    def captured(race_id, run_id, T):
        try:
            return gap_by_race_run.loc[(race_id, run_id)] <= T
        except KeyError:
            return False

    print("\n=== Margin view: strike rate for winner / quinella / trifecta / first-four ===")
    print(f"{'margin':>7}  {'avg sel':>8}  {'winner':>8}  {'quinella':>9}  {'trifecta':>9}  {'first-4':>8}")
    for T in [3, 4, 5, 6, 7, 8, 9, 10]:
        pool_size = (cdf["combo_gap"] <= T).groupby(cdf["race_id"]).sum().mean()

        win_hits = win_n = 0
        quin_hits = quin_n = 0
        tri_hits = tri_n = 0
        first4_hits = first4_n = 0
        for rid in race_ids:
            r1 = by_place[1].get(rid)
            r2 = by_place[2].get(rid)
            r3 = by_place[3].get(rid)
            r4 = by_place[4].get(rid)
            if r1 is not None:
                win_n += 1
                win_hits += captured(rid, r1, T)
            if r1 is not None and r2 is not None:
                quin_n += 1
                quin_hits += captured(rid, r1, T) and captured(rid, r2, T)
            if r1 is not None and r2 is not None and r3 is not None:
                tri_n += 1
                tri_hits += captured(rid, r1, T) and captured(rid, r2, T) and captured(rid, r3, T)
            if r1 is not None and r2 is not None and r3 is not None and r4 is not None:
                first4_n += 1
                first4_hits += (
                    captured(rid, r1, T) and captured(rid, r2, T)
                    and captured(rid, r3, T) and captured(rid, r4, T)
                )

        print(f"{T:>7}  {pool_size:>8.2f}  {100*win_hits/win_n:>7.1f}%  {100*quin_hits/quin_n:>8.1f}%  "
              f"{100*tri_hits/tri_n:>8.1f}%  {100*first4_hits/first4_n:>7.1f}%")
    print(f"\n(denominators: winner n={win_n}, quinella n={quin_n}, trifecta n={tri_n}, first-4 n={first4_n} "
          f"- races missing that many recorded placings are excluded from that column only)")


if __name__ == "__main__":
    main()
