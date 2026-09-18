"""One-off scratch analysis: for the Race (Summary) tab specifically (the
general race listing, NOT the tracker's own gated betting-rule
population), how well does the currently-shipped Combo score (0.45*wpr +
0.30*toprateRating(rescaled) + 0.25*formFactor(rescaled)) find the actual
race winner, at a margin of 10 and below, and at fixed top-2/3/4
shortlists? Real user question, 2026-09-19: "What is the analysis for
finding the winner using combo? Look at within 10 and less, look at
strike rate of finding winner, top 2,3,4 and how many selections on avg".

Read-only against toprate_runners.csv - writes nothing. Same methodology/
population as wpr_composite_score_capture_test.py (complete-case resulted
races only, so every non-scratched runner has wprp_proj/pfm_score/
toprate_rating - avoids asymmetric treatment from pfm_score's partial
coverage): 1,994 races, 56 dates (2026-07-24 to 2026-09-17), not gated by
speed_map since this is a Race-tab display question, not the tracker's
own betting rule.

Two views, both reported since the user asked for both:
  - Margin (gap-from-top) view: avg selections per race and win-capture
    rate at margin<=T for T in 3..10. NOT directly comparable to WPR-
    alone's own margin numbers at the same T - blending compresses the
    scale (see wpr_composite_score_capture_test.py's own matched-margin
    section), so Combo's pool at a given T is always smaller than WPR's
    at that same T. Included anyway since it directly answers "within 10
    and less" as asked, with WPR's own numbers alongside for reference.
  - Fixed top-K view: exactly K selections per race (ties aside), which
    IS a fair, direct comparison against WPR alone since selection count
    is held equal by construction.
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
    cdf["wpr_top"] = cdf.groupby("race_id")["wprp_proj"].transform("max")
    cdf["wpr_gap"] = cdf["wpr_top"] - cdf["wprp_proj"]
    cdf["combo_rank"] = cdf.groupby("race_id")["combo"].rank(method="min", ascending=False)
    cdf["wpr_rank"] = cdf.groupby("race_id")["wprp_proj"].rank(method="min", ascending=False)

    winners = cdf[cdf["won"] == 1]

    print("\n=== Margin (gap-from-top) view: Combo vs raw WPR at the SAME nominal margin ===")
    print(f"{'margin':>7}  {'Combo avg sel':>13}  {'Combo capture':>13}   {'WPR avg sel':>11}  {'WPR capture':>11}")
    for T in [3, 4, 5, 6, 7, 8, 9, 10]:
        combo_pool = (cdf["combo_gap"] <= T).groupby(cdf["race_id"]).sum().mean()
        combo_capture = (winners["combo_gap"] <= T).mean()
        wpr_pool = (cdf["wpr_gap"] <= T).groupby(cdf["race_id"]).sum().mean()
        wpr_capture = (winners["wpr_gap"] <= T).mean()
        print(f"{T:>7}  {combo_pool:>13.2f}  {100*combo_capture:>12.1f}%   "
              f"{wpr_pool:>11.2f}  {100*wpr_capture:>10.1f}%")
    print("  (Combo's pool is always smaller than WPR's at the same margin - blending")
    print("   compresses the scale. Not a fair strength comparison at equal T; see top-K below.)")

    print("\n=== Fixed top-K view (fair: exactly K selections/race either way) ===")
    print(f"{'K':>3}  {'Combo capture':>13}  {'Combo avg sel':>13}   {'WPR capture':>11}  {'WPR avg sel':>11}")
    for K in [1, 2, 3, 4, 5]:
        combo_capture = (winners["combo_rank"] <= K).mean()
        combo_sel = (cdf["combo_rank"] <= K).groupby(cdf["race_id"]).sum().mean()
        wpr_capture = (winners["wpr_rank"] <= K).mean()
        wpr_sel = (cdf["wpr_rank"] <= K).groupby(cdf["race_id"]).sum().mean()
        print(f"{K:>3}  {100*combo_capture:>12.1f}%  {combo_sel:>13.2f}   "
              f"{100*wpr_capture:>10.1f}%  {wpr_sel:>11.2f}")


if __name__ == "__main__":
    main()
