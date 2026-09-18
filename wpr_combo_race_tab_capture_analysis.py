"""One-off scratch analysis: for the Race (Summary) tab specifically (the
general race listing, NOT the tracker's own gated betting-rule
population), how well does the currently-shipped Combo score (0.45*wpr +
0.30*toprateRating(rescaled) + 0.25*formFactor(rescaled)) find the actual
race result at a margin of 10 and below, COMPARED to just taking the
market in order (shortest price first)? Real user question, 2026-09-19,
direct follow-up to the margin-only winner/quinella/trifecta/first-four
table: "Compare the above table to if you just took the market in order.
Add avg price to help compare".

Read-only against toprate_runners.csv - writes nothing. Same population
as wpr_composite_score_capture_test.py, with one addition: a race is
complete-case only if EVERY non-scratched runner also has a known price
(starting_price_sp, falling back to fixed_win_price - same convention
raceModel.ts's computeEffectiveRace uses for market price), so the
market ranking is never missing a runner the way it would be if a
favourite happened to lack a recorded price. This narrows the population
slightly from the original 1,994/56-date window - printed below, not
assumed unchanged.

Market comparison methodology: Combo's own margin thresholds don't have
a market equivalent in the same units (a WPR-point gap isn't a price
gap), so the market side is compared by RANK instead (1st favourite,
2nd favourite, ...) - the natural way to describe "taking the market in
order". For each Combo margin row (with its own average selection
count, which varies continuously with the field), the market side is
computed by linearly interpolating between the two integer rank cutoffs
bracketing that same average selection count, so both sides carry
exactly the same average number of selections per race - the only way
this comparison is fair, otherwise a wider Combo shortlist would look
arbitrarily better or worse than a narrower market one for reasons
having nothing to do with which one predicts better.

Avg price: mean price across every SELECTED runner-instance (not a
per-race average of averages) - if you'd blindly backed everyone in the
shortlist, what would the average price have been. Reported for both
sides so a reader can see whether Combo's edge (if any) comes at the
cost of shorter, more heavily-backed prices or not.
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
    print(f"Complete-case (incl. known price), resulted races: {cdf['race_id'].nunique()} races, "
          f"{cdf['date'].nunique()} dates ({cdf['date'].min()} to {cdf['date'].max()}), "
          f"{len(cdf)} runners")

    cdf["pfm_rescaled"] = zscore_rescale(cdf["pfm_score"], wpr_mean, wpr_std)
    cdf["trr_rescaled"] = zscore_rescale(cdf["toprate_rating"], wpr_mean, wpr_std)
    cdf["combo"] = 0.45 * cdf["wprp_proj"] + 0.30 * cdf["trr_rescaled"] + 0.25 * cdf["pfm_rescaled"]
    cdf["combo_top"] = cdf.groupby("race_id")["combo"].transform("max")
    cdf["combo_gap"] = cdf["combo_top"] - cdf["combo"]
    # Market "gap": rank - 1, so gap <= K-1 means "in the top K favourites".
    # Reuses the exact same threshold machinery as combo_gap.
    cdf["market_rank"] = cdf.groupby("race_id")["price"].rank(method="first", ascending=True)
    cdf["market_gap"] = cdf["market_rank"] - 1

    by_place = {}
    for place in [1, 2, 3, 4]:
        rows = cdf[cdf["finish_position"] == place]
        by_place[place] = rows.groupby("race_id")["run_id"].apply(lambda s: s.iloc[0] if len(s) else None).to_dict()

    race_ids = cdf["race_id"].unique()

    def stats_for_gap(gap_col: str, T: float):
        in_pool = cdf[gap_col] <= T
        avg_sel = in_pool.groupby(cdf["race_id"]).sum().mean()
        avg_price = cdf.loc[in_pool, "price"].mean()
        gap_lookup = cdf.set_index(["race_id", "run_id"])[gap_col]

        def captured(rid, run_id):
            try:
                return gap_lookup.loc[(rid, run_id)] <= T
            except KeyError:
                return False

        win_hits = win_n = quin_hits = quin_n = tri_hits = tri_n = first4_hits = first4_n = 0
        for rid in race_ids:
            r1, r2, r3, r4 = (by_place[p].get(rid) for p in (1, 2, 3, 4))
            if r1 is not None:
                win_n += 1
                win_hits += captured(rid, r1)
            if r1 is not None and r2 is not None:
                quin_n += 1
                quin_hits += captured(rid, r1) and captured(rid, r2)
            if r1 is not None and r2 is not None and r3 is not None:
                tri_n += 1
                tri_hits += captured(rid, r1) and captured(rid, r2) and captured(rid, r3)
            if r1 is not None and r2 is not None and r3 is not None and r4 is not None:
                first4_n += 1
                first4_hits += captured(rid, r1) and captured(rid, r2) and captured(rid, r3) and captured(rid, r4)
        return {
            "avg_sel": avg_sel, "avg_price": avg_price,
            "win": 100 * win_hits / win_n, "quin": 100 * quin_hits / quin_n,
            "tri": 100 * tri_hits / tri_n, "first4": 100 * first4_hits / first4_n,
        }

    def market_matched(target_avg_sel: float):
        """Interpolate market stats between the two integer rank cutoffs
        bracketing target_avg_sel, so both sides carry the same average
        selection count."""
        k_lo = int(target_avg_sel)
        k_hi = k_lo + 1
        lo = stats_for_gap("market_gap", k_lo - 1) if k_lo >= 1 else {k: 0.0 for k in
                                                                        ["avg_sel", "avg_price", "win", "quin", "tri", "first4"]}
        hi = stats_for_gap("market_gap", k_hi - 1)
        frac = target_avg_sel - k_lo
        return {k: lo[k] * (1 - frac) + hi[k] * frac for k in lo}

    print("\n=== Margin view: Combo vs market-in-order (matched avg selections), 2026-09-19 ===")
    header = f"{'margin':>7}  {'avg sel':>8} | {'Combo win/quin/tri/f4':>24}  {'avg $':>6} | {'Mkt win/quin/tri/f4':>22}  {'avg $':>6}"
    print(header)
    for T in [3, 4, 5, 6, 7, 8, 9, 10]:
        c = stats_for_gap("combo_gap", T)
        m = market_matched(c["avg_sel"])
        print(f"{T:>7}  {c['avg_sel']:>8.2f} | "
              f"{c['win']:>5.1f}/{c['quin']:>5.1f}/{c['tri']:>5.1f}/{c['first4']:>5.1f}  ${c['avg_price']:>5.2f} | "
              f"{m['win']:>5.1f}/{m['quin']:>5.1f}/{m['tri']:>5.1f}/{m['first4']:>5.1f}  ${m['avg_price']:>5.2f}")


if __name__ == "__main__":
    main()
