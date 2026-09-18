"""One-off scratch analysis: a genuinely untested angle after margin
buckets, price floors, state/class slicing, overlay/edge-vs-market
framing, and price-floor win-betting all failed to find a robust Combo
edge (see CLAUDE.md's own running history) - does backing Combo's #1
pick specifically when it DISAGREES with the market (Combo's top pick is
NOT the market's own favourite) do any better than backing it blindly?
Real user question, 2026-09-19: "Any betting edges you can find with
combo score?" - classic "value" framing: a model's pick that goes
AGAINST market consensus is the textbook case for a real edge (if the
model is actually seeing something), so it's worth checking as its own
population rather than lumped in with agreement cases.

Read-only against toprate_runners.csv - writes nothing. Per race: among
non-scratched, resulted runners with both a computable Combo score
(needs wprp_proj at minimum, gracefully degrading trr/pfm same as
production) and a known price, find the top-Combo runner and the
top-price (shortest-priced, i.e. market favourite) runner. AGREE = same
runner; DISAGREE = different runners. Backs the top-Combo runner to win
in both cases (that's the actual bet - "Combo's own pick", not the
market's), so DISAGREE is specifically "Combo prefers something other
than the favourite". Requires >=2 qualifying runners in the race
(otherwise there's no real favourite to disagree with).
"""
import pandas as pd

CSV = "toprate_runners.csv"

COMPOSITE_WEIGHT_WPR = 0.50
COMPOSITE_WEIGHT_TRR = 0.25
COMPOSITE_WEIGHT_PFM = 0.25
WPR_POP_MEAN, WPR_POP_STD = 72.57, 10.48
TRR_POP_MEAN, TRR_POP_STD = 96.26, 2.71
PFM_POP_MEAN, PFM_POP_STD = 38.35, 30.88


def combo_score(wpr, trr, pfm):
    if wpr is None or wpr != wpr:
        return None
    weighted_sum = COMPOSITE_WEIGHT_WPR * wpr
    weight_total = COMPOSITE_WEIGHT_WPR
    if trr is not None and trr == trr:
        trr_r = WPR_POP_MEAN + ((trr - TRR_POP_MEAN) / TRR_POP_STD) * WPR_POP_STD
        weighted_sum += COMPOSITE_WEIGHT_TRR * trr_r
        weight_total += COMPOSITE_WEIGHT_TRR
    if pfm is not None and pfm == pfm:
        pfm_r = WPR_POP_MEAN + ((pfm - PFM_POP_MEAN) / PFM_POP_STD) * WPR_POP_STD
        weighted_sum += COMPOSITE_WEIGHT_PFM * pfm_r
        weight_total += COMPOSITE_WEIGHT_PFM
    return weighted_sum / weight_total


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


def main():
    df = pd.read_csv(CSV, low_memory=False)
    df = df[df["scratched"] != 1].copy()
    df["price"] = df["starting_price_sp"].fillna(df["fixed_win_price"])
    df = df[df["resulted"] == 1]
    df["combo"] = [combo_score(w, t, p) for w, t, p in
                   zip(df["wprp_proj"], df["toprate_rating"], df["pfm_score"])]

    rows = []
    for rid, g in df.groupby("race_id"):
        valid = g[g["combo"].notna() & g["price"].notna() & (g["price"] > 1.0)]
        if len(valid) < 2:
            continue
        combo_top = valid.loc[valid["combo"].idxmax()]
        price_top = valid.loc[valid["price"].idxmin()]
        agree = combo_top["run_id"] == price_top["run_id"]
        rows.append({
            "race_id": rid, "date": combo_top["date"], "state": combo_top["state"],
            "agree": agree, "won": combo_top["won"], "placed": combo_top["placed"],
            "price": combo_top["price"], "market_fav_price": price_top["price"],
            "combo_gap_to_fav": combo_top["combo"] - g[g["run_id"] == price_top["run_id"]]["combo"].iloc[0]
            if not agree else 0.0,
        })
    result = pd.DataFrame(rows)
    print(f"Races with >=2 combo+price-valid runners: {len(result)}, "
          f"{result['date'].nunique()} dates ({result['date'].min()} to {result['date'].max()})")

    print("\n=== Backing Combo's #1 pick: AGREE (also market favourite) vs DISAGREE ===")
    print(f"{'group':>10}  {'n':>6}  {'win %':>6}  {'place %':>7}  {'avg price':>9}  {'flat ROI':>9}  {'prop ROI':>9}")
    for label, sub in [("AGREE", result[result["agree"]]), ("DISAGREE", result[~result["agree"]])]:
        flat_roi, prop_roi = roi_stats(sub)
        print(f"{label:>10}  {len(sub):>6}  {100*sub['won'].mean():>5.1f}%  {100*sub['placed'].mean():>6.1f}%  "
              f"${sub['price'].mean():>8.2f}  {flat_roi:>+8.1f}%  {prop_roi:>+8.1f}%")

    disagree = result[~result["agree"]].copy()
    print(f"\n=== DISAGREE only, by how much shorter the market favourite's own price is ===")
    print("(a bigger price ratio = the market favourite is much shorter than Combo's pick's own price - "
          "the market strongly disagrees with Combo, not just a photo-finish preference)")
    disagree["price_ratio"] = disagree["price"] / disagree["market_fav_price"]
    bins = [1, 1.5, 2, 3, 5, 1000]
    disagree["bucket"] = pd.cut(disagree["price_ratio"], bins=bins)
    print(f"{'price ratio':>14}  {'n':>6}  {'win %':>6}  {'avg price':>9}  {'flat ROI':>9}  {'prop ROI':>9}")
    for b, g in disagree.groupby("bucket", observed=True):
        flat_roi, prop_roi = roi_stats(g)
        print(f"{str(b):>14}  {len(g):>6}  {100*g['won'].mean():>5.1f}%  ${g['price'].mean():>8.2f}  "
              f"{flat_roi:>+8.1f}%  {prop_roi:>+8.1f}%")

    print(f"\n=== DISAGREE only, by state ===")
    print(f"{'state':>6}  {'n':>6}  {'win %':>6}  {'avg price':>9}  {'flat ROI':>9}  {'prop ROI':>9}")
    for state, g in disagree.groupby("state"):
        if len(g) < 20:
            continue
        flat_roi, prop_roi = roi_stats(g)
        print(f"{state:>6}  {len(g):>6}  {100*g['won'].mean():>5.1f}%  ${g['price'].mean():>8.2f}  "
              f"{flat_roi:>+8.1f}%  {prop_roi:>+8.1f}%")

    # SA (the only near-breakeven cell above, +0.9%/+2.4%, n=173) checked
    # the same two ways every apparently-positive cell in this file's
    # history gets checked before being called a finding: FAILS both.
    # First-half/second-half date split (51 dates): +15.1% vs -12.0% -
    # not a stable edge. Excluding the 2 biggest-priced winners ($8.5,
    # $8.0) flips it to -7.6% flat ROI. Not a real finding - the DISAGREE
    # population overall (-15.1%/-16.2%, n=2,369) is the honest headline,
    # not this one small, noisy state slice.


if __name__ == "__main__":
    main()
