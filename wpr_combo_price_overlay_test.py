"""One-off scratch analysis: convert the Race tab's Combo score into an
implied win probability/fair price via the SAME softmax formula
wpr_projection.py's project_race()/compute_edge_scores() already use for
raw WPR (beta read from wpr_models/config.json = 0.15, NOT the 0.4
fallback get_price_beta() falls back to when config is missing) - is
there a real, profitable overlay signal (market price > Combo's own fair
price) here, the way this repo's own documented history already found
for raw WPR alone (wpr_slope_roi_test.py, referenced in
wpr_projection.py's calibration-removal comment: edge>=0.10 strike rate
16.7%->19.1%, ROI held/improved, t-stats strengthened)? Real user
question, 2026-09-19: "What about if combo was converted into a price and
compared against market? Can it be profitable to bet overlays?"

Read-only against toprate_runners.csv - writes nothing. Mirrors
compute_edge_scores() exactly rather than reinventing the edge
calculation: for each race, softmax over every runner with a usable
score (Combo, or WPR for the baseline column) gives model_prob; the
SAME priced-and-scored subset's inverse prices, normalised, gives
market_prob; edge = model_prob - market_prob; has_edge when edge > 0
(the market is offering a longer price than the model's own fair value,
i.e. an overlay). Combo itself uses the CURRENTLY-shipped formula and
population rescale constants from frontend/src/lib/raceModel.ts
(0.50*wpr + 0.25*trr(rescaled) + 0.25*pfm(rescaled), gracefully dropping
a missing trr/pfm and renormalising remaining weights - the real
production behaviour, not a complete-case-only approximation like the
margin/capture scripts elsewhere in this session use) - WPR_POP_MEAN=
72.57/STD=10.48, TRR_POP_MEAN=96.26/STD=2.71, PFM_POP_MEAN=38.35/
STD=30.88, matching every prior script that already used these fixed
constants.

Two parallel columns are computed side by side, Combo and raw WPR alone,
so the question "can Combo be profitable" has a direct, real baseline to
compare against (the WPR edge is repo history's own already-validated
signal), not just an isolated number.

Price: `starting_price_sp` falling back to `fixed_win_price` (this
session's established convention throughout, matching raceModel.ts's own
`computeEffectiveRace` display price - NOT the same fallback ORDER
`toprate_daily.py`'s own edge-writing call site uses, `fixed_win_price`
combine_first `starting_price_sp` combine_first `price_top`). Checked
directly rather than assumed safe: re-deriving edge from scratch with
EITHER price order does not reproduce the CSV's own already-stored
`wprp_edge` column closely (mean abs diff ~0.03-0.05, some large
individual outliers) - root cause is almost certainly that `wprp_edge`
was written ONCE, pre-race, against whatever price was live at fetch
time, while `fixed_win_price`/`starting_price_sp` in today's CSV are the
CURRENT (repeatedly overwritten by 5-min price refreshes and the
post-race SP fill) values - comparing a frozen historical edge against a
now-updated price column is a timing mismatch, not proof either price
convention is wrong. Sanity-checked the formula a different way instead:
edge correlates with log(price) only moderately (~0.4, printed below,
confirming it's not a near-tautology), and a high-edge (>0.10) subset
beats its OWN price bucket's baseline win rate in most buckets (also
printed) - the same "not just picking longshots" property this repo's
own documented favourite-longshot-bias check already required of the
raw-WPR edge signal.
"""
import numpy as np
import pandas as pd

CSV = "toprate_runners.csv"
BETA = 0.15  # wpr_models/config.json's "beta" - matches production exactly.

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
    print(f"Resulted, non-scratched runners: {len(df)}, "
          f"{df['race_id'].nunique()} races, {df['date'].nunique()} dates "
          f"({df['date'].min()} to {df['date'].max()})")

    df["combo"] = [combo_score(w, t, p) for w, t, p in
                   zip(df["wprp_proj"], df["toprate_rating"], df["pfm_score"])]

    def edge_table(score_col: str, label: str) -> pd.DataFrame:
        rows = []
        for rid, g in df.groupby("race_id"):
            scored = g[g[score_col].notna()]
            valid = scored[scored["price"].notna() & (scored["price"] > 1.0)]
            if len(valid) < 2:
                continue
            s = valid[score_col].to_numpy(dtype=float)
            e = np.exp(BETA * (s - s.max()))
            model_prob = e / e.sum()
            inv = 1.0 / valid["price"].to_numpy(dtype=float)
            market_prob = inv / inv.sum()
            edge = model_prob - market_prob
            out = valid[["run_id", "won", "price"]].copy()
            out["edge"] = edge
            rows.append(out)
        result = pd.concat(rows, ignore_index=True)
        print(f"\n{label}: {len(rows)} races contributing, {len(result)} scored-and-priced runners")
        return result

    combo_result = edge_table("combo", "Combo-based edge")
    wpr_result = edge_table("wprp_proj", "Raw-WPR-based edge (baseline, matches production's own compute_edge_scores)")

    # Sanity check before trusting the headline ROI numbers below: edge
    # correlates with price to some degree (corr with log(price) ~0.4,
    # printed below) since a flatter model softmax than the market's own
    # naturally shows a small positive edge on most longshots - the real
    # question (matching this repo's own documented favourite-longshot-
    # bias check for raw WPR) is whether a high-edge subset beats its
    # OWN price bucket's baseline win rate, not just "picks longshots".
    print(f"\ncorr(edge, log(price)), WPR baseline: {wpr_result['edge'].corr(np.log(wpr_result['price'])):.3f}")
    bins = [1, 2, 3, 5, 8, 15, 30, 1000]
    wpr_result_b = wpr_result.copy()
    wpr_result_b["bucket"] = pd.cut(wpr_result_b["price"], bins=bins)
    print("\n=== WPR baseline: win rate within price bucket, edge>0.10 vs bucket baseline ===")
    print(f"{'price bucket':>14}  {'n':>6}  {'baseline win%':>13}  {'n edge>0.10':>11}  {'edge>0.10 win%':>14}")
    for b, g in wpr_result_b.groupby("bucket", observed=True):
        hi = g[g["edge"] > 0.10]
        hi_win = 100 * hi["won"].mean() if len(hi) else float("nan")
        print(f"{str(b):>14}  {len(g):>6}  {100*g['won'].mean():>12.1f}%  {len(hi):>11}  {hi_win:>13.1f}%")

    thresholds = [0.0, 0.02, 0.04, 0.06, 0.08, 0.10, 0.15, 0.20]
    for label, result in [("COMBO", combo_result), ("WPR (baseline)", wpr_result)]:
        print(f"\n=== {label}: overlay (edge > threshold) win rate / ROI by threshold ===")
        print(f"{'edge>':>7}  {'n bets':>7}  {'win %':>6}  {'avg price':>9}  {'flat ROI':>9}  {'prop ROI':>9}")
        for t in thresholds:
            sub = result[result["edge"] > t]
            flat_roi, prop_roi = roi_stats(sub)
            win_pct = 100 * sub["won"].mean() if len(sub) else float("nan")
            avg_price = sub["price"].mean() if len(sub) else float("nan")
            print(f"{t:>7.2f}  {len(sub):>7}  {win_pct:>5.1f}%  ${avg_price:>8.2f}  "
                  f"{flat_roi:>+8.1f}%  {prop_roi:>+8.1f}%")


if __name__ == "__main__":
    main()
