"""One-off scratch analysis: Combo alone has no robust backing edge (see
CLAUDE.md's running history - margin, price floor, state, class, overlay/
edge-vs-market, win-betting, market-disagreement all tested and failed).
Direct follow-up, real user request 2026-09-19 ("look into that" - bring
in a signal Combo doesn't already contain, per the closing suggestion of
the prior analysis): does adding a JOCKEY-QUALITY filter to Combo's own
#1 pick find a real edge, the same way speedmap_jockey_tracker.py's own
JW_RELATIVE_TOP_PCT/JW_FLOOR mechanic already has a real, backtested,
positive-ROI history for its own (differently-gated) tracker population?
This tests the SAME jockey-relative-rank idea against a completely
different base population (Combo's own #1 pick, not the tracker's
solo-only/speed_map-gated one) to see if it transfers.

Read-only against toprate_runners.csv - writes nothing. Same per-runner-
valid population as wpr_combo_market_disagreement_test.py/
wpr_combo_price_overlay_test.py (6,126 races, 121 dates, no complete-case
gate - the biggest population used for any Combo test this session).
jw_field is jockey_win_pct_90d across the WHOLE race field (every
non-scratched runner, not just the combo+price-valid subset) - matches
speedmap_jockey_tracker.py's own build_candidates() convention exactly
(the whole point of a RELATIVE rule is comparing against the full
field's jockey quality). Combo's own #1 pick's jockey rank within that
field (ties count generously, same _rank_desc convention) is checked
against a swept top-X% cutoff.
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


def rank_desc(value, all_values):
    if value is None or value != value:
        return None
    return 1 + sum(1 for v in all_values if v is not None and v == v and v > value)


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
        pick = valid.loc[valid["combo"].idxmax()]
        jw_field = g["jockey_win_pct_90d"].tolist()
        jw_field_n = sum(1 for v in jw_field if v is not None and v == v)
        jw_rank = rank_desc(pick["jockey_win_pct_90d"], jw_field)
        jw_pct = 100 * jw_rank / jw_field_n if jw_rank is not None and jw_field_n else None
        rows.append({
            "race_id": rid, "date": pick["date"], "won": pick["won"], "placed": pick["placed"],
            "price": pick["price"], "jw": pick["jockey_win_pct_90d"], "jw_rank": jw_rank,
            "jw_field_n": jw_field_n, "jw_pct": jw_pct,
        })
    result = pd.DataFrame(rows)
    print(f"Combo #1 picks: {len(result)} races, {result['date'].nunique()} dates "
          f"({result['date'].min()} to {result['date'].max()})")
    has_jw = result["jw_pct"].notna().sum()
    print(f"Picks with a known jockey_win_pct_90d and a scoreable field: {has_jw} ({100*has_jw/len(result):.1f}%)")

    flat_roi, prop_roi = roi_stats(result)
    print(f"\nBaseline (no jockey filter): n={len(result)}  win%={100*result['won'].mean():.1f}%  "
          f"flat ROI={flat_roi:+.1f}%  prop ROI={prop_roi:+.1f}%")

    print("\n=== Combo #1 pick, filtered by jockey's own relative rank in the field (top X%) ===")
    print(f"{'top X%':>7}  {'n':>6}  {'win %':>6}  {'avg price':>9}  {'flat ROI':>9}  {'prop ROI':>9}")
    for pct in [10, 15, 20, 25, 30, 40, 50, 100]:
        sub = result[result["jw_pct"].notna() & (result["jw_pct"] <= pct)]
        flat_roi, prop_roi = roi_stats(sub)
        print(f"{pct:>6}%  {len(sub):>6}  {100*sub['won'].mean():>5.1f}%  ${sub['price'].mean():>8.2f}  "
              f"{flat_roi:>+8.1f}%  {prop_roi:>+8.1f}%")

    print("\n=== Combo #1 pick, ABSOLUTE jockey_win_pct_90d floor ===")
    print(f"{'jw >=':>7}  {'n':>6}  {'win %':>6}  {'avg price':>9}  {'flat ROI':>9}  {'prop ROI':>9}")
    for floor in [None, 10, 14, 16, 18, 20, 25, 30]:
        sub = result if floor is None else result[result["jw"] >= floor]
        sub = sub[sub["jw"].notna()] if floor is None else sub
        flat_roi, prop_roi = roi_stats(sub)
        label = "none" if floor is None else f">={floor}"
        print(f"{label:>7}  {len(sub):>6}  {100*sub['won'].mean():>5.1f}%  ${sub['price'].mean():>8.2f}  "
              f"{flat_roi:>+8.1f}%  {prop_roi:>+8.1f}%")

    # Robustness check on the two most promising cells (jw>=18/20) -
    # the same two checks every apparently-positive cell in this file's
    # history gets before being called a finding. Unlike every prior
    # positive cell (CONTESTED_PRICE_FLOOR's own, the gap>=3/price>=3
    # claim, Maiden race class, inner5/floor>=10 win-betting), THIS ONE
    # does not collapse into deeply negative territory under either
    # check - it's the first genuinely more-robust-than-noise result
    # this whole Combo-edge thread has found, though still modest and
    # weaker in the second half than the first.
    print("\n=== Robustness check: jw>=18 and jw>=20, date-half split + exclude 3 biggest winners ===")
    for floor in [18, 20]:
        sub = result[result["jw"] >= floor]
        dates = sorted(sub["date"].unique())
        mid = dates[len(dates) // 2]
        first, second = sub[sub["date"] < mid], sub[sub["date"] >= mid]
        winners = sub[sub["won"] == 1].sort_values("price", ascending=False)
        excl = sub.drop(winners.head(3).index)
        f_flat, f_prop = roi_stats(first)
        s_flat, s_prop = roi_stats(second)
        e_flat, e_prop = roi_stats(excl)
        print(f"jw>={floor} (n={len(sub)}): first-half n={len(first)} flat={f_flat:+.1f}%/prop={f_prop:+.1f}%  "
              f"second-half n={len(second)} flat={s_flat:+.1f}%/prop={s_prop:+.1f}%  "
              f"excl-top3-winners flat={e_flat:+.1f}%/prop={e_prop:+.1f}%")


if __name__ == "__main__":
    main()
