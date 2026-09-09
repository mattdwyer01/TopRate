"""wpr_rating_quality_check.py - are the WPR ratings/rankings themselves
any good, independent of the price/overlay question? (user follow-up,
Sep 2026, after wpr_adj_term_combo_search_test.py confirmed there is no
recoverable price-based overlay edge). That question was about whether
wpr_price beats the MARKET's price. This one is more basic: does the
model's own ranking of a field actually correlate with who wins, and does
it produce well-calibrated win probabilities - regardless of whether that
translates into a betting edge (a model can be a genuinely good predictor
and still not beat an efficient market's price, which is a much higher
bar - see wpr_adj_term_combo_search_test.py's conclusion).

WHY THIS CAN USE toprate_runners.csv DIRECTLY, NOT build_training_frame()
  Today's other fix (see wpr_projection.py's build_training_frame
  docstring) was a future-leak in how that OFFLINE reconstruction merges
  wpr_nett - it never affected LIVE SERVING, which always reads each row's
  own wpr_nett directly (verified directly earlier this session: a fresh
  recompute for a sample date was bit-identical to what is stored). And
  per CLAUDE.md / compute_wpr_projection's own docstring, historical
  wprp_proj values are NEVER retroactively rewritten - each row reflects
  whatever model was actually live on that day, a true prospective
  (non-hindsight) prediction. So toprate_runners.csv's own wprp_proj/
  wprp_blend_prob/wpr_rank/finish_position/won columns are clean ground
  truth for this question, no reconstruction needed.

METRICS (three independent lenses on "is the ranking any good"):
  1. Top-pick strike rate: WPR's #1-ranked runner per race vs the market
     favourite (lowest price) vs a "why not" bare-random baseline
     (1/field_size averaged) - the standard practical benchmark.
  2. AUC (won vs wprp_blend_prob, pooled across all runners/races): a
     single overall discrimination number, plus the market's own
     1/price-implied probability's AUC as the benchmark to beat.
  3. Brier score (calibration): wprp_blend_prob vs actual outcome,
     against the market's own de-vigged implied probability's Brier score
     over the same population - does WPR's probability estimate track
     reality at least as well as the market's own price does?
  Reported both over the FULL available history (a mix of model versions
  as they actually shipped over time - the real track record) and over
  just the last ~34 days (current architecture only, matching the
  backfilled window - see toprate_daily.OVERLAY_LIVE_SINCE).

USAGE
  python wpr_rating_quality_check.py

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np
import pandas as pd
from sklearn.metrics import roc_auc_score

import toprate_daily as td

CURRENT_ARCH_SINCE = "2026-08-09"  # matches OVERLAY_LIVE_SINCE - the backfilled window


def market_prob(df):
    inv = 1.0 / df["_price"]
    return inv / df.groupby("race_id")["_price"].transform(lambda s: (1.0 / s).sum())


def top_pick_strike(df, rank_col, ascending=True):
    """For each race, take the row with the best rank_col (lowest if
    ascending, else highest), report strike rate and n races."""
    idx = df.groupby("race_id")[rank_col].idxmin() if ascending else df.groupby("race_id")[rank_col].idxmax()
    picks = df.loc[idx]
    return float(picks["won"].mean() * 100), len(picks)


def brier(df, prob_col):
    return float(((df[prob_col] - df["won"]) ** 2).mean())


def report_slice(df, label):
    print(f"\n{'='*80}\n{label}\n{'='*80}")
    print(f"races: {df['race_id'].nunique():,}  runners: {len(df):,}  "
          f"avg field size: {df.groupby('race_id').size().mean():.1f}")

    avg_field_size = df.groupby("race_id").size().mean()
    random_baseline = 100.0 / avg_field_size

    wpr_strike, n_races_wpr = top_pick_strike(df, "wprp_blend_rank_calc", ascending=True)
    mkt_strike, n_races_mkt = top_pick_strike(df, "_price", ascending=True)
    print(f"\nTop-pick strike rate (n={n_races_wpr:,} races):")
    print(f"  WPR top pick:        {wpr_strike:5.2f}%")
    print(f"  Market favourite:    {mkt_strike:5.2f}%")
    print(f"  Bare random (1/field size, avg): {random_baseline:5.2f}%")

    auc_wpr = roc_auc_score(df["won"], df["wprp_blend_prob"])
    auc_mkt = roc_auc_score(df["won"], df["_mkt_prob"])
    print(f"\nAUC (won vs probability, pooled {len(df):,} runners):")
    print(f"  WPR (wprp_blend_prob): {auc_wpr:.4f}")
    print(f"  Market (implied prob): {auc_mkt:.4f}")

    brier_wpr = brier(df, "wprp_blend_prob")
    brier_mkt = brier(df, "_mkt_prob")
    print(f"\nBrier score (lower is better calibrated):")
    print(f"  WPR:    {brier_wpr:.5f}")
    print(f"  Market: {brier_mkt:.5f}")


def run():
    print("Loading runners...")
    r = td.load_runners()
    r["d"] = r["date"].astype(str).str[:10]
    r["won"] = pd.to_numeric(r["won"], errors="coerce")
    r["resulted"] = pd.to_numeric(r["resulted"], errors="coerce")
    r["scratched"] = pd.to_numeric(r["scratched"], errors="coerce")
    r["wprp_proj"] = pd.to_numeric(r["wprp_proj"], errors="coerce")
    r["wprp_blend_prob"] = pd.to_numeric(r["wprp_blend_prob"], errors="coerce")
    r["_price"] = pd.to_numeric(r["fixed_win_price"], errors="coerce").combine_first(
        pd.to_numeric(r["starting_price_sp"], errors="coerce"))

    scoped = r[(r["resulted"] == 1) & (r["scratched"] != 1) &
               r["won"].notna() & r["wprp_proj"].notna() & r["wprp_blend_prob"].notna() &
               r["_price"].notna() & (r["_price"] > 1.0)].copy()

    # only keep races with >= 4 runners with usable data, matching the
    # convention used everywhere else this session (a 2-3 horse "race"
    # after scratches has degenerate top-pick/AUC statistics)
    field_counts = scoped.groupby("race_id")["race_id"].transform("size")
    scoped = scoped[field_counts >= 4].copy()

    scoped["_mkt_prob"] = market_prob(scoped)
    # rank by wprp_proj descending (higher = better) within each race, for top-pick selection
    scoped["wprp_blend_rank_calc"] = scoped.groupby("race_id")["wprp_proj"].rank(ascending=False, method="first")

    print(f"Total usable rows: {len(scoped):,}  date range {scoped['d'].min()} to {scoped['d'].max()}")

    report_slice(scoped, "FULL AVAILABLE HISTORY (mixed model versions, as actually shipped)")
    report_slice(scoped[scoped["d"] >= CURRENT_ARCH_SINCE], f"CURRENT ARCHITECTURE ONLY (since {CURRENT_ARCH_SINCE})")


if __name__ == "__main__":
    run()
