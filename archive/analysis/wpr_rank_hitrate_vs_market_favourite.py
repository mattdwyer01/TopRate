"""
wpr_rank_hitrate_vs_market_favourite.py - a pure FORECASTING-SKILL check,
separate from the ROI/edge-vs-market question already answered (no,
"buy disagreement with market" doesn't work - see wpr_real_model_
calibration_diagnosis.py / wpr_calibrated_edge_kfold_validation.py /
wpr_top_pick_margin_strategy_kfold.py). This asks a more basic question:
how often does the ACTUAL race winner correspond to the model's #1
(#2, #3, ...) ranked runner, and how does that compare to how often the
winner is simply the market's own favourite (shortest price)? This is
informative even though we already know it can't be turned into a
profitable "back the disagreement" strategy - it tells us whether the
model's own ranking has real skill (comparable to, or a bit below/above,
the market's own skill), independent of price/ROI entirely.

METHOD: for every eligible race (field>=4, every runner has a real
projection from the current, corrected project_race() - see PR #165),
rank runners two ways: by projected_wpr descending (model_rank 1 = the
model's top pick) and by price ascending (market_rank 1 = the actual
market favourite, shortest price). For each race, record the winner's
model_rank and market_rank. Reports:
  1. Hit-rate distribution: what fraction of races are won by the
     model's rank-1/2/3/4+ pick, vs the market's rank-1/2/3/4+ (the
     favourite/2nd-favourite/etc) - directly comparable strike rates.
  2. Agreement rate: how often the model's #1 pick IS the market
     favourite (same horse).
  3. Head-to-head on DISAGREEMENT races only (model's #1 != market's #1):
     which one wins more often, on the exact same set of races - the
     cleanest possible comparison of the two ranking systems' skill.

Reuses the cached full-history projected population (see
wpr_calibrated_edge_kfold_validation.build_pool) - no ROI/staking
involved here at all, this is strike-rate/rank-accuracy only.

NO EM DASHES policy: hyphens only in this file.
"""
import pandas as pd

from wpr_calibrated_edge_kfold_validation import build_pool

MIN_FIELD_SIZE = 4
RANK_BUCKETS = [1, 2, 3, 4]  # 4 means "4th or worse"


def bucket_rank(r):
    return r if r in (1, 2, 3) else 4


def run():
    pool = build_pool()
    field_size = pool.groupby("race_id")["proj"].transform("size")
    pool = pool[field_size >= MIN_FIELD_SIZE].copy()
    print(f"Population: {len(pool):,} runners across {pool['race_id'].nunique():,} eligible races "
          f"(field>={MIN_FIELD_SIZE}, every runner projected)")

    pool["model_rank"] = pool.groupby("race_id")["proj"].rank(ascending=False, method="first").astype(int)
    pool["market_rank"] = pool.groupby("race_id")["price"].rank(ascending=True, method="first").astype(int)

    winners = pool[pool["won"] == 1].copy()
    print(f"Races with a recorded winner in this population: {len(winners):,}")

    winners["model_rank_b"] = winners["model_rank"].apply(bucket_rank)
    winners["market_rank_b"] = winners["market_rank"].apply(bucket_rank)

    n = len(winners)
    print(f"\n{'='*90}\nWHERE DOES THE WINNER RANK? (n={n:,} races)\n{'='*90}")
    print(f"{'rank':>12}  {'model strike':>14}  {'market (favourite) strike':>28}")
    for b in RANK_BUCKETS:
        label = f"{b}" if b < 4 else "4+"
        model_pct = (winners["model_rank_b"] == b).mean() * 100
        market_pct = (winners["market_rank_b"] == b).mean() * 100
        print(f"{label:>12}  {model_pct:>13.1f}%  {market_pct:>27.1f}%")

    model_top1 = (pool["model_rank"] == 1)
    market_top1 = (pool["market_rank"] == 1)
    model_top1_strike = pool.loc[model_top1, "won"].mean() * 100
    market_top1_strike = pool.loc[market_top1, "won"].mean() * 100
    print(f"\nModel's #1 pick strike rate (unconditional): {model_top1_strike:.1f}%  (n={model_top1.sum():,})")
    print(f"Market favourite strike rate (unconditional): {market_top1_strike:.1f}%  (n={market_top1.sum():,})")

    # Agreement: does the SAME horse hold model_rank==1 and market_rank==1?
    race_summary = pool.groupby("race_id").apply(
        lambda g: pd.Series({
            "model_pick": g.loc[g["model_rank"] == 1, "horse"].iloc[0] if (g["model_rank"] == 1).any() else None,
            "market_pick": g.loc[g["market_rank"] == 1, "horse"].iloc[0] if (g["market_rank"] == 1).any() else None,
            "model_won": int(g.loc[g["model_rank"] == 1, "won"].iloc[0]) if (g["model_rank"] == 1).any() else None,
            "market_won": int(g.loc[g["market_rank"] == 1, "won"].iloc[0]) if (g["market_rank"] == 1).any() else None,
        }), include_groups=False)
    race_summary["agree"] = race_summary["model_pick"] == race_summary["market_pick"]

    agree_pct = race_summary["agree"].mean() * 100
    print(f"\n{'='*90}\nAGREEMENT: model's #1 pick vs market favourite\n{'='*90}")
    print(f"Same horse in {agree_pct:.1f}% of races (n={len(race_summary):,})")

    agree = race_summary[race_summary["agree"]]
    disagree = race_summary[~race_summary["agree"]]
    print(f"\nWhen they AGREE (n={len(agree):,}): strike rate = {agree['model_won'].mean()*100:.1f}%")
    print(f"\nWhen they DISAGREE (n={len(disagree):,}), head-to-head on the SAME races:")
    print(f"  model's #1 pick wins:          {disagree['model_won'].mean()*100:.1f}%")
    print(f"  market's favourite wins:       {disagree['market_won'].mean()*100:.1f}%")
    both_lose = ((disagree["model_won"] == 0) & (disagree["market_won"] == 0)).mean() * 100
    print(f"  neither wins (someone else):   {both_lose:.1f}%")


if __name__ == "__main__":
    run()
