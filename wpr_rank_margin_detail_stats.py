"""
wpr_rank_margin_detail_stats.py - detailed follow-up to wpr_rank_hitrate_
vs_market_favourite.py's headline numbers (model top-1 strike 26.3% vs
market favourite 33.7%). Answers, all from the same real (corrected)
project_race() population:
  1. How often does the model's #1 pick WIN.
  2. How often does the model's #1 pick PLACE (top 2 / top 3 finish).
  3. Win rate by the WPR-point gap between the model's #1 and #2 pick -
     does a bigger gap actually predict a higher win rate.
  4. How often the winner comes from the model's top 4 picks (cumulative).
  5. avg/median/Q1/Q3 of the margin (in WPR points) from the winner's own
     projected_wpr up to the #1 pick's projected_wpr in that race (0 when
     the winner IS the #1 pick).
  6. avg/median/Q1/Q3 of the winner's own rank in the model's ordering.

Reuses the cached full-history projected population (see wpr_calibrated_
edge_kfold_validation.build_pool) - rebuilds (~15 min) only if a relevant
file changed since the last cache.

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np
import pandas as pd

from wpr_calibrated_edge_kfold_validation import build_pool

MIN_FIELD_SIZE = 4


def run():
    pool = build_pool()
    field_size = pool.groupby("race_id")["proj"].transform("size")
    pool = pool[field_size >= MIN_FIELD_SIZE].copy()
    print(f"Population: {len(pool):,} runners across {pool['race_id'].nunique():,} eligible races "
          f"(field>={MIN_FIELD_SIZE}, every runner projected)")

    pool["model_rank"] = pool.groupby("race_id")["proj"].rank(ascending=False, method="first").astype(int)
    pool["finish_position"] = pd.to_numeric(pool["finish_position"], errors="coerce")

    n_races = pool["race_id"].nunique()

    # --- 1 & 2: win rate and place rate of the model's #1 pick ---
    top1 = pool[pool["model_rank"] == 1].copy()
    win_rate = top1["won"].mean() * 100
    place2_rate = (top1["finish_position"] <= 2).mean() * 100
    place3_rate = (top1["finish_position"] <= 3).mean() * 100
    print(f"\n{'='*90}\nMODEL'S #1 PICK: WIN AND PLACE RATE (n={len(top1):,} races)\n{'='*90}")
    print(f"  Wins (finishes 1st):        {win_rate:.1f}%")
    print(f"  Places top 2 (1st or 2nd):  {place2_rate:.1f}%")
    print(f"  Places top 3 (1st-3rd):     {place3_rate:.1f}%")
    print("  (place-payout rules vary by field size in real markets - top 3 is the common convention,")
    print("   some small fields only pay 2 places - both shown for reference)")

    # --- 3: win rate by gap-to-#2 bucket ---
    rank2 = pool[pool["model_rank"] == 2][["race_id", "proj"]].rename(columns={"proj": "proj_r2"})
    top1g = top1.merge(rank2, on="race_id", how="inner")
    top1g["gap"] = top1g["proj"] - top1g["proj_r2"]
    gap_bins = [0, 1, 2, 3, 5, 8, float("inf")]
    gap_labels = ["0-1", "1-2", "2-3", "3-5", "5-8", "8+"]
    top1g["gap_bucket"] = pd.cut(top1g["gap"], bins=gap_bins, labels=gap_labels, include_lowest=True)
    print(f"\n{'='*90}\nMODEL'S #1 PICK WIN RATE BY GAP TO #2 (WPR points)\n{'='*90}")
    g = top1g.groupby("gap_bucket", observed=True).agg(n=("won", "size"), win_rate=("won", "mean"))
    g["win_rate"] = g["win_rate"] * 100
    print(g.to_string(formatters={"win_rate": "{:.1f}%".format}))

    # --- 4: cumulative hit rate, winner in top-K picks ---
    winners = pool[pool["won"] == 1][["race_id", "model_rank"]].rename(columns={"model_rank": "winner_rank"})
    print(f"\n{'='*90}\nCUMULATIVE HIT RATE: winner within model's top-K picks (n={len(winners):,} races)\n{'='*90}")
    for k in [1, 2, 3, 4, 5]:
        pct = (winners["winner_rank"] <= k).mean() * 100
        print(f"  top {k}: {pct:.1f}%")

    # --- 5: margin from winner's proj up to the #1 pick's proj ---
    top1p = top1[["race_id", "proj"]].rename(columns={"proj": "proj_top1"})
    winner_full = pool[pool["won"] == 1][["race_id", "proj", "model_rank"]].merge(top1p, on="race_id", how="inner")
    winner_full["margin_to_top1"] = winner_full["proj_top1"] - winner_full["proj"]
    desc = winner_full["margin_to_top1"].describe(percentiles=[0.25, 0.5, 0.75])
    print(f"\n{'='*90}\nMARGIN (WPR points): winner's own projection UP TO the #1 pick's projection\n{'='*90}")
    print(f"  (0 when the winner IS the #1 pick; n={len(winner_full):,} races)")
    print(f"  mean:   {winner_full['margin_to_top1'].mean():.2f}")
    print(f"  median: {desc['50%']:.2f}")
    print(f"  Q1:     {desc['25%']:.2f}")
    print(f"  Q3:     {desc['75%']:.2f}")

    # --- 6: winner's own rank distribution ---
    desc_rank = winner_full["model_rank"].describe(percentiles=[0.25, 0.5, 0.75])
    print(f"\n{'='*90}\nWINNER'S RANK in the model's ordering (1 = model's top pick)\n{'='*90}")
    print(f"  mean:   {winner_full['model_rank'].mean():.2f}")
    print(f"  median: {desc_rank['50%']:.1f}")
    print(f"  Q1:     {desc_rank['25%']:.1f}")
    print(f"  Q3:     {desc_rank['75%']:.1f}")
    print(f"\n  Full rank distribution (top 8 + rest):")
    rank_counts = winner_full["model_rank"].value_counts().sort_index()
    for r, c in rank_counts.items():
        if r <= 8:
            print(f"    rank {r}: {c:5d}  ({c/len(winner_full)*100:.1f}%)")
    rest = rank_counts[rank_counts.index > 8].sum()
    if rest:
        print(f"    rank 9+: {rest:5d}  ({rest/len(winner_full)*100:.1f}%)")


if __name__ == "__main__":
    run()
