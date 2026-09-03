"""
wpr_rank_margin_detail_stats.py - detailed rank/margin/place stats for
the model's top pick AND the market favourite, side by side, follow-up
to wpr_rank_hitrate_vs_market_favourite.py's headline numbers. For each
of the two ranking systems (model by projected_wpr, market by price/
implied probability), reports:
  1. Win rate and place rate (top 2/top 3 finish) of the #1 ranked
     runner.
  2. Win rate broken down by the #1-to-#2 gap (WPR points for the
     model, implied-probability points for the market - different
     units, same idea: does a bigger gap between the top two actually
     predict a higher win rate).
  3. Cumulative hit rate: how often the winner falls within the top-K
     ranked runners (K=1..5).
  4. avg/median/Q1/Q3 of the margin from the winner's own score up to
     the #1 ranked runner's score (0 when the winner IS the #1 pick) -
     WPR points for the model, probability points for the market.
  5. avg/median/Q1/Q3 of the winner's own rank in each ordering.

Reuses the cached full-history projected population (see wpr_
calibrated_edge_kfold_validation.build_pool) - rebuilds (~15 min) only
if a relevant file changed since the last cache; otherwise loads
instantly.

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np
import pandas as pd

from wpr_calibrated_edge_kfold_validation import build_pool

MIN_FIELD_SIZE = 4


def market_prob(pool):
    def _probs(g):
        inv = 1.0 / g["price"].to_numpy(dtype=float)
        return pd.Series(inv / inv.sum(), index=g.index)
    return pool.groupby("race_id", group_keys=False).apply(_probs)


def report_for_ranking(pool, rank_col, score_col, label, gap_bins, gap_labels, unit_label):
    top1 = pool[pool[rank_col] == 1].copy()
    win_rate = top1["won"].mean() * 100
    place2_rate = (top1["finish_position"] <= 2).mean() * 100
    place3_rate = (top1["finish_position"] <= 3).mean() * 100
    print(f"\n{'='*90}\n{label}: #1 PICK WIN AND PLACE RATE (n={len(top1):,} races)\n{'='*90}")
    print(f"  Wins (finishes 1st):        {win_rate:.1f}%")
    print(f"  Places top 2 (1st or 2nd):  {place2_rate:.1f}%")
    print(f"  Places top 3 (1st-3rd):     {place3_rate:.1f}%")

    rank2 = pool[pool[rank_col] == 2][["race_id", score_col]].rename(columns={score_col: "score_r2"})
    top1g = top1.merge(rank2, on="race_id", how="inner")
    top1g["gap"] = top1g[score_col] - top1g["score_r2"]
    top1g["gap_bucket"] = pd.cut(top1g["gap"], bins=gap_bins, labels=gap_labels, include_lowest=True)
    print(f"\n{label}: #1 PICK WIN RATE BY GAP TO #2 ({unit_label})")
    g = top1g.groupby("gap_bucket", observed=True).agg(n=("won", "size"), win_rate=("won", "mean"))
    g["win_rate"] = g["win_rate"] * 100
    print(g.to_string(formatters={"win_rate": "{:.1f}%".format}))

    winners = pool[pool["won"] == 1][["race_id", rank_col]].rename(columns={rank_col: "winner_rank"})
    print(f"\n{label}: CUMULATIVE HIT RATE (winner within top-K, n={len(winners):,} races)")
    for k in [1, 2, 3, 4, 5]:
        pct = (winners["winner_rank"] <= k).mean() * 100
        print(f"  top {k}: {pct:.1f}%")

    top1s = top1[["race_id", score_col]].rename(columns={score_col: "score_top1"})
    winner_full = pool[pool["won"] == 1][["race_id", score_col, rank_col]].merge(top1s, on="race_id", how="inner")
    winner_full["margin_to_top1"] = winner_full["score_top1"] - winner_full[score_col]
    desc = winner_full["margin_to_top1"].describe(percentiles=[0.25, 0.5, 0.75])
    print(f"\n{label}: MARGIN ({unit_label}) - winner's own score UP TO the #1 pick's score "
          f"(n={len(winner_full):,})")
    print(f"  mean={winner_full['margin_to_top1'].mean():.3f}  median={desc['50%']:.3f}  "
          f"Q1={desc['25%']:.3f}  Q3={desc['75%']:.3f}")

    desc_rank = winner_full[rank_col].describe(percentiles=[0.25, 0.5, 0.75])
    print(f"\n{label}: WINNER'S RANK (1 = #1 pick)")
    print(f"  mean={winner_full[rank_col].mean():.2f}  median={desc_rank['50%']:.1f}  "
          f"Q1={desc_rank['25%']:.1f}  Q3={desc_rank['75%']:.1f}")

    return {"win_rate": win_rate, "place2": place2_rate, "place3": place3_rate,
            "top1_hit": (winners["winner_rank"] <= 1).mean() * 100,
            "top4_hit": (winners["winner_rank"] <= 4).mean() * 100,
            "margin_median": desc["50%"], "margin_mean": winner_full["margin_to_top1"].mean(),
            "rank_median": desc_rank["50%"], "rank_mean": winner_full[rank_col].mean()}


def run():
    pool = build_pool()
    field_size = pool.groupby("race_id")["proj"].transform("size")
    pool = pool[field_size >= MIN_FIELD_SIZE].copy()
    print(f"Population: {len(pool):,} runners across {pool['race_id'].nunique():,} eligible races "
          f"(field>={MIN_FIELD_SIZE}, every runner projected)")

    pool["model_rank"] = pool.groupby("race_id")["proj"].rank(ascending=False, method="first").astype(int)
    pool["market_rank"] = pool.groupby("race_id")["price"].rank(ascending=True, method="first").astype(int)
    pool["market_prob"] = market_prob(pool)
    pool["finish_position"] = pd.to_numeric(pool["finish_position"], errors="coerce")

    model_bins = [0, 1, 2, 3, 5, 8, float("inf")]
    model_labels = ["0-1", "1-2", "2-3", "3-5", "5-8", "8+"]
    model_stats = report_for_ranking(pool, "model_rank", "proj", "MODEL",
                                       model_bins, model_labels, "WPR points")

    market_bins = [0, 0.02, 0.05, 0.10, 0.20, 0.35, 1.0]
    market_labels = ["0-2pp", "2-5pp", "5-10pp", "10-20pp", "20-35pp", "35pp+"]
    market_stats = report_for_ranking(pool, "market_rank", "market_prob", "MARKET FAVOURITE",
                                        market_bins, market_labels, "implied-probability points")

    print(f"\n{'='*90}\nSIDE-BY-SIDE SUMMARY: MODEL'S #1 PICK vs MARKET FAVOURITE\n{'='*90}")
    print(f"{'metric':<38}{'model':>15}{'market':>15}")
    print(f"{'Win rate':<38}{model_stats['win_rate']:>14.1f}%{market_stats['win_rate']:>14.1f}%")
    print(f"{'Place top 2':<38}{model_stats['place2']:>14.1f}%{market_stats['place2']:>14.1f}%")
    print(f"{'Place top 3':<38}{model_stats['place3']:>14.1f}%{market_stats['place3']:>14.1f}%")
    print(f"{'Winner in top 1 (=win rate)':<38}{model_stats['top1_hit']:>14.1f}%{market_stats['top1_hit']:>14.1f}%")
    print(f"{'Winner in top 4':<38}{model_stats['top4_hit']:>14.1f}%{market_stats['top4_hit']:>14.1f}%")
    print(f"{'Winner rank, median':<38}{model_stats['rank_median']:>15.1f}{market_stats['rank_median']:>15.1f}")
    print(f"{'Winner rank, mean':<38}{model_stats['rank_mean']:>15.2f}{market_stats['rank_mean']:>15.2f}")
    print(f"{'Margin to #1 pick, median':<38}{model_stats['margin_median']:>13.2f} pt{market_stats['margin_median']*100:>12.2f} pp")
    print(f"{'Margin to #1 pick, mean':<38}{model_stats['margin_mean']:>13.2f} pt{market_stats['margin_mean']*100:>12.2f} pp")
    print("\n(pt = WPR points, pp = implied-probability percentage points - different units, not directly")
    print("comparable in magnitude, only in relative shape/direction)")


if __name__ == "__main__":
    run()
