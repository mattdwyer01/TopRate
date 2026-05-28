"""
Rank-vs-Finish Analysis
========================
Honestly answers: how well does the model's PRE-RACE projected WPR-rank
line up with the actual finishing order on resulted races?

This is the practical question for a punter: "if I trust the model's
ranking, how often is the top pick actually best?" - separate from the
~6 WPR mean absolute error on the projection itself, which is about
absolute rating, not order.

Uses toprate_runners.csv. Looks for:
  - wprp_rank  : the model's projected WPR rank (1 = top pick)
  - finish_position (or 'finish' / 'position_finish' - script auto-finds)
  - race_id
  - resulted flag (skip non-resulted races)

Run from the TopRate directory: python rank_vs_finish_analysis.py

NOTE: this is descriptive only. No model or dashboard change is made.
"""

import sys
import numpy as np
import pandas as pd
try:
    from scipy.stats import spearmanr
    HAVE_SCIPY = True
except ImportError:
    HAVE_SCIPY = False
    print("(scipy not installed - Spearman correlations skipped)\n")

RUNNERS_CSV = "toprate_runners.csv"


def find_col(df, candidates):
    """Find the first column from candidates that exists in df."""
    for c in candidates:
        if c in df.columns:
            return c
    return None


def main():
    try:
        df = pd.read_csv(RUNNERS_CSV,
                         dtype={"run_id": str, "race_id": str},
                         low_memory=False)
    except FileNotFoundError:
        print(f"Could not find {RUNNERS_CSV}. Run from the TopRate directory.")
        sys.exit(1)

    rank_col = find_col(df, ["wprp_rank", "wpr_rank"])
    finish_col = find_col(df, ["finish_position", "finish", "position_finish",
                                "positionFinish"])
    resulted_col = find_col(df, ["resulted"])

    if rank_col is None:
        print(f"No rank column found in {RUNNERS_CSV}. "
              f"Looked for: wprp_rank, wpr_rank.")
        sys.exit(1)
    if finish_col is None:
        print(f"No finish-position column found. "
              f"Looked for: finish_position, finish, positionFinish.")
        sys.exit(1)

    print(f"Using columns: rank='{rank_col}', finish='{finish_col}'")
    if resulted_col:
        print(f"Filtering to resulted races via '{resulted_col}'")
    print()

    df[rank_col] = pd.to_numeric(df[rank_col], errors="coerce")
    df[finish_col] = pd.to_numeric(df[finish_col], errors="coerce")
    if resulted_col:
        df[resulted_col] = pd.to_numeric(df[resulted_col], errors="coerce")
        df = df[df[resulted_col] == 1]
    df = df.dropna(subset=[rank_col, finish_col, "race_id"])
    df = df[df[finish_col] > 0]
    df = df[df[rank_col] > 0]

    print(f"Usable runner-rows: {len(df):,}")
    print(f"Races available: {df['race_id'].nunique():,}")
    if len(df) == 0:
        print("No data after filters - nothing to analyse.")
        sys.exit(0)

    abs_errs = []
    spearmans = []
    top_pick_won = []
    top_pick_placed = []
    field_sizes = []
    top3_hit_counts = []

    for rid, g in df.groupby("race_id"):
        if len(g) < 4:
            continue
        g = g.copy()
        # actual finish rank within this race (ties get min rank)
        g["finish_rank"] = g[finish_col].rank(ascending=True, method="min")
        # model's projected rank should already be 1..N within the race;
        # re-rank to be safe in case ranks are missing for some runners
        # (e.g. first-starters with no projection).
        g_ranked = g[g[rank_col].notna()].copy()
        if len(g_ranked) < 4:
            continue
        g_ranked["pred_rank"] = g_ranked[rank_col].rank(
            ascending=True, method="min")
        field_sizes.append(len(g_ranked))

        err = (g_ranked["pred_rank"] - g_ranked["finish_rank"]).abs().mean()
        abs_errs.append(err)

        if HAVE_SCIPY and len(g_ranked) >= 3:
            r, _ = spearmanr(g_ranked["pred_rank"], g_ranked["finish_rank"])
            if not np.isnan(r):
                spearmans.append(r)

        # top pick (predicted rank 1): did it win? did it place top-3?
        top_pick = g_ranked[g_ranked["pred_rank"] == 1]
        if len(top_pick) == 1:
            finish = int(top_pick[finish_col].iloc[0])
            top_pick_won.append(1 if finish == 1 else 0)
            top_pick_placed.append(1 if finish <= 3 else 0)

        # top-3 by predicted rank: how many actually finish top-3?
        pred_top3 = set(
            g_ranked[g_ranked["pred_rank"] <= 3][finish_col].astype(int).values)
        hit = len(pred_top3 & {1, 2, 3})
        top3_hit_counts.append(hit)

    n_races = len(abs_errs)
    if n_races == 0:
        print("No races with usable data (need 4+ ranked runners per race).")
        sys.exit(0)

    print()
    print("=" * 64)
    print("RANK PREDICTION vs FINISH ORDER")
    print("=" * 64)
    print(f"Races analysed: {n_races:,}")
    print(f"Mean field size (with ranks): {np.mean(field_sizes):.1f}  "
          f"(median {np.median(field_sizes):.0f})")
    print()
    print(f"RANK MAE (predicted vs actual finish position):")
    print(f"   mean: {np.mean(abs_errs):.2f} positions  "
          f"median: {np.median(abs_errs):.2f}")
    print(f"   interpretation: a typical horse's predicted rank lands")
    print(f"   this many positions off its actual finish.")
    print()
    if HAVE_SCIPY and spearmans:
        print(f"Spearman rank correlation per race:")
        print(f"   mean: {np.mean(spearmans):.3f}  "
              f"median: {np.median(spearmans):.3f}")
        print(f"   (1.0 = perfect order, 0 = random, -1 = inverse)")
        print()
    if top_pick_won:
        avg_fs = np.mean(field_sizes)
        print(f"Top pick (predicted rank 1):")
        print(f"   wins race: {100*np.mean(top_pick_won):.1f}%  "
              f"(random baseline {100/avg_fs:.1f}%)")
        print(f"   places top-3: {100*np.mean(top_pick_placed):.1f}%  "
              f"(random baseline {300/avg_fs:.1f}%)")
        print()
    if top3_hit_counts:
        print(f"Top-3 by predicted rank - how many actually finish top-3:")
        hits = pd.Series(top3_hit_counts).value_counts().sort_index()
        for k in [0, 1, 2, 3]:
            n = hits.get(k, 0)
            pct = 100 * n / len(top3_hit_counts)
            print(f"   {k} of 3 correct: {n:,} races ({pct:.1f}%)")
        print(f"   mean: {np.mean(top3_hit_counts):.2f} of 3")
    print()
    print("Reminder: descriptive only. No model or dashboard change.")


if __name__ == "__main__":
    main()
