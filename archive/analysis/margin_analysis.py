"""
Margin Analysis - WPR Predictions vs Actual Finishing Margins
==============================================================
Two questions about the model's margin performance on resulted races:

  A) When the model's predicted top pick does NOT win - how close was
     it? And when it DOES win, by how much?
     Practical view: "did it nearly win" / "by how much."

  B) Calibration: does a predicted WPR gap translate into actual
     finishing margin the way "2 WPR ~= 1 length" implies?
     Honest view: are the model's WPR numbers calibrated as lengths.

CAVEATS up front (these are real):

  - "2 WPR = 1 length" is a rough heuristic, not a constant. It varies
    with distance, going (heavy stretches margins), and how the margin
    was measured. The calibration test uses 2 WPR/length but the result
    is approximate by construction.
  - Sample size on this dataset is small. Direction is informative,
    exact numbers will move on a larger sample.
  - margin_finish's own sign convention is not "0 for the winner, positive
    for the beaten" - the winner's row commonly carries a NEGATIVE value
    (their winning margin, sign-inverted). Both parts below anchor every
    runner's margin to their own race's winner (see behind_winner) instead
    of trusting the raw column's sign. A prior version of this script
    filtered out margin_finish < 0, which silently deleted most winning
    rows and made the top-pick win rate look like ~0.3% instead of the
    real ~25-27%. Fixed; kept here as a warning against re-adding that
    filter.

Descriptive only. No model or dashboard change is made by this script.

Run from the TopRate directory: python margin_analysis.py
"""

import sys
import numpy as np
import pandas as pd

RUNNERS_CSV = "toprate_runners.csv"
WPR_PER_LENGTH = 2.0   # heuristic, see caveats above

# Margin column candidates - script auto-finds.
MARGIN_CANDIDATES = [
    "margin", "margin_finish", "marginFinish", "winning_margin",
    "finish_margin", "beaten_margin", "marginToWinner",
    "margin_to_winner", "margin_lengths",
]


def find_col(df, candidates):
    for c in candidates:
        if c in df.columns:
            return c
    return None


def pct(arr, p):
    return float(np.percentile(arr, p)) if len(arr) else float("nan")


def main():
    try:
        df = pd.read_csv(RUNNERS_CSV,
                         dtype={"run_id": str, "race_id": str},
                         low_memory=False)
    except FileNotFoundError:
        print(f"Could not find {RUNNERS_CSV}. Run from the TopRate directory.")
        sys.exit(1)

    rank_col = find_col(df, ["wprp_rank", "wpr_rank"])
    proj_col = find_col(df, ["wprp_proj", "wpr_projection", "wprp", "wpjp"])
    finish_col = find_col(df, ["finish_position", "finish", "position_finish",
                                "positionFinish"])
    margin_col = find_col(df, MARGIN_CANDIDATES)
    resulted_col = find_col(df, ["resulted"])

    missing = []
    if rank_col is None: missing.append("rank (wprp_rank/wpr_rank)")
    if proj_col is None: missing.append("projection (wprp_proj/etc)")
    if finish_col is None: missing.append("finish position")
    if margin_col is None: missing.append("margin (from " +
                                          ", ".join(MARGIN_CANDIDATES) + ")")
    if missing:
        print("Missing columns:")
        for m in missing:
            print(f"   - {m}")
        print()
        print("Available columns containing 'margin' or 'finish':")
        for c in df.columns:
            cl = c.lower()
            if "margin" in cl or "finish" in cl or "wpr" in cl:
                print(f"   {c}")
        sys.exit(1)

    print(f"Using columns: rank='{rank_col}', proj='{proj_col}', "
          f"finish='{finish_col}', margin='{margin_col}'")
    if resulted_col:
        print(f"Filtering to resulted races via '{resulted_col}'")
    print()

    for c in [rank_col, proj_col, finish_col, margin_col]:
        df[c] = pd.to_numeric(df[c], errors="coerce")
    if resulted_col:
        df[resulted_col] = pd.to_numeric(df[resulted_col], errors="coerce")
        df = df[df[resulted_col] == 1]

    # 99 / 99.9 is a null/DNF sentinel in this data, not a real 90+ length
    # margin (confirmed: only a handful of rows, all exactly at that value).
    df = df[df[margin_col] < 90]

    df = df.dropna(subset=[rank_col, proj_col, finish_col,
                            margin_col, "race_id"])
    df = df[df[finish_col] > 0]
    df = df[df[rank_col] > 0]

    # margin_col is NOT "0 for the winner, positive for the beaten" - the
    # winner's own row commonly carries a NEGATIVE value (their winning
    # margin, sign-inverted), which the old `>= 0` filter here dropped,
    # silently deleting most winning rows before Part A even counted wins
    # (this was the bug: it made top-pick win rate look like ~0.3% when the
    # real number is ~25%). Fix: anchor every runner's margin to their OWN
    # race's winner. Subtracting the winner's raw value per race gives a
    # clean "lengths behind the winner" column (0 for the winner, >=0 for
    # everyone else) regardless of whatever sign convention the raw column
    # uses on any given row.
    winner_raw = (df[df[finish_col] == 1]
                  .drop_duplicates(subset="race_id")
                  .set_index("race_id")[margin_col])
    df["_winner_raw"] = df["race_id"].map(winner_raw)
    df = df.dropna(subset=["_winner_raw"])
    df["behind_winner"] = df[margin_col] - df["_winner_raw"]
    # small negative residuals are measurement noise (photo finishes /
    # timing rounding) - clip to 0. Meaningfully negative means a runner is
    # recorded as literally ahead of the winner, a genuine data problem for
    # that specific race - drop only those rows.
    df = df[df["behind_winner"] > -0.5]
    df["behind_winner"] = df["behind_winner"].clip(lower=0.0)

    print(f"Usable runner-rows: {len(df):,}")
    print(f"Races available: {df['race_id'].nunique():,}")
    if len(df) == 0:
        print("No data after filters - nothing to analyse.")
        sys.exit(0)

    # ────────────────────────────────────────────────────────────────
    # A) Top-pick margin distributions
    # ────────────────────────────────────────────────────────────────
    top_pick_margins_when_loss = []   # margin behind winner when top pick lost
    top_pick_margins_when_won = []    # winning margin when top pick won
    top_pick_wins = 0
    top_pick_losses = 0

    for rid, g in df.groupby("race_id"):
        if len(g) < 4:
            continue
        g_ranked = g[g[rank_col].notna()].copy()
        if len(g_ranked) < 4:
            continue
        g_ranked["pred_rank"] = g_ranked[rank_col].rank(
            ascending=True, method="min")
        top = g_ranked[g_ranked["pred_rank"] == 1]
        if len(top) != 1:
            continue
        top_finish = int(top[finish_col].iloc[0])
        if top_finish == 1:
            top_pick_wins += 1
            # winning margin = the closest chaser's gap behind the winner
            others = g.loc[g[finish_col] != 1, "behind_winner"]
            if len(others):
                top_pick_margins_when_won.append(float(others.min()))
        else:
            top_pick_losses += 1
            top_pick_margins_when_loss.append(float(top["behind_winner"].iloc[0]))

    print("=" * 64)
    print("A) TOP-PICK MARGIN DISTRIBUTIONS")
    print("=" * 64)
    print(f"Top-pick wins:   {top_pick_wins:,}")
    print(f"Top-pick losses: {top_pick_losses:,}")
    print()
    if top_pick_margins_when_won:
        arr = top_pick_margins_when_won
        print(f"When top pick WINS, winning margin (lengths):")
        print(f"   mean   {np.mean(arr):.2f}   median {np.median(arr):.2f}   "
              f"P25 {pct(arr,25):.2f}   P75 {pct(arr,75):.2f}")
    if top_pick_margins_when_loss:
        arr = top_pick_margins_when_loss
        print(f"When top pick LOSES, beaten margin behind winner (lengths):")
        print(f"   mean   {np.mean(arr):.2f}   median {np.median(arr):.2f}   "
              f"P25 {pct(arr,25):.2f}   P75 {pct(arr,75):.2f}")
        # "nearly won" share - within 1 length of winner
        within_1 = sum(1 for m in arr if m <= 1.0)
        within_2 = sum(1 for m in arr if m <= 2.0)
        within_3 = sum(1 for m in arr if m <= 3.0)
        print(f"   within 1.0L of winner: {within_1:,}/{len(arr):,} "
              f"({100*within_1/len(arr):.0f}%)")
        print(f"   within 2.0L of winner: {within_2:,}/{len(arr):,} "
              f"({100*within_2/len(arr):.0f}%)")
        print(f"   within 3.0L of winner: {within_3:,}/{len(arr):,} "
              f"({100*within_3/len(arr):.0f}%)")
    print()

    # ────────────────────────────────────────────────────────────────
    # B) WPR-gap vs actual-margin calibration (across all pairs)
    # ────────────────────────────────────────────────────────────────
    pred_gaps = []   # lengths, from |wpr_a - wpr_b| / WPR_PER_LENGTH
    actual_gaps = [] # lengths, from |margin_a - margin_b|

    for rid, g in df.groupby("race_id"):
        if len(g) < 4:
            continue
        # use all runners with both a projection and a margin
        vals = g[[proj_col, "behind_winner"]].dropna().to_numpy()
        n = len(vals)
        if n < 4:
            continue
        for i in range(n):
            for j in range(i + 1, n):
                pred_gap_len = abs(vals[i, 0] - vals[j, 0]) / WPR_PER_LENGTH
                actual_gap_len = abs(vals[i, 1] - vals[j, 1])
                pred_gaps.append(pred_gap_len)
                actual_gaps.append(actual_gap_len)

    pg = np.array(pred_gaps)
    ag = np.array(actual_gaps)

    print("=" * 64)
    print("B) WPR-GAP vs ACTUAL-MARGIN CALIBRATION")
    print("   (predicted gap = |WPR diff| / 2 lengths)")
    print("=" * 64)
    print(f"Pairs analysed: {len(pg):,}")
    print()
    print(f"Predicted gap (lengths):   mean {pg.mean():.2f}   "
          f"median {np.median(pg):.2f}")
    print(f"Actual margin gap (lengths): mean {ag.mean():.2f}   "
          f"median {np.median(ag):.2f}")
    print()
    # global correlation across pairs
    if len(pg) > 1:
        corr = float(np.corrcoef(pg, ag)[0, 1])
        print(f"Correlation (predicted vs actual gap): {corr:+.3f}")
    print()

    # buckets - within each predicted-gap bucket, what was the mean
    # actual margin? Tells us whether the model's predictions track
    # the real margins or systematically over/under shoot.
    print("Calibration table - predicted-gap bucket vs actual margin:")
    print(f"   {'pred-gap':>14s}  {'n':>7s}  {'pred mean':>10s}  "
          f"{'actual mean':>12s}  {'diff':>7s}")
    edges = [0, 0.5, 1.0, 2.0, 3.0, 5.0, 8.0, 12.0, 100.0]
    labels = []
    for i in range(len(edges) - 1):
        lo, hi = edges[i], edges[i + 1]
        mask = (pg >= lo) & (pg < hi)
        n = int(mask.sum())
        if n < 20:
            continue
        pm = pg[mask].mean()
        am = ag[mask].mean()
        diff = am - pm
        lbl = f"{lo:>4.1f} - {hi:<5.1f}L"
        print(f"   {lbl:>14s}  {n:>7d}  {pm:>10.2f}  "
              f"{am:>12.2f}  {diff:>+7.2f}")
    print()
    print("Read: 'diff' is actual minus predicted. Negative means the")
    print("model predicted a larger gap than the horses finished apart;")
    print("positive means the field spread out more than predicted.")
    print()
    print("Reminders:")
    print("  - 2 WPR per length is a HEURISTIC, not a constant. Varies with")
    print("    distance, going, and how margins were measured.")
    print("  - Small sample. Direction is informative, exact numbers will")
    print("    move on a larger sample.")
    print("  - Descriptive only. No model or dashboard change.")


if __name__ == "__main__":
    main()
