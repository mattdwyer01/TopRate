"""
wpr_rejected_candidates_strike_recheck.py - re-checks every ADJ_TERMS
candidate this codebase already tested and rejected PURELY on held-out
MAE, against TOP-1 STRIKE RATE instead - the metric this session
established actually matters for the user's goal, and which this
session's own closing_merit/gear_change findings proved can point in a
DIFFERENT direction than MAE (both hurt MAE while genuinely improving
strike rate).

WHY THIS EXISTS
  wpr_projection.py's build_features() already computes 14 own-history
  candidates that were tried and rejected - each one "TESTED, NOT
  ADOPTED" per its own comment, decided on held-out MAE alone, still
  emitted in the feats dict ("harmless, informative") even though none
  are summed into ADJ_TERMS:
    own_third_up, own_fourth_up, own_fifth_up, own_barrier (the
    own-history version, distinct from the adopted population-level
    track_barrier), own_settle, own_track_distance, own_recent_trend,
    own_settle_distance, own_settle_barrier, own_distance_barrier,
    own_settle_distance_barrier, own_wet, own_dry, firstup_wpr.
  None of these were ever checked against strike rate specifically -
  they may have been correctly rejected for MAE while still carrying
  real ranking information (a small, real shift in the right direction
  for SOME races, even if it makes the point estimate noisier overall).

METHODOLOGY: same bar as every other candidate this session - one
build_training_frame() call (no race_speed_labels needed, these are all
already-computed columns), corrected won merge (see
merge_won_by_horse_date), track_barrier + base built per chronological
direction, top-1 strike rate AND MAE compared for baseline (7 terms) vs
baseline+ONE candidate, both directions, for every candidate in one pass
(cheap once the frame is built - no per-candidate rebuild needed).

USAGE
  python wpr_rejected_candidates_strike_recheck.py

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np
import pandas as pd
from sklearn.metrics import mean_absolute_error

import wpr_projection as wpr
from wpr_own_pace_backtest import add_base, add_track_barrier, merge_won_by_horse_date

FORM_CSV = "wpr_form_history.csv.gz"
CANDIDATES = [
    "own_third_up", "own_fourth_up", "own_fifth_up", "own_barrier",
    "own_settle", "own_track_distance", "own_recent_trend",
    "own_settle_distance", "own_settle_barrier", "own_distance_barrier",
    "own_settle_distance_barrier", "own_wet", "own_dry", "firstup_wpr",
]


def top1_strike_rate(frame, proj_col):
    f = frame.copy()
    f["rank"] = f.groupby("race_id")[proj_col].rank(ascending=False, method="first")
    top1 = f[f["rank"] == 1]
    return float(top1["won"].mean() * 100), int(top1["won"].sum()), len(top1)


def proj_of(frame, extra_terms):
    terms = list(wpr.ADJ_TERMS) + extra_terms
    return frame["_base"].to_numpy() + wpr._cap_adj_sum(frame[terms].to_numpy()).sum(axis=1)


def run():
    print("Rebuilding training frame (no race_speed_labels needed - all 14 "
          "candidates are already computed by build_features)...")
    full = wpr.build_training_frame(FORM_CSV, verbose=True, n_jobs=-1)
    full["date"] = pd.to_datetime(full["date"])

    print("\nMerging race result (won) from toprate_runners.csv by (horse_id, date)...")
    full = merge_won_by_horse_date(full)

    full = add_base(full)
    non_tb_terms = [t for t in wpr.ADJ_TERMS if t != "track_barrier"]
    present = [c for c in CANDIDATES if c in full.columns]
    missing = [c for c in CANDIDATES if c not in full.columns]
    if missing:
        print(f"WARNING: not found in training frame, skipping: {missing}")
    full = full.dropna(subset=["target", "_base", "career_avg"] + non_tb_terms +
                        ["barrier", "field_size", "track", "cur_distance"] + present)
    print(f"Scoped rows: {len(full):,} ({full['race_id'].nunique():,} races)")

    mid = full["date"].quantile(0.5)
    h1, h2 = full[full["date"] < mid].copy(), full[full["date"] >= mid].copy()
    print(f"H1: {len(h1):,} rows (< {mid.date()}), H2: {len(h2):,} rows (>= {mid.date()})")

    h1_d1, h2_d1 = h1.copy(), h2.copy()
    add_track_barrier(h1_d1, [h1_d1, h2_d1])
    h1_d2, h2_d2 = h1.copy(), h2.copy()
    add_track_barrier(h2_d2, [h1_d2, h2_d2])

    h1_d1["proj_base"] = proj_of(h1_d1, [])
    h2_d1["proj_base"] = proj_of(h2_d1, [])
    h1_d2["proj_base"] = proj_of(h1_d2, [])
    h2_d2["proj_base"] = proj_of(h2_d2, [])
    b_r1, b_k1, b_n1 = top1_strike_rate(h1_d1, "proj_base")
    b_r2, b_k2, b_n2 = top1_strike_rate(h2_d1, "proj_base")
    b_r2b, b_k2b, b_n2b = top1_strike_rate(h2_d2, "proj_base")
    b_r1b, b_k1b, b_n1b = top1_strike_rate(h1_d2, "proj_base")
    b_mae2 = mean_absolute_error(h2_d1["target"], h2_d1["proj_base"])
    b_mae1 = mean_absolute_error(h1_d2["target"], h1_d2["proj_base"])
    print(f"\nBaseline (7 terms): H1-fit/H2-val = {b_r1:.2f}%->{b_r2:.2f}% (MAE {b_mae2:.4f}), "
          f"H2-fit/H1-val = {b_r2b:.2f}%->{b_r1b:.2f}% (MAE {b_mae1:.4f})")

    print(f"\n{'candidate':>28s} | {'nonzero%':>8s} | {'H2 strike (held-out)':>22s} | "
          f"{'H1 strike (held-out)':>22s} | {'both improve?':>14s}")
    results = []
    for cand in present:
        h1_d1[f"proj_{cand}"] = proj_of(h1_d1, [cand])
        h2_d1[f"proj_{cand}"] = proj_of(h2_d1, [cand])
        h1_d2[f"proj_{cand}"] = proj_of(h1_d2, [cand])
        h2_d2[f"proj_{cand}"] = proj_of(h2_d2, [cand])

        c_r2, c_k2, c_n2 = top1_strike_rate(h2_d1, f"proj_{cand}")
        c_r1b, c_k1b, c_n1b = top1_strike_rate(h1_d2, f"proj_{cand}")
        c_mae2 = mean_absolute_error(h2_d1["target"], h2_d1[f"proj_{cand}"])
        c_mae1 = mean_absolute_error(h1_d2["target"], h1_d2[f"proj_{cand}"])

        nonzero = (full[cand] != 0.0).mean() * 100
        strike_both = (c_r2 > b_r2) and (c_r1b > b_r1b)
        mae_both = (c_mae2 < b_mae2) and (c_mae1 < b_mae1)
        flag = "STRIKE+MAE" if (strike_both and mae_both) else \
               "STRIKE ONLY" if strike_both else \
               "MAE ONLY" if mae_both else ""
        print(f"{cand:>28s} | {nonzero:7.1f}% | "
              f"{b_r2:6.2f}%->{c_r2:6.2f}%{'  ok' if c_r2 > b_r2 else '  no':>6s} | "
              f"{b_r1b:6.2f}%->{c_r1b:6.2f}%{'  ok' if c_r1b > b_r1b else '  no':>6s} | "
              f"{flag:>14s}")
        results.append((cand, nonzero, b_r2, c_r2, b_r1b, c_r1b, strike_both, mae_both))

    winners = [r for r in results if r[6]]
    print(f"\n{len(winners)}/{len(results)} candidates improve top-1 strike rate in BOTH "
          f"held-out directions:")
    for r in winners:
        print(f"  {r[0]}: H2 {r[2]:.2f}%->{r[3]:.2f}%, H1 {r[4]:.2f}%->{r[5]:.2f}% "
              f"(MAE also improved both ways: {r[7]})")
    if not winners:
        print("  (none)")


if __name__ == "__main__":
    run()
