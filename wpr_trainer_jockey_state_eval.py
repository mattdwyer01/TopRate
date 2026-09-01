"""
wpr_trainer_jockey_state_eval.py - follow-up to
wpr_trainer_jockey_adj_strike_eval.py (which validated trainer_merit/
jockey_merit as production ADJ_TERMs, now shipped). This checks whether a
STATE-CONDITIONED version of those two terms would be worth building: does
trainer/jockey trailing win-rate carry meaningfully different predictive
power in different states, with enough volume in each to trust the
difference, or is the earlier state-by-state AUC spread (WA a standout at
0.662/0.651 vs overall 0.636/0.632; TAS/ACT higher still but tiny samples,
n=1056/n=493) mostly noise?

METHODOLOGY: same population-fitted decile-bucket lookup as the production
term (see wpr_trainer_jockey_adj_strike_eval.py's fit_bucket_lookup/
apply_bucket), fit and evaluated PER STATE rather than nationally, on the
same H1/H2 chronological split. Reports per-state row counts (fit and
held-out) alongside the both-directions strike-rate comparison so a
result backed by too little volume is visible as such, not just a number.

USAGE
  python wpr_trainer_jockey_state_eval.py

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np
import pandas as pd

import wpr_projection as wpr
from wpr_own_pace_backtest import add_base, add_track_barrier, merge_won_by_horse_date
from wpr_trainer_jockey_adj_strike_eval import (
    FORM_CSV, merge_trainer_jockey_by_horse_date, add_closing_merit,
    fit_bucket_lookup, apply_bucket, top1_strike_rate, proj_of,
)

MIN_STATE_ROWS = 300  # per half, per state - below this a decile fit is noise


def merge_state(D, runners_csv="toprate_runners.csv"):
    tr = pd.read_csv(runners_csv, low_memory=False, usecols=["horse", "date", "state"])
    tr["date"] = pd.to_datetime(tr["date"], errors="coerce")
    tr = tr.dropna(subset=["date"])
    tr = tr.drop_duplicates(subset=["horse", "date"], keep=False)
    return D.merge(tr, on=["horse", "date"], how="inner")


def run():
    print("Rebuilding training frame...")
    full = wpr.build_training_frame(FORM_CSV, verbose=True, n_jobs=-1)
    full["date"] = pd.to_datetime(full["date"])

    print("\nMerging race result, trainer/jockey win-rate, and state "
          "from toprate_runners.csv by (horse, date)...")
    full = merge_won_by_horse_date(full)
    full = merge_trainer_jockey_by_horse_date(full)
    full = merge_state(full)

    full = add_base(full)
    non_tb_terms = [t for t in wpr.ADJ_TERMS if t not in ("track_barrier", "closing_merit")]
    full = full.dropna(subset=["target", "_base", "career_avg"] + non_tb_terms +
                        ["barrier", "field_size", "track", "cur_distance",
                         "trainer_win_pct_365d", "jockey_win_pct_90d", "state"])
    print(f"\nScoped rows: {len(full):,}")

    mid = full["date"].quantile(0.5)
    h1, h2 = full[full["date"] < mid].copy(), full[full["date"] >= mid].copy()
    print(f"H1: {len(h1):,} rows (< {mid.date()}), H2: {len(h2):,} rows (>= {mid.date()})")

    states = sorted(full["state"].dropna().unique())
    print(f"\nStates present: {states}")

    print(f"\n{'state':6} {'h1_n':>7} {'h2_n':>7}  "
          f"{'base_h2%':>9} {'both_h2%':>9} {'delta':>7}  "
          f"{'base_h1%':>9} {'both_h1%':>9} {'delta':>7}  verdict")
    for st in states:
        h1_s = h1[h1["state"] == st].copy()
        h2_s = h2[h2["state"] == st].copy()
        if len(h1_s) < MIN_STATE_ROWS or len(h2_s) < MIN_STATE_ROWS:
            print(f"{st:6} {len(h1_s):>7} {len(h2_s):>7}  "
                  f"{'-':>9} {'-':>9} {'-':>7}  {'-':>9} {'-':>9} {'-':>7}  "
                  f"skipped (< {MIN_STATE_ROWS}/half)")
            continue

        # direction 1: fit on H1(state), validate on H2(state)
        h1_d1, h2_d1 = h1_s.copy(), h2_s.copy()
        add_track_barrier(h1_d1, [h1_d1, h2_d1])
        add_closing_merit([h1_d1, h2_d1], h1_s["date"].max())
        et, lt = fit_bucket_lookup(h1_d1, "trainer_win_pct_365d")
        ej, lj = fit_bucket_lookup(h1_d1, "jockey_win_pct_90d")
        for f in (h1_d1, h2_d1):
            apply_bucket(f, "trainer_win_pct_365d", et, lt, "trainer_merit")
            apply_bucket(f, "jockey_win_pct_90d", ej, lj, "jockey_merit")
            f["proj_base"] = proj_of(f, [])
            f["proj_both"] = proj_of(f, ["trainer_merit", "jockey_merit"])
        b_r2, _, _ = top1_strike_rate(h2_d1, "proj_base")
        c_r2, _, _ = top1_strike_rate(h2_d1, "proj_both")

        # direction 2: fit on H2(state), validate on H1(state)
        h1_d2, h2_d2 = h1_s.copy(), h2_s.copy()
        add_track_barrier(h2_d2, [h1_d2, h2_d2])
        add_closing_merit([h1_d2, h2_d2], h2_s["date"].max())
        et2, lt2 = fit_bucket_lookup(h2_d2, "trainer_win_pct_365d")
        ej2, lj2 = fit_bucket_lookup(h2_d2, "jockey_win_pct_90d")
        for f in (h1_d2, h2_d2):
            apply_bucket(f, "trainer_win_pct_365d", et2, lt2, "trainer_merit")
            apply_bucket(f, "jockey_win_pct_90d", ej2, lj2, "jockey_merit")
            f["proj_base"] = proj_of(f, [])
            f["proj_both"] = proj_of(f, ["trainer_merit", "jockey_merit"])
        b_r1, _, _ = top1_strike_rate(h1_d2, "proj_base")
        c_r1, _, _ = top1_strike_rate(h1_d2, "proj_both")

        both_improved = (c_r2 > b_r2) and (c_r1 > b_r1)
        verdict = "clears both directions" if both_improved else "does not clear"
        print(f"{st:6} {len(h1_s):>7} {len(h2_s):>7}  "
              f"{b_r2:>8.2f}% {c_r2:>8.2f}% {c_r2-b_r2:>+6.2f}  "
              f"{b_r1:>8.2f}% {c_r1:>8.2f}% {c_r1-b_r1:>+6.2f}  {verdict}")

    print("\nDone. A state clearing both directions AND meeting the row-count "
          "floor is the bar for a state-conditioned lookup being worth building; "
          "anything below MIN_STATE_ROWS is reported for visibility only, not "
          "as evidence either way.")


if __name__ == "__main__":
    run()
