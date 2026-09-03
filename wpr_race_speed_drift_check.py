"""
wpr_race_speed_drift_check.py - follow-up to the pred_tr/pred_te
requantile fix: fixing that mismatch corrected the label split cleanly
on the 6-month held-out period it was fit on (Hot 34.5%/Fast 30.2%/Even
25.0%/Slow 10.3%, matching the ~35/30/25/10% design intent), but
checking the MOST RECENT 1,500 races specifically still shows a real
skew (Hot 51%/Fast 29%/Even 15%/Slow 5%) - barely different from before
the fix. That points at a second, separate issue: temporal drift WITHIN
the held-out period itself, not just a train-vs-test mismatch.

Tests this directly: scores held-out races (2026-03-01 onward) in
monthly buckets and reports each month's own predicted_rse distribution,
to see whether there's a genuine upward trend over time (which would
mean a single static calibration can never represent "right now" well,
however it's fit) or whether the "last 1,500" sample is just an
unrepresentative/noisy slice.

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np
import pandas as pd

import race_speed_estimate as rse

TEST_CUTOFF = "2026-03-01"


def run():
    print("Loading model + form history...")
    rse._load_model()
    fh = rse._load_and_prep_form()
    fh = fh.dropna(subset=["track", "raceNumber", "raceShapeEarly"])
    fh["race_key"] = (fh["track"].astype(str) + "|" + fh["date"].astype(str)
                      + "|" + fh["raceNumber"].astype(str))

    race_meta = (fh.groupby("race_key")
                   .agg(date=("date", "first"), n=("horse_lc", "count"))
                   .reset_index())
    race_meta = race_meta[race_meta["n"] >= 4]
    test_races = race_meta[race_meta["date"] >= pd.Timestamp(TEST_CUTOFF)].copy()
    test_races["month"] = test_races["date"].dt.to_period("M")
    print(f"Held-out races: {len(test_races):,}, months: {sorted(test_races['month'].unique())}")

    fh_by_race = fh.groupby("race_key")
    pmeans_by_date = {}
    rows = []
    for i, (_, r) in enumerate(test_races.iterrows()):
        if i % 1500 == 0:
            print(f"  ... {i}/{len(test_races)}")
        day = r["date"].normalize()
        if day not in pmeans_by_date:
            pmeans_by_date[day] = rse._prior_means(fh, day)
        runners = fh_by_race.get_group(r["race_key"])
        try:
            res = rse.estimate_race_speed(runners, r["date"], fh, pmeans=pmeans_by_date[day])
        except Exception:
            continue
        rows.append((r["month"], res["predicted_rse"]))

    df = pd.DataFrame(rows, columns=["month", "predicted_rse"])
    print(f"\nScored {len(df):,} races.\n")
    print(f"{'month':>10} {'n':>6} {'mean':>8} {'median':>8} {'p25':>8} {'p75':>8}")
    for month, g in df.groupby("month"):
        print(f"{str(month):>10} {len(g):>6} {g['predicted_rse'].mean():>8.3f} "
              f"{g['predicted_rse'].median():>8.3f} {g['predicted_rse'].quantile(0.25):>8.3f} "
              f"{g['predicted_rse'].quantile(0.75):>8.3f}")

    print("\nIf mean/median climb steadily month over month, that confirms genuine drift - a single "
          "static calibration (however correctly fit on the aggregate held-out period) will always lag "
          "behind 'right now'.")


if __name__ == "__main__":
    run()
