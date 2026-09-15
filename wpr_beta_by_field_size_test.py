"""
wpr_beta_by_field_size_test.py - tests whether the wprp_price softmax beta
should vary by field size instead of one global value for every race.

WHY THIS EXISTS (see chat, Sep 2026): calibrate_price_beta.py already
grid-searched ONE global beta against held-out Brier (0.3 -> 0.15, real
improvement, shipped). But a single beta assumes the same "how much win
probability separation a given WPR gap implies" holds regardless of how
many runners are in the race - a 6-horse field and an 18-horse field may
genuinely need different softmax sharpness to be well-calibrated (more
runners means more ways for the favourite to be beaten, which a fixed
beta cannot represent). This is the natural follow-up to a later isotonic
recalibration test that found NO improvement (Brier tied 0.0866 vs
0.0866) - isotonic only remaps by raw probability value, blind to
context like field size, so it could not have found a real field-size-
dependent effect even if one exists. This test can.

METHODOLOGY: reuses calibrate_price_beta.py's own _load_resulted() (fresh
wprp_proj via the real compute_wpr_projection() entry point, NOT the
stale stored column - same staleness bug this session already found and
worked around once tonight) over the same held-out-Brier-selection
convention, but bucketed by field size (Small 6-9, Medium 10-13, Large
14+, matching the buckets already used in the earlier barrier analysis
tonight) instead of one number for the whole dataset. Reports:
  1. Best beta per field-size bucket (held-out-selected, same grid as
     calibrate_price_beta.py) vs the single global beta (0.15) applied to
     each bucket.
  2. Held-out Brier: global-beta-everywhere vs per-bucket-beta.
  3. A verdict: does this beat the current global approach enough to be
     worth the added complexity (a beta lookup instead of one number)?

NO EM DASHES policy: hyphens only.
"""
import numpy as np
import pandas as pd

from calibrate_price_beta import _load_resulted, _brier, BETA_GRID, DEFAULT_DAYS_BACK, CONFIG_PATH
import json

FS_BUCKETS = [(6, 9, "Small (6-9)"), (10, 13, "Medium (10-13)"), (14, 99, "Large (14+)")]


def add_field_size(d):
    d = d.copy()
    fs = d.groupby("race_id")["race_id"].transform("size")
    d["field_size"] = fs
    return d


def brier_by_beta(data, beta_grid):
    return {b: _brier(data, b) for b in beta_grid}


def run(days_back=60):
    # 60 days (not DEFAULT_DAYS_BACK*2/90+) - _load_resulted() recomputes
    # wprp_proj fresh per date via the real compute_wpr_projection() entry
    # point (~45-50s/date observed empirically tonight, wpr_isotonic_
    # calibration_test.py's 150-day run took ~90 min) - 60 days keeps this
    # test's runtime to something reasonable while still giving each of
    # the 3 field-size buckets a few thousand held-out rows.
    print(f"Loading resulted races (fresh wprp_proj via compute_wpr_projection, "
          f"{days_back} days back)...")
    d = _load_resulted(days_back=days_back)
    d = d.dropna(subset=["wprp_proj", "won", "race_id", "date"])
    d = add_field_size(d)
    d = d[d["field_size"] >= 4]
    print(f"Loaded: {len(d):,} resulted rows, {d['race_id'].nunique():,} races, "
          f"{d['date'].min()} .. {d['date'].max()}")

    cur_beta = 0.15
    if CONFIG_PATH.exists():
        cur_beta = json.load(open(CONFIG_PATH)).get("beta", 0.15)
    print(f"current shipped global beta: {cur_beta}")

    cut = d["date"].quantile(0.60)
    trn, tst = d[d["date"] < cut], d[d["date"] >= cut]
    print(f"search < {cut.date()}: {trn['race_id'].nunique():,} races, "
          f"held-out: {tst['race_id'].nunique():,} races")

    print("\n" + "=" * 78)
    print("GLOBAL beta (current approach) - held-out Brier per field-size bucket")
    print("=" * 78)
    global_tst_brier = {}
    for lo, hi, label in FS_BUCKETS:
        sub_tst = tst[(tst["field_size"] >= lo) & (tst["field_size"] <= hi)]
        b = _brier(sub_tst, cur_beta)
        global_tst_brier[label] = (b, sub_tst["race_id"].nunique())
        print(f"  {label:16s}: n_races={sub_tst['race_id'].nunique():4d}  "
              f"Brier(beta={cur_beta})={b:.4f}")

    print("\n" + "=" * 78)
    print("PER-BUCKET beta search (fit on search set, select by held-out Brier)")
    print("=" * 78)
    bucket_best = {}
    for lo, hi, label in FS_BUCKETS:
        sub_trn = trn[(trn["field_size"] >= lo) & (trn["field_size"] <= hi)]
        sub_tst = tst[(tst["field_size"] >= lo) & (tst["field_size"] <= hi)]
        print(f"\n-- {label} (search races={sub_trn['race_id'].nunique():,}, "
              f"held-out races={sub_tst['race_id'].nunique():,}) --")
        search_briers = brier_by_beta(sub_trn, BETA_GRID)
        tst_briers = brier_by_beta(sub_tst, BETA_GRID)
        for b in BETA_GRID:
            print(f"    beta={b:.2f}   search {search_briers[b]:.4f}   held-out {tst_briers[b]:.4f}")
        best_b = min(search_briers, key=lambda b: search_briers[b])  # select by SEARCH, same as calibrate_price_beta.py
        bucket_best[label] = (best_b, tst_briers[best_b])
        print(f"  best beta (search-selected): {best_b}  ->  held-out Brier: {tst_briers[best_b]:.4f}  "
              f"(vs global beta={cur_beta}: {global_tst_brier[label][0]:.4f})")

    print("\n" + "=" * 78)
    print("VERDICT: per-field-size beta vs one global beta, pooled held-out Brier")
    print("=" * 78)
    total_n = sum(n for _, n in global_tst_brier.values())
    global_pooled = sum(b * n for b, n in global_tst_brier.values()) / total_n
    bucket_pooled = sum(bucket_best[label][1] * global_tst_brier[label][1] for label in bucket_best) / total_n
    print(f"global beta ({cur_beta}) everywhere:        pooled held-out Brier = {global_pooled:.4f}")
    print(f"per-field-size beta ({', '.join(f'{l}={b}' for l,(b,_) in bucket_best.items())}): "
          f"pooled held-out Brier = {bucket_pooled:.4f}")
    delta = bucket_pooled - global_pooled
    print(f"delta: {delta:+.4f}  ({'IMPROVEMENT from per-bucket beta' if delta < 0 else 'WORSE, not worth the complexity'})")


if __name__ == "__main__":
    run()
