"""
wpr_beta_calibration_angles_test.py - follow-up to wpr_beta_by_field_size_test.py,
testing the field-size-conditioned-beta question with two angles that a
single Brier-score grid search can hide:

  1. RELIABILITY TABLE per field-size bucket (Small 6-9 / Medium 10-13 /
     Large 14+): predicted-vs-actual win rate by probability decile,
     AT THE CURRENT GLOBAL BETA (0.15). A single aggregate Brier number
     can look fine while hiding a real pattern in one part of the
     probability range (e.g. fine everywhere except the top decile) -
     this shows the SHAPE, not just one scalar. wpr_beta_by_field_size_
     test.py's own numbers already suggested nothing real was there
     (Small had a genuine, well-separated Brier-minimum at 0.15 matching
     global; Medium's apparent shift to 0.20 was a search-set tie, not a
     real signal; Large only had 46 held-out races, too thin to trust) -
     this confirms or overturns that with the richer view.
  2. ROI-BASED CHECK per field-size bucket: this session's own repeated
     lesson tonight (the calibration-slope removal, closing_merit,
     gear_change) is that a point-accuracy/probability-fit metric (MAE,
     Brier) and actual betting profitability (ROI/strike) can diverge.
     Brier being a wash does not by itself prove ROI would be a wash too -
     this tests edge/strike/ROI at the existing EDGE_THRESHOLDS, split by
     field-size bucket, current global beta vs each bucket's own
     candidate beta from the earlier grid.
  3. LONGER WINDOW (120 days, not 60) specifically to give the Large
     bucket (14+) a real held-out sample - 46 races was too few to
     conclude anything either way last time.

METHODOLOGY: reuses calibrate_price_beta.py's _load_resulted() (fresh
wprp_proj via the real compute_wpr_projection() entry point - avoids the
stale-stored-column bug this session already worked around once), keeps
the FULL frame (including fixed_win_price/starting_price_sp) rather than
stripping to bare columns - wpr_isotonic_calibration_test.py's ROI
section silently found "no price column" because its softmax_by_race()
helper discarded every column except p/won/race_id before scoring; this
version keeps the frame intact throughout to avoid repeating that.

NO EM DASHES policy: hyphens only.
"""
import numpy as np
import pandas as pd

from calibrate_price_beta import _load_resulted, _brier, CONFIG_PATH
import json

from wpr_bet_selection_post_retrain import report
from wpr_slope_roi_test import EDGE_THRESHOLDS
import wpr_slope_roi_test as roi

DAYS_BACK = 120
FS_BUCKETS = [(6, 9, "Small (6-9)"), (10, 13, "Medium (10-13)"), (14, 99, "Large (14+)")]
# current global + each bucket's own candidate from the earlier grid search
BETAS_TO_CHECK = [0.10, 0.15, 0.20, 0.25]


def add_field_size(d):
    d = d.copy()
    d["field_size"] = d.groupby("race_id")["race_id"].transform("size")
    return d


def score_probs(data, beta):
    """Per-runner softmax win probability at `beta`, race-scoped (>=4
    finishers only, same convention as _brier). Returns a Series aligned
    to data's index, NaN for excluded rows."""
    p = pd.Series(np.nan, index=data.index)
    for rid, g in data.groupby("race_id"):
        if len(g) < 4:
            continue
        pv = g["wprp_proj"].to_numpy(dtype=float)
        e = np.exp(beta * (pv - pv.max()))
        p.loc[g.index] = e / e.sum()
    return p


def reliability_table(data, prob_col, n_bins=5):
    d = data.dropna(subset=[prob_col]).copy()
    if len(d) < 50:
        return None
    d["bin"] = pd.qcut(d[prob_col], min(n_bins, d[prob_col].nunique()), labels=False, duplicates="drop")
    return d.groupby("bin").agg(pred=(prob_col, "mean"), actual=("won", "mean"), n=("won", "size"))


def run():
    print(f"Loading resulted races (fresh wprp_proj via compute_wpr_projection, "
          f"{DAYS_BACK} days back)...")
    d = _load_resulted(days_back=DAYS_BACK)
    d = d.dropna(subset=["wprp_proj", "won", "race_id", "date"])
    d = add_field_size(d)
    print(f"Loaded: {len(d):,} resulted rows, {d['race_id'].nunique():,} races, "
          f"{d['date'].min()} .. {d['date'].max()}")

    sp = pd.to_numeric(d["fixed_win_price"], errors="coerce")
    sp_fb = pd.to_numeric(d["starting_price_sp"], errors="coerce")
    d["sp"] = sp.fillna(sp_fb)

    cur_beta = 0.15
    if CONFIG_PATH.exists():
        cur_beta = json.load(open(CONFIG_PATH)).get("beta", 0.15)

    print("\n" + "=" * 78)
    print(f"ANGLE 1: reliability table per field-size bucket (beta={cur_beta})")
    print("=" * 78)
    d["p_cur"] = score_probs(d, cur_beta)
    for lo, hi, label in FS_BUCKETS:
        sub = d[(d["field_size"] >= lo) & (d["field_size"] <= hi)]
        print(f"\n-- {label}: n={len(sub):,} rows, {sub['race_id'].nunique():,} races --")
        tbl = reliability_table(sub, "p_cur")
        if tbl is None:
            print("  too few rows for a reliability table")
        else:
            print(tbl.to_string())

    print("\n" + "=" * 78)
    print("ANGLE 2: ROI/edge check per field-size bucket, at several beta values")
    print("=" * 78)
    valid_sp = d.dropna(subset=["sp"])
    valid_sp = valid_sp[valid_sp["sp"] > 1.0]
    for lo, hi, label in FS_BUCKETS:
        sub = valid_sp[(valid_sp["field_size"] >= lo) & (valid_sp["field_size"] <= hi)]
        print(f"\n-- {label}: n={len(sub):,} priced rows --")
        if len(sub) < 200:
            print("  too few priced rows, skipping")
            continue
        for beta in BETAS_TO_CHECK:
            s = sub.copy()
            s["p"] = score_probs(s, beta)
            s = s.dropna(subset=["p"])
            s["mkt_prob"] = s.groupby("race_id")["sp"].transform(lambda x: (1 / x) / (1 / x).sum())
            s["edge_wpr"] = s["p"] - s["mkt_prob"]
            print(f"  beta={beta:.2f}:")
            for thr in EDGE_THRESHOLDS:
                report(s[s["edge_wpr"] >= thr], f"    edge>={thr:.2f}")

    print("\n" + "=" * 78)
    print(f"ANGLE 3 context: sample sizes with the longer {DAYS_BACK}-day window")
    print("=" * 78)
    for lo, hi, label in FS_BUCKETS:
        sub = d[(d["field_size"] >= lo) & (d["field_size"] <= hi)]
        print(f"  {label}: {sub['race_id'].nunique():,} races total ({DAYS_BACK} days) "
              f"vs the earlier 60-day test's smaller sample")


if __name__ == "__main__":
    run()
