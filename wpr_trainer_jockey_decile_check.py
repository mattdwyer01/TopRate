"""
wpr_trainer_jockey_decile_check.py - stress-test follow-up to the two
candidates that broke through wpr_roi_rule_mining.py's broad scan
(trainer_win_pct_365d top decile: +17.68% ROI, 3/4 folds positive;
jockey_win_pct_90d top decile: +22.36% ROI, 3/4 folds positive - the only
two positive results out of ~30 bands tested). Neither was statistically
significant (t=1.23, t=1.67) and this was a wide multiple-comparisons
search, so before treating either as a real finding: does combining them
compound or is it redundant (same horses), does the effect need the
edge>=0.05 filter to exist at all, and does it survive at other edge
thresholds (not just the one where it happened to look best)?

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np

from wpr_roi_filter_search import build_pooled
from wpr_bet_selection_post_retrain import report

EDGE_THR = 0.05
PRICE_CAP = 26.0


def fold_check(sub, label):
    report(sub, label)
    if len(sub) < 5:
        return
    rois = []
    for f in sorted(sub["_fold"].unique()):
        fs = sub[sub["_fold"] == f]
        if len(fs) < 5:
            continue
        profit = np.where(fs["won"] == 1, fs["sp"] - 1, -1.0)
        rois.append((f, profit.mean() * 100, len(fs)))
    print("    per-fold:", ", ".join(f"f{f}={r:+.0f}%(n={n})" for f, r, n in rois))


def run():
    pooled = build_pooled()
    base = pooled[(pooled["edge"] >= EDGE_THR) & (pooled["sp"] <= PRICE_CAP)]

    tw_cut = base["trainer_win_pct_365d"].quantile(0.90)
    jw_cut = base["jockey_win_pct_90d"].quantile(0.90)

    print("\n--- both top decile (trainer AND jockey) ---")
    fold_check(base[(base["trainer_win_pct_365d"] >= tw_cut) & (base["jockey_win_pct_90d"] >= jw_cut)], "both top decile")

    print("\n--- either top decile (trainer OR jockey) ---")
    fold_check(base[(base["trainer_win_pct_365d"] >= tw_cut) | (base["jockey_win_pct_90d"] >= jw_cut)], "either top decile")

    print("\n--- SAME filters, but WITHOUT the edge>=0.05 requirement (pure trainer/jockey decile strategy) ---")
    pooled_capped = pooled[pooled["sp"] <= PRICE_CAP]
    tw_cut2 = pooled_capped["trainer_win_pct_365d"].quantile(0.90)
    jw_cut2 = pooled_capped["jockey_win_pct_90d"].quantile(0.90)
    fold_check(pooled_capped[pooled_capped["trainer_win_pct_365d"] >= tw_cut2], "trainer top decile, NO edge filter")
    fold_check(pooled_capped[pooled_capped["jockey_win_pct_90d"] >= jw_cut2], "jockey top decile, NO edge filter")

    print("\n--- trainer top decile at other edge thresholds (robustness across thresholds) ---")
    for thr in [0.0, 0.02, 0.05, 0.10]:
        sub = pooled[(pooled["edge"] >= thr) & (pooled["sp"] <= PRICE_CAP) & (pooled["trainer_win_pct_365d"] >= tw_cut)]
        fold_check(sub, f"trainer top decile, edge>={thr:.2f}")

    print("\n--- jockey top decile at other edge thresholds (robustness across thresholds) ---")
    for thr in [0.0, 0.02, 0.05, 0.10]:
        sub = pooled[(pooled["edge"] >= thr) & (pooled["sp"] <= PRICE_CAP) & (pooled["jockey_win_pct_90d"] >= jw_cut)]
        fold_check(sub, f"jockey top decile, edge>={thr:.2f}")


if __name__ == "__main__":
    run()
