"""
wpr_roi_rule_mining.py - "what about top X in wpr rating, top X in form
factor rating, edge of X, plus any other data that is profitable?"
follow-up to wpr_roi_filter_search.py (which found market-rank agreement
was the only filter that meaningfully moved ROI, and even that converges
toward "just back the favourite" rather than a real discovery).

Two parts, same pooled held-out K=4-fold scored data (NEW tiered base,
PR #173) as wpr_roi_filter_search.py:

  PART A - the user's own proposed rule shape: "top X in wpr rating" (the
  bet's rank by raw wpr_nett within its own race) and "top X in form
  factor rating" (rank by ewm5, the recency-weighted recent-form signal)
  as AGREEMENT filters on top of an edge threshold - does requiring the
  bet to also be one of the race's best-RATED (not just best-priced, cf.
  market-rank agreement) horses by these raw own-history signals help?

  PART B - a broader single-feature scan ("any other data that is
  profitable"): for a curated set of pre-race-known features not yet
  tested this session as ROI filters (barrier, distance, going,
  first/second-up, trainer/jockey merit sign, consistency, recent
  trend/trajectory, class_move), split into simple bands and report ROI
  for each vs the edge>=0.05 baseline.

ROBUSTNESS: with this many filters tested, multiple-comparisons risk is
real - some band looking good is expected by chance alone even with zero
true signal. Any candidate that beats the baseline pooled ROI is ALSO
checked fold-by-fold (does the direction hold in most/all of the 4
held-out folds, or is one fold driving it) before being called anything
more than "worth a longer look" - matching this session's standing bar
(K-fold robustness, not a single pooled number) for anything that would
change actual bet selection.

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np
import pandas as pd

from wpr_roi_filter_search import build_pooled
from wpr_bet_selection_post_retrain import report

EDGE_THR = 0.05
PRICE_CAP = 26.0


def report_with_fold_check(sub, label, pooled_folds):
    """Same as report(), plus a per-fold ROI sign check so a filter that
    only looks good pooled (driven by one lucky fold) is visible as such."""
    report(sub, label)
    if len(sub) < 20:
        return
    fold_rois = []
    for f in sorted(sub["_fold"].unique()):
        fs = sub[sub["_fold"] == f]
        if len(fs) < 5:
            fold_rois.append(None)
            continue
        profit = np.where(fs["won"] == 1, fs["sp"] - 1, -1.0)
        fold_rois.append(profit.mean() * 100)
    tags = ", ".join(f"f{f}={'n/a' if r is None else f'{r:+.0f}%'}" for f, r in zip(sorted(sub["_fold"].unique()), fold_rois))
    n_pos = sum(1 for r in fold_rois if r is not None and r > 0)
    n_scored = sum(1 for r in fold_rois if r is not None)
    print(f"        per-fold ROI: {tags}  ({n_pos}/{n_scored} folds positive)")


def run():
    print("Rebuilding pooled held-out scored data (NEW tiered base)...")
    pooled = build_pooled()
    print(f"Pooled rows: {len(pooled):,}")

    def _rank(col):
        def _r(g):
            return g[col].rank(ascending=False, method="min")
        return pooled.groupby("race_id", group_keys=False).apply(_r)

    pooled["wpr_rank_in_race"] = _rank("wpr_nett")
    pooled["form_rank_in_race"] = _rank("ewm5")

    base = pooled[(pooled["edge"] >= EDGE_THR) & (pooled["sp"] <= PRICE_CAP)]
    print(f"\n{'='*100}\nBASELINE: edge>={EDGE_THR:.2f}, price<=${PRICE_CAP:.0f}\n{'='*100}")
    report_with_fold_check(base, "baseline", pooled)

    print(f"\n{'='*100}\nPART A: TOP X IN WPR RATING / FORM FACTOR RATING (own-signal rank agreement)\n{'='*100}")
    print("\n--- top X by raw wpr_nett rank in race ---")
    for x in [1, 2, 3]:
        sub = base[base["wpr_rank_in_race"] <= x]
        report_with_fold_check(sub, f"wpr_rank<={x}", pooled)

    print("\n--- top X by ewm5 (form factor) rank in race ---")
    for x in [1, 2, 3]:
        sub = base[base["form_rank_in_race"] <= x]
        report_with_fold_check(sub, f"form_rank<={x}", pooled)

    print("\n--- BOTH top X by wpr_nett AND top X by ewm5 ---")
    for x in [1, 2, 3]:
        sub = base[(base["wpr_rank_in_race"] <= x) & (base["form_rank_in_race"] <= x)]
        report_with_fold_check(sub, f"wpr_rank<={x} AND form_rank<={x}", pooled)

    print(f"\n{'='*100}\nPART B: OTHER CANDIDATE FEATURES (single-feature bands, edge>={EDGE_THR:.2f}, "
          f"price<=${PRICE_CAP:.0f})\n{'='*100}")

    print("\n--- barrier ---")
    for label, mask in [("inside (1-4)", base["barrier"] <= 4),
                        ("mid (5-9)", (base["barrier"] >= 5) & (base["barrier"] <= 9)),
                        ("wide (10+)", base["barrier"] >= 10)]:
        report_with_fold_check(base[mask], f"barrier {label}", pooled)

    print("\n--- distance ---")
    for label, mask in [("sprint <=1200", base["cur_distance"] <= 1200),
                        ("mile 1201-1600", (base["cur_distance"] > 1200) & (base["cur_distance"] <= 1600)),
                        ("staying >1600", base["cur_distance"] > 1600)]:
        report_with_fold_check(base[mask], f"distance {label}", pooled)

    print("\n--- first-up / second-up / neither ---")
    for label, mask in [("first_up", base["first_up"] == 1),
                        ("second_up", base["second_up"] == 1),
                        ("neither (settled in prep)", (base["first_up"] == 0) & (base["second_up"] == 0))]:
        report_with_fold_check(base[mask], label, pooled)

    print("\n--- trainer_win_pct_365d / jockey_win_pct_90d (top decile vs rest) ---")
    tw_cut = base["trainer_win_pct_365d"].quantile(0.90)
    jw_cut = base["jockey_win_pct_90d"].quantile(0.90)
    report_with_fold_check(base[base["trainer_win_pct_365d"] >= tw_cut], f"trainer_win_pct top decile (>={tw_cut:.3f})", pooled)
    report_with_fold_check(base[base["jockey_win_pct_90d"] >= jw_cut], f"jockey_win_pct top decile (>={jw_cut:.3f})", pooled)

    print("\n--- consistency_ratio (low variance vs high variance recent form) ---")
    cr_med = base["consistency_ratio"].median()
    report_with_fold_check(base[base["consistency_ratio"] <= cr_med], "consistency_ratio <= median (more consistent)", pooled)
    report_with_fold_check(base[base["consistency_ratio"] > cr_med], "consistency_ratio > median (less consistent)", pooled)

    print("\n--- wpr_traj (recent form trajectory: improving vs declining) ---")
    report_with_fold_check(base[base["wpr_traj"] > 0], "wpr_traj > 0 (improving)", pooled)
    report_with_fold_check(base[base["wpr_traj"] <= 0], "wpr_traj <= 0 (flat/declining)", pooled)

    print("\n--- class_move (dropping in class vs rising vs same) ---")
    report_with_fold_check(base[base["class_move"] < 0], "class_move < 0 (dropping in class)", pooled)
    report_with_fold_check(base[base["class_move"] == 0], "class_move == 0 (same class)", pooled)
    report_with_fold_check(base[base["class_move"] > 0], "class_move > 0 (rising in class)", pooled)

    print("\n--- days_since (fresh vs backed-up) ---")
    for label, mask in [("<=14 days (quick back-up)", base["days_since"] <= 14),
                        ("15-42 days (normal cycle)", (base["days_since"] > 14) & (base["days_since"] <= 42)),
                        (">42 days (spell)", base["days_since"] > 42)]:
        report_with_fold_check(base[mask], f"days_since {label}", pooled)

    print("\nSame caveats as always: leak-free-for-wpr_nett K-fold, but one dataset/attempt. This is a wide "
          "multiple-comparisons search - some band looking good here is EXPECTED by chance even with zero "
          "true signal. Only trust a candidate that (a) beats baseline pooled ROI, (b) holds up in most/all "
          "4 folds individually, not just pooled, and (c) has a sample size large enough that its t-stat "
          "isn't just 'too small to tell'. Anything else is a hypothesis for a future walk-forward period, "
          "not a rule to ship.")


if __name__ == "__main__":
    run()
