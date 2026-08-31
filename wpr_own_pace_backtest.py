"""
wpr_own_pace_backtest.py - the "own_pace backtest script, not committed"
referenced in wpr_projection.py's _horse_feature_rows docstring.

Tests whether own_pace (does THIS horse personally run above/below its own
level when the race's early tempo matches today's PREDICTED shape - see
wpr_projection.py's own_pace computation) actually improves the WPR
projection's held-out accuracy enough to justify adding it to ADJ_TERMS.

WHY THIS EXISTS
  A form analyst's real question isn't just "rate the horse" - it's "does
  today's likely pace suit how this horse actually runs". wpr_projection.py
  already computes own_pace as a CANDIDATE (matching race_speed_estimate.py's
  leak-safe pre-race tempo prediction against each horse's own sectional-
  derived running style), but it was never added to ADJ_TERMS because the
  backtest needed to decide required computing race_speed_estimate.py's
  prediction for every HISTORICAL race with a leak-safe (prior-data-only)
  cutoff - expensive, and apparently never finished (two real bugs in
  race_speed_estimate.py's tempo labelling were found and fixed while
  someone was building this, but the actual comparison was never run).

METHODOLOGY (matches this file's own established standard - see
wpr_projection.py's ADJ_TERMS experiment log)
  1. For every race in the test window, compute race_speed_estimate.py's
     predicted tempo using ONLY prior-to-that-date form history (exactly
     how it would have looked pre-race at the time) - _prior_means/
     estimate_race_speed already do this correctly.
  2. Rebuild the training frame with race_speed_labels populated (own_pace
     becomes real instead of defaulting to 0 for every row).
  3. Compare held-out MAE of the CURRENT 7-term ADJ_TERMS baseline against
     baseline + own_pace, on a chronological half-split, BOTH directions
     (H1-fit/H2-validate and H2-fit/H1-validate) - a result that only
     helps one direction is noise, not a real effect, per every other
     ADJ_TERMS decision already made in this file.

USAGE
  python wpr_own_pace_backtest.py                  # last 6 months (default)
  python wpr_own_pace_backtest.py --since 2026-01-01

NO EM DASHES policy: hyphens only in this file.
"""
import argparse

import numpy as np
import pandas as pd
from sklearn.metrics import mean_absolute_error

import wpr_projection as wpr
import race_speed_estimate as rse

FORM_CSV = "wpr_form_history.csv.gz"


def build_race_speed_labels(since):
    """Leak-safe Hot/Fast/Even/Slow label for every race on/after `since`,
    keyed by run_id (every runner in a race shares that race's label)."""
    fh = rse._load_and_prep_form()  # adds horse_lc, dedupes, drops barrier trials
    rse._load_model()

    scoped = fh[(fh["date"] >= since) & fh["race_id"].notna()]
    dates = sorted(scoped["date"].dt.date.unique())
    print(f"Building leak-safe race-speed labels for {len(dates)} race days "
          f"({scoped['race_id'].nunique():,} races) since {since}...")

    run_id_to_label = {}
    for i, d in enumerate(dates):
        if i % 20 == 0:
            print(f"  ... {i}/{len(dates)} days")
        day_races = scoped[scoped["date"].dt.date == d]
        pmeans = rse._prior_means(fh, pd.Timestamp(d))
        for race_id, race_runners in day_races.groupby("race_id"):
            try:
                res = rse.estimate_race_speed(race_runners, pd.Timestamp(d), fh, pmeans)
            except Exception:
                continue
            for run_id in race_runners["run_id"]:
                run_id_to_label[run_id] = res["label"]
    print(f"  labelled {len(run_id_to_label):,} runner-rows")
    return run_id_to_label


def add_base(D):
    """Replicates train_wpr_projection's _base computation exactly (must
    match _compute_base()) - build_training_frame() doesn't compute this
    itself, only the raw wpr_nett/ewm3/avg_last3/career_avg it needs.
    Simplification vs the real training pipeline: skips the void-comment
    exclusion filter (a smaller-impact refinement, not needed to answer
    "does own_pace help at all") but keeps the blank-going/dirt-synth
    exclusion, which materially changes the row count."""
    D = D.copy()
    if "going" in D.columns:
        g = D["going"].astype(str).str.strip().str.lower()
        blank_going = D["going"].isna() | g.isin(["", "nan", "none", "<na>"])
        D = D[~blank_going].copy()
    both = D["wpr_nett"].notna() & D["ewm3"].notna()
    D["_base"] = np.where(both, wpr._BASE_BLEND_ALPHA * D["wpr_nett"] + (1 - wpr._BASE_BLEND_ALPHA) * D["ewm3"],
                          D["wpr_nett"].fillna(D["ewm3"]))
    D["_base"] = pd.Series(D["_base"], index=D.index).fillna(D["avg_last3"]).fillna(D["career_avg"])
    return D.dropna(subset=["_base"])


def held_out_mae(cf, te, adj_terms):
    def predict(frame):
        return frame["_base"].to_numpy() + wpr._cap_adj_sum(
            frame[adj_terms].to_numpy()).sum(axis=1)
    return mean_absolute_error(te["target"], predict(te))


def run(since):
    labels = build_race_speed_labels(since)

    print("\nRebuilding training frame with own_pace populated (this reuses "
          "wpr_projection.py's own build_training_frame, may take a while)...")
    full = wpr.build_training_frame(FORM_CSV, verbose=True, race_speed_labels=labels)

    # Only rows where own_pace could actually be non-zero (i.e. this run's
    # date is in the labelled window) are informative for this comparison -
    # outside that window own_pace is silently 0 for both models, which
    # would just dilute the measured effect, not invalidate it, but scoping
    # to the labelled window is a cleaner, more sensitive test.
    full = add_base(full)
    full["date"] = pd.to_datetime(full["date"])
    scoped = full[full["date"] >= pd.Timestamp(since)].copy()
    scoped = scoped.dropna(subset=["target", "_base"] + wpr.ADJ_TERMS + ["own_pace"])
    print(f"\nScoped rows for comparison: {len(scoped):,} "
          f"(own_pace non-zero on {(scoped['own_pace'] != 0).mean()*100:.1f}%)")

    mid = scoped["date"].quantile(0.5)
    h1, h2 = scoped[scoped["date"] < mid], scoped[scoped["date"] >= mid]
    print(f"H1: {len(h1):,} rows (< {mid.date()}), H2: {len(h2):,} rows (>= {mid.date()})")

    baseline_terms = list(wpr.ADJ_TERMS)
    candidate_terms = baseline_terms + ["own_pace"]

    print("\n=== H1-fit/H2-validate direction ===")
    # Nothing is actually "fit" here - ADJ_TERMS are per-horse lookups, not
    # a regression - so "H1-fit" is really just reporting H1's own MAE for
    # context; H2 is the real held-out number, matching this file's own
    # convention (e.g. the exact-distance-match test earlier in the file).
    print(f"  baseline (7 terms):        H1 MAE={held_out_mae(h1, h1, baseline_terms):.4f}  "
          f"H2 (held-out) MAE={held_out_mae(h1, h2, baseline_terms):.4f}")
    print(f"  +own_pace (8 terms):       H1 MAE={held_out_mae(h1, h1, candidate_terms):.4f}  "
          f"H2 (held-out) MAE={held_out_mae(h1, h2, candidate_terms):.4f}")

    print("\n=== H2-fit/H1-validate direction ===")
    print(f"  baseline (7 terms):        H2 MAE={held_out_mae(h2, h2, baseline_terms):.4f}  "
          f"H1 (held-out) MAE={held_out_mae(h2, h1, baseline_terms):.4f}")
    print(f"  +own_pace (8 terms):       H2 MAE={held_out_mae(h2, h2, candidate_terms):.4f}  "
          f"H1 (held-out) MAE={held_out_mae(h2, h1, candidate_terms):.4f}")

    b_h2 = held_out_mae(h1, h2, baseline_terms)
    c_h2 = held_out_mae(h1, h2, candidate_terms)
    b_h1 = held_out_mae(h2, h1, baseline_terms)
    c_h1 = held_out_mae(h2, h1, candidate_terms)
    print(f"\nHeld-out MAE change: direction 1 {b_h2:.4f} -> {c_h2:.4f} "
          f"({'better' if c_h2 < b_h2 else 'worse'}), "
          f"direction 2 {b_h1:.4f} -> {c_h1:.4f} ({'better' if c_h1 < b_h1 else 'worse'})")
    if c_h2 < b_h2 and c_h1 < b_h1:
        print("BOTH directions improved - a real, adoptable effect by this file's own standard.")
    else:
        print("Not both directions improved - per this file's own standard (every other "
              "ADJ_TERM decision required both), this does NOT clear the bar for adoption.")


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--since", type=str, default=None,
                     help="only label/test races on or after this date (default: 6 months back)")
    args = ap.parse_args()
    since = args.since or (pd.Timestamp.today() - pd.Timedelta(days=183)).strftime("%Y-%m-%d")
    run(since)
