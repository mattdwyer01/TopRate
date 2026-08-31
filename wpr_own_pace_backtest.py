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
    keyed by race_id (every runner in a race shares that race's label).

    CAUTION, fixed Aug 2026: this used to key by run_id, re-applying it to
    every runner in the race. run_id is NOT a reliable per-runner key in
    the raw form history - every row in a scraped horse's WHOLE form table
    gets stamped with whatever race it was being scraped FOR, not the
    run_id of each individual past run (see merge_won_by_horse_date's
    docstring for the full writeup) - so a run_id-keyed dict could
    silently apply ONE race's label to a horse's OTHER, unrelated
    historical rows that happened to share that same contaminated run_id.
    race_id has no such problem (verified: groups of it correctly contain
    many distinct horses on one date, a real race), and a pace label is a
    race-wide value anyway (every runner in it shares one label), so
    keying by race_id is both simpler and correct - no per-runner
    iteration needed."""
    fh = rse._load_and_prep_form()  # adds horse_lc, dedupes, drops barrier trials
    rse._load_model()

    scoped = fh[(fh["date"] >= since) & fh["race_id"].notna()]
    dates = sorted(scoped["date"].dt.date.unique())
    print(f"Building leak-safe race-speed labels for {len(dates)} race days "
          f"({scoped['race_id'].nunique():,} races) since {since}...")

    race_id_to_label = {}
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
            race_id_to_label[race_id] = res["label"]
    print(f"  labelled {len(race_id_to_label):,} races")
    return race_id_to_label


def merge_won_by_horse_date(D, form_csv=FORM_CSV, runners_csv="toprate_runners.csv"):
    """Merges the "won" outcome (and race_id, for grouping) from
    toprate_runners.csv onto a build_training_frame() dataframe, joining
    by (horse name, date) - NOT by run_id. Requires D to have a
    "horse_id" column (build_training_frame retains this as an
    analysis-only field - see wpr_projection.py's _horse_feature_rows).

    CRITICAL BUG THIS FIXES: build_training_frame's own "run_id" column
    is NOT a per-historical-row race identifier. Every row in a scraped
    horse's form table (its entire multi-year history, one scrape) gets
    stamped with the SAME run_id - whatever race that horse was actually
    being scraped FOR at that time - not the run_id of each individual
    past run. Verified directly: of the rows that inner-join successfully
    to toprate_runners.csv via run_id, 96.6% have a form-history date that
    does NOT match the runners.csv date for that same run_id - i.e. the
    "won" outcome attached is for a completely different race than the
    one the row is describing (a horse's 2017 run getting labelled with
    its 2026 race's result). This silently corrupted every strike-rate
    test in this session that merged "won" via run_id (closing_merit,
    settle_pace, the alpha strike-rate sweep, alpha80's calibration fit) -
    MAE-based results were unaffected (target never depended on run_id),
    only anything needing "did this row's race actually get won".

    toprate_runners.csv has no horse_id, only horse NAME - horse_id ->
    name comes from the raw form history (which has both). (horse, date)
    is not a perfect key either (824/55,528 toprate_runners.csv rows
    collide - same-name horses running the same day at different tracks)
    - those ambiguous pairs are dropped rather than risk a wrong match,
    same conservative principle as this fix itself."""
    name_map = pd.read_csv(form_csv, usecols=["horse_id", "horse"], low_memory=False)
    name_map = name_map.dropna().drop_duplicates(subset="horse_id", keep="last")
    name_map = name_map.set_index("horse_id")["horse"]

    tr = pd.read_csv(runners_csv, dtype={"race_id": str}, low_memory=False,
                      usecols=["horse", "date", "race_id", "won", "resulted", "scratched"])
    tr["date"] = pd.to_datetime(tr["date"], errors="coerce")
    tr["resulted"] = pd.to_numeric(tr["resulted"], errors="coerce")
    tr["scratched"] = pd.to_numeric(tr["scratched"], errors="coerce")
    tr["won"] = pd.to_numeric(tr["won"], errors="coerce")
    tr = tr[(tr["resulted"] == 1) & (tr["scratched"] != 1)].dropna(subset=["won", "race_id", "date"])
    tr = tr.drop_duplicates(subset=["horse", "date"], keep=False)  # drop ambiguous same-day name clashes

    D = D.copy()
    D["date"] = pd.to_datetime(D["date"])
    D["horse"] = D["horse_id"].map(name_map)
    # D's own "race_id" (if present - build_training_frame retains one from
    # the raw form history) is stamped via the same contaminated scrape-time
    # mechanism as run_id, not a reliable per-row key - drop it so the
    # correct one from toprate_runners.csv is what survives the merge,
    # rather than colliding into race_id_x/race_id_y.
    if "race_id" in D.columns:
        D = D.drop(columns=["race_id"])
    return D.merge(tr[["horse", "date", "race_id", "won"]], on=["horse", "date"], how="inner")


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


def add_track_barrier(fit, frames):
    """Replicates train_wpr_projection's track_barrier fit+apply exactly
    (wpr_projection.py lines 2644-2678) - the one ADJ_TERMS entry that needs
    an actual fitted lookup (population residual by track/dist-band/barrier-
    band) rather than a pure per-horse history lookup. Fits on `fit` only,
    applies the resulting lookup to every frame in `frames` (which may
    include `fit` itself, matching how every other held_out_mae() call here
    reports an in-sample number for context alongside the real held-out one)."""
    tb_resid = fit["target"] - fit["career_avg"]
    tb_band = [wpr._barrier_band(b, f) for b, f in zip(fit["barrier"], fit["field_size"])]
    tb_dist_band = (fit["cur_distance"] // 200 * 200).astype(int)
    tb_frame = pd.DataFrame({
        "track": fit["track"], "dist_band": tb_dist_band,
        "band": tb_band, "residual": tb_resid,
    }).dropna(subset=["track", "band", "residual"])
    tb_global = tb_frame.groupby("band")["residual"].mean().to_dict()
    lookup = {}
    for (trk, db), g in tb_frame.groupby(["track", "dist_band"]):
        stats = g.groupby("band")["residual"].agg(["mean", "count"])
        shrunk = {}
        for b in ["Inside", "Mid", "Wide"]:
            if b in stats.index:
                n, m = stats.loc[b, "count"], stats.loc[b, "mean"]
                shrunk[b] = (n * m + wpr._TRACK_BARRIER_K * tb_global.get(b, 0.0)) / (n + wpr._TRACK_BARRIER_K)
            else:
                shrunk[b] = tb_global.get(b, 0.0)
        center = float(np.mean(list(shrunk.values())))
        lookup[f"{trk}|{int(db)}"] = {
            b: float(max(-wpr._OWN_DELTA_CAP, min(wpr._OWN_DELTA_CAP, shrunk[b] - center))) for b in shrunk
        }
    for frame in frames:
        frame["track_barrier"] = [
            wpr._track_barrier_term(trk, dist, bar, fs, lookup)
            for trk, dist, bar, fs in zip(frame["track"], frame["cur_distance"],
                                          frame["barrier"], frame["field_size"])
        ]


def held_out_mae(cf, te, adj_terms):
    def predict(frame):
        return frame["_base"].to_numpy() + wpr._cap_adj_sum(
            frame[adj_terms].to_numpy()).sum(axis=1)
    return mean_absolute_error(te["target"], predict(te))


def run(since):
    labels = build_race_speed_labels(since)

    print("\nRebuilding training frame with own_pace populated (this reuses "
          "wpr_projection.py's own build_training_frame, may take a while)...")
    full = wpr.build_training_frame(FORM_CSV, verbose=True, race_speed_labels=labels, n_jobs=-1)

    # Only rows where own_pace could actually be non-zero (i.e. this run's
    # date is in the labelled window) are informative for this comparison -
    # outside that window own_pace is silently 0 for both models, which
    # would just dilute the measured effect, not invalidate it, but scoping
    # to the labelled window is a cleaner, more sensitive test.
    full = add_base(full)
    full["date"] = pd.to_datetime(full["date"])
    scoped = full[full["date"] >= pd.Timestamp(since)].copy()
    # track_barrier isn't produced by build_training_frame (unlike every
    # other ADJ_TERMS entry, it needs an actual fitted lookup - see
    # add_track_barrier) so it's excluded from this dropna and fitted/applied
    # separately, once per chronological direction below, on exactly the
    # columns it needs (barrier/field_size/career_avg/track/cur_distance).
    non_tb_terms = [t for t in wpr.ADJ_TERMS if t != "track_barrier"]
    scoped = scoped.dropna(subset=["target", "_base"] + non_tb_terms + ["own_pace",
                            "barrier", "field_size", "career_avg", "track", "cur_distance"])
    print(f"\nScoped rows for comparison: {len(scoped):,} "
          f"(own_pace non-zero on {(scoped['own_pace'] != 0).mean()*100:.1f}%)")

    mid = scoped["date"].quantile(0.5)
    h1, h2 = scoped[scoped["date"] < mid], scoped[scoped["date"] >= mid]
    print(f"H1: {len(h1):,} rows (< {mid.date()}), H2: {len(h2):,} rows (>= {mid.date()})")

    # track_barrier must be fit on whichever half is playing "fit" in each
    # direction and applied to both halves of that direction - a lookup fit
    # on H2 must never leak into the H1-fit/H2-validate direction or vice
    # versa, so each direction gets its own copies.
    h1_d1, h2_d1 = h1.copy(), h2.copy()
    add_track_barrier(h1_d1, [h1_d1, h2_d1])
    h1_d2, h2_d2 = h1.copy(), h2.copy()
    add_track_barrier(h2_d2, [h1_d2, h2_d2])

    baseline_terms = list(wpr.ADJ_TERMS)
    candidate_terms = baseline_terms + ["own_pace"]

    print("\n=== H1-fit/H2-validate direction ===")
    # Nothing is actually "fit" here - ADJ_TERMS are per-horse lookups, not
    # a regression - so "H1-fit" is really just reporting H1's own MAE for
    # context; H2 is the real held-out number, matching this file's own
    # convention (e.g. the exact-distance-match test earlier in the file).
    print(f"  baseline (7 terms):        H1 MAE={held_out_mae(h1_d1, h1_d1, baseline_terms):.4f}  "
          f"H2 (held-out) MAE={held_out_mae(h1_d1, h2_d1, baseline_terms):.4f}")
    print(f"  +own_pace (8 terms):       H1 MAE={held_out_mae(h1_d1, h1_d1, candidate_terms):.4f}  "
          f"H2 (held-out) MAE={held_out_mae(h1_d1, h2_d1, candidate_terms):.4f}")

    print("\n=== H2-fit/H1-validate direction ===")
    print(f"  baseline (7 terms):        H2 MAE={held_out_mae(h2_d2, h2_d2, baseline_terms):.4f}  "
          f"H1 (held-out) MAE={held_out_mae(h2_d2, h1_d2, baseline_terms):.4f}")
    print(f"  +own_pace (8 terms):       H2 MAE={held_out_mae(h2_d2, h2_d2, candidate_terms):.4f}  "
          f"H1 (held-out) MAE={held_out_mae(h2_d2, h1_d2, candidate_terms):.4f}")

    b_h2 = held_out_mae(h1_d1, h2_d1, baseline_terms)
    c_h2 = held_out_mae(h1_d1, h2_d1, candidate_terms)
    b_h1 = held_out_mae(h2_d2, h1_d2, baseline_terms)
    c_h1 = held_out_mae(h2_d2, h1_d2, candidate_terms)
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
