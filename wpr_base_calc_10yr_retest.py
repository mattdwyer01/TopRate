"""
wpr_base_calc_10yr_retest.py - retests the own-history anchor design
(ewm3/ewm5 span choice, and every other standalone base-signal candidate)
using race_results_2017-2026.csv.gz's genuine ~10-year depth, instead of
wpr_form_history.csv.gz's recency-skewed sample.

WHY (see chat, Sep 2026): wpr_form_history.csv.gz nominally spans
2016-09 to 2026-09, but 2016-2020 combined is under 3,000 of 325,000+
rows - 98%+ of it is 2022 onward. wpr_best_anchor_signal_test.py's own
K=4 chronological folds are consequently near-worthless as an ERA-
stability check: fold 0 of 4 already contains most of 2022-2023, folds
1-3 are almost entirely 2024-2026. The user (who does not trust the
live additive model's volatility) asked whether the base calc has ever
been retested against real decade-deep data - it had not.

race_results_2017-2026.csv.gz (built this session for the atw backfill
and track_bias_score) IS that deep dataset - dense from 2018 onward,
and its schema is (with two harmless exceptions - see below) identical
to what build_training_frame() already expects, so this script does NOT
reimplement any feature: it points build_training_frame() straight at a
combined race_results file, reusing build_features() (this codebase's
single source of truth) exactly as-is. scrape_date and weight_handicap
are the only columns wpr_form_history.csv.gz has that race_results
lacks - both are optional (scrape_date's absence just skips a dedup
step that is a no-op anyway on a results dump with no re-scrapes;
weight_handicap is never read by build_features).

ERA FOLDS: hardcoded date-range eras (2017-2020, 2021-2022, 2023, 2024,
2025-2026), NOT the usual equal-sized quantile folds - an equal-sized
split would just reproduce the recency skew this script exists to get
away from. Each candidate is scored leave-one-era-out (train = every
OTHER era, single OLS slope/intercept per era per candidate, same
"fresh calibration per fold, never reused" discipline every prior
validation in this codebase uses - see wpr_best_anchor_signal_test.py).
Per-era MAE + stability (std across eras) is the actual answer to "is
this design volatile", not just the average.

ATW SIDE-TEST: race_results also carries atw (Sep 2026 backfill - wpr
is a WFA rating, atw converts it to actual-weight-carried), but only
for Set Weight races (weight_restriction=SW, ~22% of rows) so far.
Restricting a horse's entire history to SW-only rows would fragment
continuity for most horses (most horses run a mix of race types), so
instead this builds an alternate own-history quality series q = atw
where available else raw wpr, and recomputes an ewm5-equivalent from q
via a vectorized groupby-ewm-shift(1) - mathematically identical to
build_features' own g.iloc[:i]-then-.ewm(span=k).mean().iloc[-1] loop,
since a SPAN-based (not time-based) ewm is a pure order-dependent
recursion with no reference to absolute dates. Verified against build_
features' own ewm5 output (raw-wpr case) before trusting the atw
variant - see the "VALIDATING VECTORIZED EWM" section.

wpr_nett is NOT available this deep (it only exists in toprate_
runners.csv's recent daily snapshots, not in race_results at all) -
included in the standalone sweep anyway so its near-zero old-era
coverage is visible, not silently assumed away.

Checkpoints the combined CSV and the built D to the scratchpad disk
(this sandbox has repeatedly killed long-running background builds
this session, not OOM - see chat) so an interrupted run's relaunch
skips the expensive rebuild.

Does NOT modify wpr_projection.py, does NOT touch wpr_models/*.joblib
or config.json. Read-only, safe to run repeatedly.

NO EM DASHES policy: hyphens only in this file.
"""
import pickle
from pathlib import Path

import numpy as np
import pandas as pd

import wpr_projection as wp

try:
    from wpr_void import void_from_comment_only as _void_from_comment_only
except ImportError:
    _void_from_comment_only = None

SCRATCH = Path("/tmp/claude-0/-home-user-TopRate/95a262de-71bd-5daf-b05e-b7e3031f09dd/scratchpad")
COMBINED_CSV = SCRATCH / "race_results_combined_2017_2026.csv.gz"
D_CACHE = SCRATCH / "wpr_10yr_D_cache.pkl"
BATCH_DIR = SCRATCH / "wpr_10yr_batches"
YEARS = range(2017, 2027)
REPO = Path("/home/user/TopRate")

# Full 87,404-horse population, batched rather than downsampled (user's
# explicit call, Sep 2026 - see chat) - two earlier full-population, all-
# at-once attempts (n_jobs=2, n_jobs=1) each burned 2+ hours without
# finishing (one OOM-killed, one projected at ~4 more hours from its
# measured per-horse rate), because build_training_frame() accumulates
# every horse's feature rows into ONE Python list before the final
# DataFrame conversion - that accumulation scales with total horse count
# regardless of n_jobs. Splitting the 87,404 horses into fixed-size
# batches and calling build_training_frame() separately per batch (each
# batch written as its own temp combined CSV, each batch's D pickled to
# BATCH_DIR, concatenated at the very end) bounds peak memory to ONE
# batch's worth - close to the ORIGINAL successful retrain's scale
# (18,647 horses, 325k rows, which ran safely in parallel) - while still
# processing every horse in the full population, not a subset.
BATCH_SIZE = 12000

STANDALONE_SIGNALS = ["wpr_nett", "ewm3", "ewm5", "avg_last3", "avg_last5",
                       "career_avg", "best3", "recent5_max"]
EXTRA_SPANS = [7, 10, 15]  # candidate windows NOT in production, tested here only

ERA_BOUNDS = [
    ("2017-2020", "2017-01-01", "2021-01-01"),
    ("2021-2022", "2021-01-01", "2023-01-01"),
    ("2023",      "2023-01-01", "2024-01-01"),
    ("2024",      "2024-01-01", "2025-01-01"),
    ("2025-2026", "2025-01-01", "2027-01-01"),
]


# Columns actually needed: build_training_frame()'s own "keep" list (see
# its source), "horse" (its wpr_nett merge key, dropped after that merge),
# plus atw/weight_restriction for this script's own side-test. Everything
# else (pedigree, prices, race names, jockey/trainer names, venue...) is
# pure memory bloat at this row count (1.3M+) - the first attempt at this
# 4x-larger-than-usual build got OOM-killed by the sandbox's memory cgroup
# (confirmed via dmesg, a real kill this time - not this session's earlier
# false alarms) carrying all 87 original race_results columns through.
_SECT_COLS = ["sect_i_time", "sect_ld_early", "sect_i_early", "sect_i_to600",
              "sect_i_to800", "sect_i_l200", "sect_i_l400", "sect_i_l600",
              "sect_i_l800", "sect_i_400_200", "sect_i_600_400",
              "sect_i_800_400", "sect_i_800_600"]
NEEDED_COLS = [
    "horse_id", "horse", "date", "race_id", "run_id", "wpr", "distance",
    "going", "track", "trackGrading", "positionSettled", "position800m",
    "position600m", "margin800m", "margin600m", "margin400m", "marginFinish",
    "isBarrierTrial", "barrier", "field_size", "raceShapeEarly",
    "raceShapeMid", "raceShapeLate", "race_class", "comments_video",
    "comments_steward", "gear_changes", "atw", "weight_restriction",
    "rail_position", "positionFinish", "priceStarting",
] + _SECT_COLS


def load_combined():
    if COMBINED_CSV.exists():
        print(f"Loading cached combined race_results from {COMBINED_CSV} ...")
        combined = pd.read_csv(COMBINED_CSV, low_memory=False)
        print(f"  {len(combined):,} rows")
        return combined
    print("Concatenating race_results_2017.csv.gz .. race_results_2026.csv.gz "
          f"(trimmed to {len(NEEDED_COLS)} needed columns) ...")
    frames = []
    for y in YEARS:
        f = REPO / f"race_results_{y}.csv.gz"
        if not f.exists():
            continue
        cols = pd.read_csv(f, nrows=0).columns
        use = [c for c in NEEDED_COLS if c in cols]
        df = pd.read_csv(f, low_memory=False, usecols=use)
        frames.append(df)
        print(f"  {y}: {len(df):,} rows")
    combined = pd.concat(frames, ignore_index=True)
    print(f"Combined (full population): {len(combined):,} rows, "
          f"{combined['horse_id'].nunique():,} horses -> caching to {COMBINED_CSV} ...")
    combined.to_csv(COMBINED_CSV, index=False)
    return combined


def build_D(combined):
    """Builds the full-population training frame in horse-id batches (see
    BATCH_SIZE comment above for why) - each batch is written as its own
    temp combined CSV, fed through wp.build_training_frame() exactly as a
    normal (much smaller) retrain would be, pickled to BATCH_DIR, then
    freed before the next batch starts. Resumable: a batch whose pickle
    already exists on disk is skipped, so a killed/interrupted run picks
    up at the next unfinished batch instead of restarting from scratch."""
    if D_CACHE.exists():
        print(f"Loading cached D from {D_CACHE} ...")
        with open(D_CACHE, "rb") as f:
            return pickle.load(f)

    BATCH_DIR.mkdir(parents=True, exist_ok=True)
    all_horses = sorted(combined["horse_id"].dropna().unique())
    batches = [all_horses[i:i + BATCH_SIZE] for i in range(0, len(all_horses), BATCH_SIZE)]
    print(f"\n{len(all_horses):,} horses split into {len(batches)} batches of "
          f"up to {BATCH_SIZE:,} each (n_jobs=-1 per batch, safe at this scale) ...")

    # Each batch is pickled to disk and then DROPPED from memory (not kept
    # in a running list) - only the final concat below re-reads everything
    # from disk, once, after every batch is done. Keeping finished batches
    # resident in memory throughout the loop (an earlier version of this
    # function did) was the same accumulation pattern that caused trouble
    # before, just slower - by batch 6/9 memory was down to 2.3GB free.
    for i, horse_ids in enumerate(batches):
        batch_pkl = BATCH_DIR / f"batch_{i:03d}.pkl"
        if batch_pkl.exists():
            print(f"  batch {i+1}/{len(batches)}: cached, skipping")
            continue
        print(f"  batch {i+1}/{len(batches)}: {len(horse_ids):,} horses ...")
        batch_csv = BATCH_DIR / f"batch_{i:03d}.csv.gz"
        combined[combined["horse_id"].isin(set(horse_ids))].to_csv(batch_csv, index=False)
        batch_D = wp.build_training_frame(str(batch_csv), verbose=True, n_jobs=-1)
        batch_D["date"] = pd.to_datetime(batch_D["date"])
        print(f"    {len(batch_D):,} training rows from this batch")
        with open(batch_pkl, "wb") as f:
            pickle.dump(batch_D, f)
        batch_csv.unlink()  # done with the temp CSV, only the pickle is kept
        del batch_D

    print("\nAll batches done - loading each pickle once for the final concat ...")
    batch_frames = []
    for i in range(len(batches)):
        with open(BATCH_DIR / f"batch_{i:03d}.pkl", "rb") as f:
            batch_frames.append(pickle.load(f))
    D = pd.concat(batch_frames, ignore_index=True)
    print(f"All batches combined: {len(D):,} training rows total")
    with open(D_CACHE, "wb") as f:
        pickle.dump(D, f)
    return D


def vectorized_ewm(combined, span, value_col, void_mask_col=None):
    """Point-in-time ewm(span) of value_col, leak-safe (shift(1) within
    each horse, sorted by date). See module docstring for why this is
    mathematically identical to build_features' own per-horse loop for a
    span-based (not time-based) ewm."""
    cols = ["horse_id", "date", "race_id", value_col]
    c = combined[cols].copy()
    c["date"] = pd.to_datetime(c["date"], errors="coerce")
    c[value_col] = pd.to_numeric(c[value_col], errors="coerce")
    if void_mask_col is not None:
        c.loc[void_mask_col, value_col] = np.nan
    c = c.dropna(subset=["date"]).sort_values(["horse_id", "date"])
    out_col = f"ewm{span}_{value_col}"
    c[out_col] = c.groupby("horse_id")[value_col].transform(
        lambda s: s.ewm(span=span).mean().shift(1))
    c["race_id"] = c["race_id"].astype(str)
    return c[["horse_id", "date", "race_id", out_col]].drop_duplicates(
        subset=["horse_id", "date", "race_id"])


def compute_void_mask(combined):
    if _void_from_comment_only is None:
        return pd.Series(False, index=combined.index)
    cv = combined.get("comments_video")
    cs = combined.get("comments_steward")
    if cv is None and cs is None:
        return pd.Series(False, index=combined.index)
    if cv is None:
        cv = pd.Series([None] * len(combined), index=combined.index)
    if cs is None:
        cs = pd.Series([None] * len(combined), index=combined.index)
    return pd.Series([_void_from_comment_only(a, b)[0] for a, b in zip(cv, cs)],
                      index=combined.index)


def fit_ols(x, y):
    mask = x.notna() & y.notna()
    if mask.sum() < 30:
        return 0.0, 1.0
    slope, intercept = np.polyfit(x[mask], y[mask], 1)
    return intercept, slope


def mae_for_series(train_x, train_y, test_x, test_y):
    intercept, slope = fit_ols(train_x, train_y)
    pred = intercept + slope * test_x
    mask = test_y.notna() & pred.notna()
    if mask.sum() == 0:
        return float("nan"), 0
    return float((test_y[mask] - pred[mask]).abs().mean()), int(mask.sum())


def assign_era(dates):
    era = pd.Series("unassigned", index=dates.index)
    for name, lo, hi in ERA_BOUNDS:
        mask = (dates >= pd.Timestamp(lo)) & (dates < pd.Timestamp(hi))
        era[mask] = name
    return era


def run_sweep(D, candidates, label):
    print(f"\n{'='*90}\n{label} (leave-one-era-out, single OLS slope/intercept per era)\n{'='*90}")
    era_names = [e[0] for e in ERA_BOUNDS]
    results = {}
    for sig in candidates:
        if sig not in D.columns:
            print(f"  {sig}: not found, skipped")
            continue
        era_maes, era_ns = [], []
        for era in era_names:
            train = D[D["_era"] != era]
            test = D[D["_era"] == era]
            if len(test) < 50:
                era_maes.append(float("nan"))
                era_ns.append(0)
                continue
            mae, n = mae_for_series(train[sig], train["target"], test[sig], test["target"])
            era_maes.append(mae)
            era_ns.append(n)
        results[sig] = era_maes
        valid = [m for m in era_maes if m == m]
        avg = np.mean(valid) if valid else float("nan")
        std = np.std(valid) if len(valid) > 1 else float("nan")
        cov = D[sig].notna().mean() * 100
        per_era = "  ".join(f"{e}={m:.3f}" if m == m else f"{e}=n/a" for e, m in zip(era_names, era_maes))
        print(f"  {sig:<16} avg={avg:.4f}  std={std:.4f}  coverage={cov:5.1f}%   [{per_era}]")
    return results


def run():
    combined = load_combined()
    D = build_D(combined)

    print("\nMerging atw / weight_restriction from race_results by (horse_id, date, race_id)...")
    key_cols = ["horse_id", "date", "race_id"]
    side = combined[key_cols + ["atw", "weight_restriction"]].copy()
    side["date"] = pd.to_datetime(side["date"], errors="coerce")
    side["race_id"] = side["race_id"].astype(str)
    side = side.dropna(subset=["date"]).drop_duplicates(subset=key_cols, keep="first")
    D = D.copy()
    D["race_id"] = D["race_id"].astype(str)
    before = len(D)
    D = D.merge(side, on=key_cols, how="left")
    assert len(D) == before, "atw/weight_restriction merge changed row count"
    print(f"  cur_atw coverage: {D['atw'].notna().mean()*100:.1f}%  "
          f"(weight_restriction=SW coverage: {(D['weight_restriction']=='SW').mean()*100:.1f}%)")

    print("\nComputing void mask on combined (matches build_features' own void filter)...")
    void_mask = compute_void_mask(combined)
    print(f"  {int(void_mask.sum()):,} / {len(combined):,} rows flagged void")

    print("\nVALIDATING VECTORIZED EWM: recomputing ewm5 from raw wpr the vectorized "
          "way and comparing to build_features' own ewm5 column in D...")
    check = vectorized_ewm(combined, 5, "wpr", void_mask_col=void_mask)
    D = D.merge(check, on=key_cols, how="left")
    both = D["ewm5"].notna() & D["ewm5_wpr"].notna()
    diff = (D.loc[both, "ewm5"] - D.loc[both, "ewm5_wpr"]).abs()
    print(f"  {both.sum():,} rows comparable, mean abs diff={diff.mean():.4f}, "
          f"corr={D.loc[both,'ewm5'].corr(D.loc[both,'ewm5_wpr']):.4f}")
    D = D.drop(columns=["ewm5_wpr"])

    print("\nBuilding extra-span candidates (not in production, tested here only)...")
    for span in EXTRA_SPANS:
        c = vectorized_ewm(combined, span, "wpr", void_mask_col=void_mask)
        c = c.rename(columns={f"ewm{span}_wpr": f"ewm{span}"})
        D = D.merge(c, on=key_cols, how="left")

    print("\nBuilding atw-blended anchor (q = atw where available else raw wpr)...")
    combined["q_atw_or_wpr"] = pd.to_numeric(combined["atw"], errors="coerce").fillna(
        pd.to_numeric(combined["wpr"], errors="coerce"))
    for span in (3, 5):
        c = vectorized_ewm(combined, span, "q_atw_or_wpr", void_mask_col=void_mask)
        D = D.merge(c, on=key_cols, how="left")

    D["_era"] = assign_era(D["date"])
    print(f"\nEra row counts:\n{D['_era'].value_counts().reindex([e[0] for e in ERA_BOUNDS])}")

    print(f"\nTotal D rows: {len(D):,}")

    run_sweep(D, STANDALONE_SIGNALS + [f"ewm{s}" for s in EXTRA_SPANS],
              "STANDALONE SIGNALS incl. extra-span candidates - full 10yr depth")

    print(f"\n{'='*90}\nATW SIDE-TEST: raw-wpr ewm vs atw-blended ewm (same span)\n{'='*90}")
    run_sweep(D, ["ewm3", "ewm3_q_atw_or_wpr", "ewm5", "ewm5_q_atw_or_wpr"],
              "atw-blended vs raw-wpr anchor")

    print(f"\n{'='*90}\nATW SIDE-TEST, SW-ONLY SCOPE (rows where atw actually differs from wpr history)\n{'='*90}")
    sw_scope = D[D["atw"].notna()]
    print(f"  {len(sw_scope):,} rows where TODAY's run has an atw value")
    run_sweep(sw_scope, ["ewm3", "ewm3_q_atw_or_wpr", "ewm5", "ewm5_q_atw_or_wpr"],
              "atw-blended vs raw-wpr anchor, SW-today-only rows")

    print("\nSame multiple-comparisons caveat as every backtest in this codebase:")
    print("treat this as a hypothesis, not a result to ship blind.")
    print("\nDone.")


if __name__ == "__main__":
    run()
