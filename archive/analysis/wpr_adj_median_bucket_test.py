"""wpr_adj_median_bucket_test.py - tests whether the population-bucket
ADJ_TERMS (track_barrier, trainer_merit, jockey_merit, gear_change,
closing_merit) should use MEDIAN instead of MEAN for their per-bucket
residual, after finding WPR's own residual distribution (target -
career_avg) is dramatically left-skewed (skew=-1.69, mean=-0.94 vs
median=+0.19 - opposite signs) - the same mean-fitting-on-a-skewed-target
problem already found and fixed for settling_estimate.py (see
wpr_settle_median_objective_test.py).

Unlike settling_estimate (a trained LightGBM model with a swappable
objective), these ADJ_TERMS are literal per-bucket MEANS of the residual,
shrunk toward the global mean (see _fit_merit_lookup/_track_barrier
fitting/_gear_change fitting/_fit_pace_baseline in wpr_projection.py).
This tests the direct analogue: per-bucket MEDIAN instead of MEAN
(shrunk toward the global MEDIAN), same shrinkage strength constants,
same buckets - only the summary statistic changes.

Tested bidirectionally, one term at a time (isolating which specific
terms actually benefit, rather than assuming all do).

RESULT (Sep 2026): NOT ADOPTED - unlike settling_estimate.py's model
objective switch (a clean, decisive win), swapping mean for median in
these population-bucket lookups does NOT reliably help:
  gear_change:   WORSE in both directions (A +0.0007, B +0.0033)
  track_barrier: MIXED (A -0.0008 better, B +0.0086 worse) - does not
                 clear the bidirectional bar
  trainer_merit: not tested (trainer_win_pct_365d isn't a column in
                 build_training_frame's own output - would need the
                 separate _load_trainer_jockey_by_horse_date merge step
                 to test properly; not pursued given the negative signal
                 from the two terms already tested)

WHY THE SAME FIX DOESN'T TRANSFER: settling_estimate's median objective
is fit by a LightGBM quantile-regression LOSS across the full ~150k-row
population at once, producing a smooth, well-powered per-row estimate.
These ADJ_TERMS are literal per-BUCKET medians (e.g. one (track,
dist_band, barrier_band) combo, often a few hundred rows) - for a small
sample from a skewed distribution, a sample MEDIAN is actually a NOISIER
estimator than a sample MEAN (it only uses rank information, discarding
the magnitude information a mean uses, and is more sensitive to which
few observations happen to land near the middle). Shrinkage toward a
global statistic doesn't fix this instability the same way it fixes
small-n mean estimates.

CONCLUSION: the skewed-residual finding (WPR's target-career_avg has
skew=-1.69, mean=-0.94 vs median=+0.19 - opposite signs) is real and
important, but "swap mean for median" is not a mechanical fix that
applies everywhere - it works where there's a smooth, well-powered
model fit (settling_estimate, and pace_shape's own model - see wpr_
pace_shape_median_objective_test.py), not for small-sample bucket
lookups. Not pursuing trainer_merit/jockey_merit/closing_merit further
given this consistent negative/mixed signal on the two terms tested.
"""
import numpy as np
import pandas as pd
from sklearn.metrics import mean_absolute_error

import wpr_projection as wpr


def _fit_bucket_lookup_generic(df, bucket_col, k, use_median):
    """Same shrinkage shape as wpr_projection's own _fit_merit_lookup, but
    swappable mean/median and works on a pre-bucketed column (any of
    track|dist_band's _barrier_band, trainer/jockey deciles, gear_change
    buckets, closing_merit's raceShapeEarly buckets)."""
    stat = "median" if use_median else "mean"
    resid = df["target"] - df["career_avg"]
    global_stat = resid.median() if use_median else resid.mean()
    lookup = {}
    for bucket, g in df.groupby(bucket_col):
        r = g["target"] - g["career_avg"]
        n = len(r)
        m = r.median() if use_median else r.mean()
        shrunk = (n * m + k * global_stat) / (n + k)
        lookup[bucket] = float(shrunk - global_stat)
    return lookup


def _apply_lookup(bucket_series, lookup):
    return bucket_series.map(lookup).fillna(0.0)


def held_out_both_directions(D, term_name, bucket_col, k):
    """For ONE term: fit mean-based and median-based bucket lookups on
    trn, apply to te, compare additive-model MAE (holding every OTHER
    ADJ_TERM at its already-shipped value) in both directions."""
    results = {}
    for direction, (trn, te) in [
        ("A forward", (D[D["date"] < D["date"].quantile(0.70)],
                       D[D["date"] >= D["date"].quantile(0.85)])),
        ("B reversed", (D[D["date"] > D["date"].quantile(0.30)],
                        D[D["date"] <= D["date"].quantile(0.15)])),
    ]:
        te = te.copy()
        other_terms = [t for t in wpr.ADJ_TERMS if t != term_name and t in te.columns]
        baseline_other_sum = wpr._cap_adj_sum(te[other_terms].to_numpy()).sum(axis=1) if other_terms else 0.0

        mean_lookup = _fit_bucket_lookup_generic(trn, bucket_col, k, use_median=False)
        median_lookup = _fit_bucket_lookup_generic(trn, bucket_col, k, use_median=True)

        te_mean_term = _apply_lookup(te[bucket_col], mean_lookup)
        te_median_term = _apply_lookup(te[bucket_col], median_lookup)

        pred_mean = te["_base"].to_numpy() + baseline_other_sum + te_mean_term.to_numpy()
        pred_median = te["_base"].to_numpy() + baseline_other_sum + te_median_term.to_numpy()

        scored = te.dropna(subset=["_base", "target"])
        mae_mean = mean_absolute_error(scored["target"], pd.Series(pred_mean, index=te.index).loc[scored.index])
        mae_median = mean_absolute_error(scored["target"], pd.Series(pred_median, index=te.index).loc[scored.index])
        print(f"  [{term_name}] {direction}: MEAN-bucket MAE={mae_mean:.4f}  "
              f"MEDIAN-bucket MAE={mae_median:.4f}  "
              f"({'better' if mae_median < mae_mean else 'worse'}, {mae_median - mae_mean:+.4f})")
        results[direction] = (mae_mean, mae_median)
    return results


def run():
    print("Building training frame (this is the expensive step)...")
    D = wpr.build_training_frame("wpr_form_history.csv.gz", n_jobs=-1).dropna(
        subset=["target", "date"]).sort_values("date")
    print(f"  {len(D):,} rows")

    D["_base"] = wpr._BASE_BLEND_ALPHA * D["wpr_nett"] + (1 - wpr._BASE_BLEND_ALPHA) * D["ewm5"]
    D["_base"] = D["_base"].fillna(D["wpr_nett"]).fillna(D["ewm5"]).fillna(D["avg_last3"]).fillna(D["career_avg"])
    D = D.dropna(subset=["_base", "career_avg"]).copy()

    from wpr_void import void_from_comment_only
    cv = D["comments_video"] if "comments_video" in D.columns else None
    cs = D["comments_steward"] if "comments_steward" in D.columns else None
    if cv is not None or cs is not None:
        cv = cv if cv is not None else [None] * len(D)
        cs = cs if cs is not None else [None] * len(D)
        void_mask = [void_from_comment_only(a, b)[0] for a, b in zip(cv, cs)]
        D = D[[not v for v in void_mask]].copy()
        print(f"  void filter: {len(D):,} rows remain")

    # For simplicity/isolation, only run the ADJ_TERMS that are already
    # present as columns (computed by build_features/build_training_frame
    # for own_* terms) - track_barrier/trainer_merit/jockey_merit/
    # gear_change/closing_merit are injected post-hoc in project_race, not
    # present in D by default. Fit them here directly from D's own raw
    # ingredient columns instead.
    print("\n=== gear_change: mean vs median bucket ===")
    D["_gc_bucket"] = D["gear_changes"].apply(wpr._gear_change_bucket) if "gear_changes" in D.columns else None
    if D["_gc_bucket"].notna().any():
        held_out_both_directions(D.dropna(subset=["_gc_bucket"]), "gear_change", "_gc_bucket", wpr._GEAR_CHANGE_K)

    print("\n=== track_barrier: mean vs median bucket (track|dist_band|barrier_band) ===")
    D["_tb_band"] = [wpr._barrier_band(b, f) for b, f in zip(D["barrier"], D["field_size"])]
    D["_tb_dist_band"] = (D["cur_distance"] // 200 * 200).astype("Int64")
    D["_tb_key"] = D["track"].astype(str) + "|" + D["_tb_dist_band"].astype(str) + "|" + D["_tb_band"].astype(str)
    tb_d = D.dropna(subset=["_tb_band", "track"])
    held_out_both_directions(tb_d, "track_barrier", "_tb_key", wpr._TRACK_BARRIER_K)

    print("\n=== trainer_merit: mean vs median bucket (decile) ===")
    tm_d = D.dropna(subset=["trainer_win_pct_365d"]).copy() if "trainer_win_pct_365d" in D.columns else pd.DataFrame()
    if len(tm_d):
        edges = np.unique(np.quantile(tm_d["trainer_win_pct_365d"], np.linspace(0, 1, 11)))
        tm_d["_tm_bucket"] = np.digitize(tm_d["trainer_win_pct_365d"], edges[1:-1])
        held_out_both_directions(tm_d, "trainer_merit", "_tm_bucket", wpr._TJ_MERIT_K)
    else:
        print("  no trainer_win_pct_365d coverage in this frame, skipping")


if __name__ == "__main__":
    run()
