"""wpr_adj_slope_and_bucket_model_test.py - two related questions raised by
the user after "the population bucket lookup adjs are too minor":

1. Is _CALIB_ADJ_SLOPE (0.1791) STALE? It was fit once, months ago, on
   whatever ADJ_TERMS existed at the time - decomposed calibration:
   actual = a + b_base*base + b_adj*adjustment, fit on a train split,
   validated out-of-sample. Since then, trainer_merit, jockey_merit, and
   (today) pace_shape were added, and the settling model behind pace_shape
   was substantially improved. If the CURRENT adjustment sum is more
   informative than what 0.1791 was calibrated against, that slope is
   compressing every term (not just the bucket ones) toward "minor"
   regardless of any individual term's own accuracy - a much higher-
   leverage single fix than touching any one term. Re-derives b_adj fresh
   using EVERY current ADJ_TERM (including pace_shape) on real historical
   data, via the already-fitted lookups/models in wpr_models/config.json
   and wpr_models/pace_shape.joblib (no re-fitting of the terms themselves -
   isolates the calibration slope question from the terms' own accuracy).

2. Would converting track_barrier (the simplest, already-isolated bucket
   term) into a trained per-row model - the same fix that worked for
   settling_estimate and pace_shape - beat the current shrunk-lookup-table
   approach? Tests a small LightGBM model on (track, dist_band, barrier,
   field_size) predicting residual = target - career_avg, vs the shipped
   population-bucket lookup, bidirectionally.

RESULT (Sep 2026):

Question 1 - REJECTED, and the opposite of what was expected. A fresh 3-
parameter OLS fit (intercept + base slope + adj slope) on today's full
adjustment sum (including pace_shape) found b_adj=0.3447 on the
calibration fold - nearly double the shipped 0.1791, suggesting the slope
IS stale. But that fit does NOT generalize: held-out MAE with the fresh
fit is 5.7140, WORSE than the shipped slope's 5.6694. A slope-only sweep
(holding intercept=0, base=1x) confirms it: MAE gets WORSE at every
slope above the shipped one (0.25->5.6800, 0.50->5.7767, 1.00->6.2268),
and the single best held-out slope in the sweep was actually LOWER
(0.10->5.6668) than shipped. CONCLUSION: the adjustment layer's terms are
each real (they cleared their own bidirectional bars) but individually
noisy/weak signals - amplifying the whole sum (a higher slope) amplifies
their noise along with their signal, and shrinking toward zero is close
to already optimal for held-out accuracy. The "adjustments feel too
minor" complaint is NOT explained by a stale/over-conservative
calibration slope - if anything the current 0.1791 is already close to
(or slightly more generous than) the best achievable value. Raising it
would make the model WORSE, not better.

Question 2 - CONFIRMED, a real win. track_barrier as a trained model
(same features it already uses - distance, barrier, field_size, plus
track identity - quantile/median objective) beats the shipped shrunk-
lookup table in BOTH directions: residual MAE 6.6124->6.5488 (-0.0637)
forward, 5.6880->5.5976 (-0.0904) reversed. This is NOT the same
question wpr_adj_median_bucket_test.py answered (mean vs median WITHIN
the same bucket-lookup architecture, which failed) - this is bucket-
lookup architecture vs trained-model architecture entirely, and here
the trained model wins clearly, matching the exact lesson settling_
estimate.py and pace_shape already taught: a smooth per-row model
generalizes better than a rigid population bucket, once there's enough
data and real feature interactions to learn (track x distance x barrier
here, same as settling's own draw x tendency interaction).

NEXT: converting track_barrier to a trained model (and, on this
evidence, plausibly trainer_merit/jockey_merit/gear_change/closing_merit
too, each needing its own validation before shipping) is a real,
promising direction - raising the calibration slope is not. Left for
explicit confirmation before implementing (retrains the live model,
changes the "Barrier draw at this track and trip" row shown for every
resulted/upcoming runner).
"""
import numpy as np
import pandas as pd
import lightgbm as lgb
from sklearn.metrics import mean_absolute_error
import json

import wpr_projection as wpr


def build_frame():
    print("Building training frame (expensive step)...")
    D = wpr.build_training_frame("wpr_form_history.csv.gz", n_jobs=-1).dropna(
        subset=["target", "date"]).sort_values("date")
    print(f"  {len(D):,} rows")

    print("  merging trainer/jockey trailing win-rate...")
    name_map, tj_lookup = wpr._load_trainer_jockey_by_horse_date("wpr_form_history.csv.gz")
    tj_dates = D["date"].dt.strftime("%Y-%m-%d")
    tj_names = D["horse_id"].map(name_map)
    tj_vals = [tj_lookup.get((n, d), (np.nan, np.nan)) for n, d in zip(tj_names, tj_dates)]
    D["trainer_win_pct_365d"] = [t for t, j in tj_vals]
    D["jockey_win_pct_90d"] = [j for t, j in tj_vals]
    D["horse_lc"] = tj_names.astype(str).str.lower()

    from wpr_void import void_from_comment_only
    cv = D["comments_video"] if "comments_video" in D.columns else None
    cs = D["comments_steward"] if "comments_steward" in D.columns else None
    if cv is not None or cs is not None:
        cv = cv if cv is not None else [None] * len(D)
        cs = cs if cs is not None else [None] * len(D)
        void_mask = [void_from_comment_only(a, b)[0] for a, b in zip(cv, cs)]
        D = D[[not v for v in void_mask]].copy()
        print(f"  void filter: {len(D):,} rows remain")

    D["_base"] = wpr._BASE_BLEND_ALPHA * D["wpr_nett"] + (1 - wpr._BASE_BLEND_ALPHA) * D["ewm5"]
    D["_base"] = D["_base"].fillna(D["wpr_nett"]).fillna(D["ewm5"]).fillna(D["avg_last3"]).fillna(D["career_avg"])
    D = D.dropna(subset=["_base", "career_avg"]).copy()
    return D


def apply_current_adj_terms(D, cfg):
    """Apply the ALREADY-FITTED lookups (no refitting) for every ADJ_TERM
    that needs a population lookup, using wpr_projection's own live
    functions - own_* terms are already columns in D (computed by
    build_features itself)."""
    D["track_barrier"] = [
        wpr._track_barrier_term(trk, dist, bar, fs, cfg.get("track_barrier_lookup"))
        for trk, dist, bar, fs in zip(D["track"], D["cur_distance"], D["barrier"], D["field_size"])
    ]
    D["trainer_merit"] = [
        wpr._merit_term(wpr._merit_bucket(v, cfg.get("trainer_merit_edges")), cfg.get("trainer_merit_lookup"))
        for v in D["trainer_win_pct_365d"]
    ]
    D["jockey_merit"] = [
        wpr._merit_term(wpr._merit_bucket(v, cfg.get("jockey_merit_edges")), cfg.get("jockey_merit_lookup"))
        for v in D["jockey_win_pct_90d"]
    ]
    D["gear_change"] = [
        wpr._gear_change_term(b, cfg.get("gear_change_lookup"))
        for b in D["gear_changes"].apply(wpr._gear_change_bucket)
    ] if "gear_changes" in D.columns else 0.0
    D["closing_merit"] = [
        wpr._closing_merit_term(pairs, cfg.get("pace_baseline_lookup"))
        for pairs in D["closing_pairs"]
    ] if "closing_pairs" in D.columns else 0.0
    return D


def add_pace_shape(D, since):
    print(f"  building pace_shape ingredients (leak-safe, since {since})...")
    race_id_to_score = wpr._build_pace_shape_race_scores(since)
    settle_lookup = wpr._build_pace_shape_settle_lookup(since)
    D["pace_score"] = D["race_id"].map(race_id_to_score)
    D["predicted_rel_settle"] = [settle_lookup.get((h, d)) for h, d in zip(D["horse_lc"], D["date"])]
    D["settle_signal"] = (D["predicted_rel_settle"] - 0.5) * 2
    D["pace_signal"] = (D["pace_score"] - 0.5) * 2
    D["interaction"] = D["settle_signal"] * D["pace_signal"]

    import joblib
    model = joblib.load("wpr_models/pace_shape.joblib")
    feats = wpr._PACE_SHAPE_FEATURES
    has_all = D[feats].notna().all(axis=1)
    D["pace_shape"] = 0.0
    if has_all.any():
        D.loc[has_all, "pace_shape"] = model.predict(D.loc[has_all, feats])
    return D


def question_1_slope(D):
    print("\n=== Question 1: is the calibration slope stale? ===")
    with open("wpr_models/config.json") as f:
        cfg = json.load(f)
    D = apply_current_adj_terms(D, cfg)
    since = (D["date"].max() - pd.Timedelta(days=365)).strftime("%Y-%m-%d")
    D = add_pace_shape(D, since)

    D_scored = D.dropna(subset=wpr.ADJ_TERMS + ["_base", "target"]).copy()
    raw_sum = wpr._cap_adj_sum(D_scored[wpr.ADJ_TERMS].to_numpy()).sum(axis=1)
    D_scored["_raw_adj"] = raw_sum

    q1, q2 = D_scored["date"].quantile([0.70, 0.85])
    cf = D_scored[(D_scored["date"] >= q1) & (D_scored["date"] < q2)]
    te = D_scored[D_scored["date"] >= q2]
    print(f"  cf={len(cf):,} te={len(te):,}")

    # Fit actual = a + b_base*base + b_adj*adjustment on cf (OLS)
    X = np.column_stack([np.ones(len(cf)), cf["_base"], cf["_raw_adj"]])
    y = cf["target"].to_numpy()
    coef, *_ = np.linalg.lstsq(X, y, rcond=None)
    a, b_base, b_adj = coef
    print(f"  freshly fit: a={a:.3f}  b_base={b_base:.4f}  b_adj={b_adj:.4f}  (shipped b_adj={wpr._CALIB_ADJ_SLOPE})")

    # held-out MAE comparison: shipped slope vs freshly-fit slope
    pred_shipped = te["_base"] + te["_raw_adj"] * wpr._CALIB_ADJ_SLOPE
    pred_fresh = a + te["_base"] * b_base + te["_raw_adj"] * b_adj
    mae_shipped = mean_absolute_error(te["target"], pred_shipped)
    mae_fresh = mean_absolute_error(te["target"], pred_fresh)
    print(f"  held-out MAE, shipped slope (no intercept/base rescale): {mae_shipped:.4f}")
    print(f"  held-out MAE, freshly-fit (a + b_base*base + b_adj*adj): {mae_fresh:.4f}")

    # isolate JUST the slope question: keep intercept/base coefficient at
    # their current effective values (a=0, b_base=1 - the shipped design
    # applies no calibration to base), only vary b_adj
    print("\n  slope-only sweep (a=0, b_base=1, vary b_adj):")
    for slope in [0.10, wpr._CALIB_ADJ_SLOPE, 0.25, 0.35, 0.50, 0.70, 1.00]:
        pred = te["_base"] + te["_raw_adj"] * slope
        mae = mean_absolute_error(te["target"], pred)
        tag = " <- shipped" if abs(slope - wpr._CALIB_ADJ_SLOPE) < 1e-6 else ""
        print(f"    slope={slope:.2f}: MAE={mae:.4f}{tag}")

    return D_scored


def question_2_track_barrier_model(D_scored):
    print("\n=== Question 2: trained model vs bucket lookup for track_barrier ===")
    feats = ["cur_distance", "barrier", "field_size"]
    D_tb = D_scored.dropna(subset=feats + ["target", "career_avg", "track"]).copy()
    D_tb["track_code"] = D_tb["track"].astype("category").cat.codes

    for direction, (trn, te) in [
        ("A forward", (D_tb[D_tb["date"] < D_tb["date"].quantile(0.70)],
                       D_tb[D_tb["date"] >= D_tb["date"].quantile(0.85)])),
        ("B reversed", (D_tb[D_tb["date"] > D_tb["date"].quantile(0.30)],
                        D_tb[D_tb["date"] <= D_tb["date"].quantile(0.15)])),
    ]:
        # Compare the TERM's own MAE against the residual it's trying to
        # explain (same methodology as wpr_adj_median_bucket_test.py) -
        # both predictors face the same huge irreducible noise floor, so
        # the DIFFERENCE between them is what matters, not the absolute
        # MAE value.
        resid_trn = trn["target"] - trn["career_avg"]
        resid_te = te["target"] - te["career_avg"]
        mae_lookup = mean_absolute_error(resid_te, te["track_barrier"])

        model = lgb.LGBMRegressor(n_estimators=150, max_depth=3, learning_rate=0.05,
                                  num_leaves=8, random_state=42, verbosity=-1,
                                  objective="quantile", alpha=0.5)
        model.fit(trn[feats + ["track_code"]], resid_trn)
        pred_model = model.predict(te[feats + ["track_code"]])
        mae_model = mean_absolute_error(resid_te, pred_model)
        print(f"  [{direction}] residual MAE: shipped lookup={mae_lookup:.4f}  trained model={mae_model:.4f} "
              f"({'better' if mae_model < mae_lookup else 'worse'}, {mae_model - mae_lookup:+.4f})")


if __name__ == "__main__":
    D = build_frame()
    D_scored = question_1_slope(D)
    question_2_track_barrier_model(D_scored)
