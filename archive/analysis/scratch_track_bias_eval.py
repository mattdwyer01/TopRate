"""
scratch_track_bias_eval.py
---------------------------
One-off, throwaway comparison: does adding track_bias_score (from the new
race_results_*.csv.gz-derived _build_track_bias_lookup) to the pace_shape
ADJ_TERM actually improve held-out MAE over the currently-shipped 4-feature
model, on the SAME target (target - career_avg) and SAME leak-safe 365-day
coverage window pace_shape's own real fit already uses?

Does NOT modify wpr_projection.py's live functions, does NOT touch
wpr_models/*.joblib. Read-only comparison, safe to run repeatedly.

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np
import pandas as pd
import lightgbm as lgb
from sklearn.metrics import mean_absolute_error

import wpr_projection as wp

print("Building training frame (this takes a while - same as a real retrain)...")
D = wp.build_training_frame("wpr_form_history.csv.gz", verbose=True).dropna(
    subset=["target", "date"]).sort_values("date")
print(f"{len(D):,} training rows")

name_map, _ = wp._load_trainer_jockey_by_horse_date("wpr_form_history.csv.gz")

since = (D["date"].max() - pd.Timedelta(days=365)).strftime("%Y-%m-%d")
print(f"\npace_shape leak-safe window: since {since}")
race_id_to_score = wp._build_pace_shape_race_scores(since)
settle_lookup = wp._build_pace_shape_settle_lookup(since)

D["pace_score"] = D["race_id"].map(race_id_to_score)
D["horse_lc"] = D["horse_id"].map(name_map).astype(str).str.lower()
D["predicted_rel_settle"] = [settle_lookup.get((h, d)) for h, d in zip(D["horse_lc"], D["date"])]
D["settle_signal"] = (D["predicted_rel_settle"] - 0.5) * 2
D["pace_signal"] = (D["pace_score"] - 0.5) * 2
D["interaction"] = D["settle_signal"] * D["pace_signal"]

print("Building track_bias_lookup from race_results_*.csv.gz...")
bias_lookup = wp._build_track_bias_lookup()
D["track_bias_score"] = [
    wp._track_bias_score(trk, going, rail, bias_lookup)
    for trk, going, rail in zip(D["track"], D["going"], D.get("rail_position"))
]
print(f"track_bias_score nonzero: {(D['track_bias_score'] != 0).mean()*100:.1f}% of rows")

cov = D[D["date"] >= pd.Timestamp(since)].dropna(
    subset=["settle_signal", "pace_signal", "interaction", "target", "career_avg"])
print(f"\ncovered rows (has pace_score + predicted_rel_settle): {len(cov):,}")

cutoff = cov["date"].quantile(0.70)
trn = cov[cov["date"] < cutoff]
test = cov[cov["date"] >= cutoff]
print(f"train: {len(trn):,} rows (before {cutoff.date()}), test: {len(test):,} rows (on/after)")

BASELINE_FEATS = ["settle_signal", "pace_signal", "interaction", "field_size"]
NEW_FEATS = BASELINE_FEATS + ["track_bias_score"]

def fit_and_eval(feats, label):
    model = lgb.LGBMRegressor(n_estimators=150, max_depth=3, learning_rate=0.05,
                              num_leaves=8, random_state=42, verbosity=-1,
                              objective="quantile", alpha=0.5)
    model.fit(trn[feats], trn["target"] - trn["career_avg"])
    pred_resid = model.predict(test[feats])
    pred_target = test["career_avg"] + pred_resid
    mae = mean_absolute_error(test["target"], pred_target)
    # Also: how much does this term move projections on average (sanity, not
    # a la the real serving code's own centering - just a magnitude check)
    print(f"  {label}: held-out MAE (career_avg + term vs actual target) = {mae:.4f}  "
          f"(term itself: mean={pred_resid.mean():.4f}, std={pred_resid.std():.4f})")
    return mae, model

print("\n--- Held-out comparison (same test set both models) ---")
mae_base, _ = fit_and_eval(BASELINE_FEATS, "baseline (4 features, no track_bias)")
mae_new, model_new = fit_and_eval(NEW_FEATS, "with track_bias_score (5 features)")

print(f"\nDelta: {mae_new - mae_base:+.4f} MAE ({'IMPROVEMENT' if mae_new < mae_base else 'WORSE'})")
print("\nFeature importances (with track_bias_score):")
for feat, imp in sorted(zip(NEW_FEATS, model_new.feature_importances_), key=lambda x: -x[1]):
    print(f"  {feat:20s} {imp}")
