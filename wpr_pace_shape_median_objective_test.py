"""wpr_pace_shape_median_objective_test.py - tests switching pace_shape's
own LightGBM model (wpr_projection.py's _fit_pace_shape_model) from
LightGBM's default objective (L2/mean-fitting) to quantile regression at
alpha=0.5 (median), the same fix that was BY FAR the biggest validated
win for settling_estimate.py (see wpr_settle_median_objective_test.py).

MOTIVATION: pace_shape's own model predicts residual = target -
career_avg directly - the EXACT quantity found (Sep 2026) to be
dramatically right... left-skewed across the whole WPR population
(skew=-1.69, mean=-0.94 vs median=+0.19, opposite signs - see
wpr_adj_median_bucket_test.py). pace_shape's model was built this same
session using LGBMRegressor with no objective argument (default
L2/mean), the exact same untouched-default pattern settling_estimate.py
had. Unlike the population-BUCKET ADJ_TERMS (wpr_adj_median_bucket_test.py
- median did NOT help there, small-sample bucket medians are noisier
than bucket means), pace_shape is a smooth, well-powered per-row
LightGBM fit across ~67k covered rows - the same statistical setting
where the fix worked for settling_estimate, not the bucket-lookup
setting where it didn't.

Reuses the NOW-UPDATED settling_estimate model (median objective + margin
feature + tactical exclusion, already shipped) for the leak-safe
predicted_rel_settle reconstruction, via wpr_projection.py's own already-
built _build_pace_shape_race_scores/_build_pace_shape_settle_lookup.

RESULT (Sep 2026): CLEARS THE BAR - direction A: MAE 6.4749 -> 6.4049
(-0.0700), direction B: MAE 5.9042 -> 5.8196 (-0.0846). Both real,
meaningful improvements (~1.1-1.4% relative on this residual's own
scale) - confirms the median-objective fix generalizes to pace_shape's
own model, the second (of two tested) smooth per-row LightGBM fit in
this codebase to benefit from it, matching settling_estimate.py's own
result and NOT matching the negative/mixed result found for the
population-BUCKET ADJ_TERMS (wpr_adj_median_bucket_test.py) - consistent
with the "smooth model fit, not small-sample bucket lookup" distinction
that result's docstring draws.

ADOPTED - see wpr_projection.py's _fit_pace_shape_model, updated to use
objective="quantile", alpha=0.5.
"""
import numpy as np
import pandas as pd
import lightgbm as lgb
from sklearn.metrics import mean_absolute_error

import wpr_projection as wpr


def _fit_eval(trn, te, features, target_col, objective_kwargs):
    trn_u = trn.dropna(subset=features + [target_col])
    te_u = te.dropna(subset=features + [target_col])
    m = lgb.LGBMRegressor(n_estimators=150, max_depth=3, learning_rate=0.05,
                          num_leaves=8, random_state=42, verbosity=-1, **objective_kwargs)
    m.fit(trn_u[features], trn_u[target_col])
    pred = m.predict(te_u[features])
    return mean_absolute_error(te_u[target_col], pred), m, len(trn_u), len(te_u)


def run():
    since = (pd.Timestamp.today() - pd.Timedelta(days=365)).strftime("%Y-%m-%d")
    print(f"Building leak-safe pace scores/settle lookup since {since} "
          f"(using the NOW-UPDATED settling_estimate model)...")
    race_id_to_score = wpr._build_pace_shape_race_scores(since)
    settle_lookup = wpr._build_pace_shape_settle_lookup(since)

    print("\nBuilding training frame...")
    D = wpr.build_training_frame("wpr_form_history.csv.gz", n_jobs=-1).dropna(
        subset=["target", "date"]).sort_values("date")
    print(f"  {len(D):,} rows")

    D["pace_score"] = D["race_id"].map(race_id_to_score)
    from wpr_projection import _load_trainer_jockey_by_horse_date
    name_map, _ = _load_trainer_jockey_by_horse_date("wpr_form_history.csv.gz")
    D["horse_lc"] = D["horse_id"].map(name_map).astype(str).str.lower()
    D["predicted_rel_settle"] = [settle_lookup.get((h, d)) for h, d in zip(D["horse_lc"], D["date"])]
    print(f"  pace_score coverage: {D['pace_score'].notna().mean()*100:.1f}%  "
          f"predicted_rel_settle coverage: {D['predicted_rel_settle'].notna().mean()*100:.1f}%")

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
    D = D.dropna(subset=["_base"]).copy()

    D["settle_signal"] = (D["predicted_rel_settle"] - 0.5) * 2
    D["pace_signal"] = (D["pace_score"] - 0.5) * 2
    D["interaction"] = D["settle_signal"] * D["pace_signal"]
    D["_resid"] = D["target"] - D["career_avg"]

    since_ts = pd.Timestamp(since)
    D = D[D["date"] >= since_ts].copy()
    print(f"  bounded to scored window: {len(D):,} rows")

    features = ["settle_signal", "pace_signal", "interaction", "field_size"]

    for direction, qlo, qhi, reverse in [
        ("A: forward (oldest 70% trn, newest 15% te)", 0.70, 0.85, False),
        ("B: reversed (newest 70% trn, oldest 15% te)", 0.30, 0.15, True),
    ]:
        print(f"\n--- direction {direction} ---")
        if not reverse:
            trn, te = D[D["date"] < D["date"].quantile(qlo)], D[D["date"] >= D["date"].quantile(qhi)]
        else:
            trn, te = D[D["date"] > D["date"].quantile(qlo)], D[D["date"] <= D["date"].quantile(qhi)]

        base_mae, _, n_trn, n_te = _fit_eval(trn, te, features, "_resid", {})
        print(f"  baseline (default L2, fits MEAN):     MAE={base_mae:.4f}  n_trn={n_trn:,} n_te={n_te:,}")

        med_mae, _, _, _ = _fit_eval(trn, te, features, "_resid", dict(objective="quantile", alpha=0.5))
        print(f"  quantile objective, alpha=0.5 (MEDIAN): MAE={med_mae:.4f} "
              f"({'better' if med_mae < base_mae else 'worse'}, {med_mae - base_mae:+.4f})")


if __name__ == "__main__":
    run()
