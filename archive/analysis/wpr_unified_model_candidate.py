"""wpr_unified_model_candidate.py - Phase 1 of the "restart WPR prediction
from scratch" plan (Sep 2026): a single LightGBM trained directly on every
raw ingredient the current 11 ADJ_TERMS are hand-built from, predicting
`target` directly - no base/adjustment decomposition at all.

WHY THIS IS WORTH RE-TESTING NOW
  This is the THIRD time this codebase would try a unified model. A
  HistGradientBoosting mean regressor, then a quantile-GBM (q10/q50/q90 on
  the full FEATURES list, q50 as the projection), and before either of
  those a Ridge model as the "adjustment" term were all tried and replaced
  by the current hand-crafted, per-horse-own-history ADJ_TERMS (see
  wpr_projection.py's module docstring and ADJ_TERMS's own comment for
  that history). Every one of those comparisons used `_base`/`wpr_nett`
  built through the run_id merge bug this session found and fixed (97% of
  joinable rows resolved to the wrong race, most leaking a LATER race's
  rating in) - so the verdict that decomposed features beat a unified
  model has never actually been tested honestly. This re-opens that
  question with the leak fixed, decided on the numbers (see
  wpr_model_eval_harness.py), not assumed either way.

FEATURES
  Every raw ingredient the current ADJ_TERMS/population-term models use,
  fed to ONE model instead of eleven separately-fit pieces: the full
  FEATURES list from wpr_models/config.json (now including a correctly-
  merged wpr_nett), the six own-history engineered features (own_distance
  etc - already columns from build_features, cheap to include alongside
  their own raw ingredients), trainer/jockey trailing win-rate, track/
  barrier/field_size, the pace_shape ingredients (pace_score,
  predicted_rel_settle, precomputed leak-safe on the full frame same as
  every other script this session), and the closing-sectional residual.

USAGE
  python wpr_unified_model_candidate.py
  (imports wpr_model_eval_harness and runs this scorer through it,
  printing the same MAE/AUC/Brier/strike-rate table as the baseline)

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np
import lightgbm as lgb

import wpr_projection as wpr
from wpr_adj_term_roi_ablation_test import build_frame
import wpr_model_eval_harness as harness

OWN_HISTORY_FEATURES = [
    "own_distance", "own_going", "own_first_up", "own_second_up",
    "own_trend", "own_long_spell",
]
EXTRA_FEATURES = OWN_HISTORY_FEATURES + [
    "trainer_win_pct_365d", "jockey_win_pct_90d",
    "barrier", "track_code",
    "pace_score", "predicted_rel_settle",
    "closing_raw_resid", "closing_n_pairs",
    "gear_code",
]

LGB_PARAMS = dict(objective="quantile", alpha=0.5, n_estimators=300,
                   max_depth=4, learning_rate=0.04, num_leaves=16,
                   random_state=42, verbosity=-1)


def _prep_inputs(D):
    D = D.copy()
    track_categories = sorted(D["track"].dropna().unique())
    track_code_map = {t: i for i, t in enumerate(track_categories)}
    D["track_code"] = D["track"].map(track_code_map).fillna(-1).astype(int)
    D["gear_code"] = D["gear_bucket"].map(wpr._GEAR_BUCKET_CODE).fillna(0).astype(int)
    return D


def _closing_resid(D, pace_baseline_lookup):
    def one(pairs):
        vals = []
        for sect, bucket in pairs:
            exp = pace_baseline_lookup.get(bucket)
            if exp is not None and sect is not None and sect == sect:
                vals.append(float(sect) - float(exp))
        return (float(np.mean(vals)), float(len(vals))) if vals else (np.nan, 0.0)
    computed = [one(p) for p in D["closing_pairs"]]
    D["closing_raw_resid"] = [c[0] for c in computed]
    D["closing_n_pairs"] = [c[1] for c in computed]
    return D


def unified_scorer(fit_data, held_out):
    """A single LightGBM (quantile alpha=0.5, matching the objective
    already validated for every other trained term in this codebase) on
    the union of FEATURES + every ADJ_TERM's own raw ingredients. Fit
    strictly on fit_data, applied to both (fit_data too, so the harness's
    Brier-beta search has an in-sample frame to calibrate against, same
    contract fit_fold_terms's baseline scorer follows)."""
    wpr._load_models()
    base_features = list(wpr._CFG.get("features", []))

    fit_data = _prep_inputs(fit_data)
    held_out = _prep_inputs(held_out)
    pace_baseline_lookup = wpr._fit_pace_baseline("wpr_form_history.csv.gz", fit_data["date"].max())
    fit_data = _closing_resid(fit_data, pace_baseline_lookup)
    held_out = _closing_resid(held_out, pace_baseline_lookup)

    feats = [f for f in base_features + EXTRA_FEATURES if f in fit_data.columns]
    fit_trn = fit_data.dropna(subset=["target"])
    medians = fit_trn[feats].median()
    fit_X = fit_trn[feats].fillna(medians)

    model = lgb.LGBMRegressor(**LGB_PARAMS)
    model.fit(fit_X, fit_trn["target"])

    for f in (fit_data, held_out):
        f["pred"] = model.predict(f[feats].fillna(medians))
    return fit_data, held_out


if __name__ == "__main__":
    full = build_frame()
    harness.run(full, unified_scorer, "CANDIDATE: single unified LightGBM (full feature set, no decomposition)")
