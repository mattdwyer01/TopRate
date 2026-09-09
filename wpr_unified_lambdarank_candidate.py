"""wpr_unified_lambdarank_candidate.py - Phase 1 follow-up: the same
unified feature set as wpr_unified_model_candidate.py, but trained with
LightGBM's lambdarank objective (LGBMRanker, race_id as the query group)
instead of quantile/point regression.

WHY
  wpr_unified_model_candidate.py's first attempt trained to predict the
  exact rating VALUE (quantile alpha=0.5), which optimises MAE - and it
  won clearly on MAE (6.26 vs baseline's 6.85) but lost narrowly on AUC
  (0.607 vs 0.618) and top-pick strike rate (25.9% vs 26.8%) against the
  current shipped architecture, on the SAME walk-forward folds via
  wpr_model_eval_harness.py. That's a mismatched-objective problem, not
  necessarily evidence a unified model can't rank well: predicting the
  right absolute number is a different task from ordering horses correctly
  WITHIN a race, which is what AUC/strike-rate actually measure and what
  the whole system is for. lambdarank directly optimises within-group
  ordering instead.

RELEVANCE LABEL
  NOT the raw `target` value - LightGBM's default lambdarank gain is
  2^label - 1, which would be nonsensical (and numerically enormous) fed a
  raw WPR-scale label (40-110+). Instead each row's relevance is its own
  PER-RACE ordinal rank of `target` (0 = worst finisher in that race by
  target, field_size-1 = best) - small non-negative integers, safe for the
  gain formula, and a more direct encoding of "did this horse do well
  RELATIVE TO THE OTHERS IN THIS RACE" than the raw value ever was for a
  ranking objective.

Same feature set, same walk-forward harness, same metrics as the point-
regression candidate - the only thing that changes is the objective, so
any difference in the result is attributable to that, not to some other
confound.

USAGE
  python wpr_unified_lambdarank_candidate.py

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np
import lightgbm as lgb

import wpr_projection as wpr
from wpr_adj_term_roi_ablation_test import build_frame
from wpr_unified_model_candidate import _prep_inputs, _closing_resid, EXTRA_FEATURES
import wpr_model_eval_harness as harness

LGB_RANKER_PARAMS = dict(objective="lambdarank", n_estimators=300, max_depth=4,
                          learning_rate=0.04, num_leaves=16, random_state=42, verbosity=-1)


def unified_lambdarank_scorer(fit_data, held_out):
    wpr._load_models()
    base_features = list(wpr._CFG.get("features", []))

    fit_data = _prep_inputs(fit_data)
    held_out = _prep_inputs(held_out)
    pace_baseline_lookup = wpr._fit_pace_baseline("wpr_form_history.csv.gz", fit_data["date"].max())
    fit_data = _closing_resid(fit_data, pace_baseline_lookup)
    held_out = _closing_resid(held_out, pace_baseline_lookup)

    feats = [f for f in base_features + EXTRA_FEATURES if f in fit_data.columns]
    fit_trn = fit_data.dropna(subset=["target"]).sort_values("race_id").copy()
    medians = fit_trn[feats].median()
    fit_X = fit_trn[feats].fillna(medians)

    # per-race ordinal rank of target as the relevance label (see docstring)
    relevance = fit_trn.groupby("race_id")["target"].rank(method="first", ascending=True).astype(int) - 1
    group_sizes = fit_trn.groupby("race_id", sort=False).size().to_numpy()

    model = lgb.LGBMRanker(**LGB_RANKER_PARAMS)
    model.fit(fit_X, relevance, group=group_sizes)

    for f in (fit_data, held_out):
        f["pred"] = model.predict(f[feats].fillna(medians))
    return fit_data, held_out


if __name__ == "__main__":
    full = build_frame()
    harness.run(full, unified_lambdarank_scorer,
                "CANDIDATE: unified LightGBM, lambdarank objective (per-race rank relevance)")
