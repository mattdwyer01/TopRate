"""wpr_slope_and_hyperparam_recheck.py - items 2 and 4 of the "how do we
improve strike rate/AUC/Brier further" follow-up (Sep 2026), re-checked
against the NOW-FIXED _base (see wpr_projection.py's build_training_frame
docstring for the wpr_nett future-leak bug this session found and fixed -
every prior calibration-slope/hyperparameter decision was made against
the corrupted version).

ITEM 2: calibration slope. The original _CALIB_ADJ_SLOPE (0.1791, removed
this session) was fit as actual = a + b_base*base + b_adj*adjustment,
first half of data, evaluated purely out-of-sample on the second half
(see git history commit 87d801f / b98888d). It was removed specifically
because ROI evidence favoured no-slope even though MAE alone favoured
keeping it - but that MAE comparison used the LEAK-CORRUPTED base. This
refits the same decomposed slope structure (b_base, b_adj via OLS) on the
FIXED base, bidirectionally (H1 fit / H2 eval and vice versa, matching
wpr_adj_term_ablation_test.py's own convention), and reports whether a
slope now measurably helps or hurts held-out MAE.

ITEM 4: population-term hyperparameters. track_barrier/trainer_merit/
jockey_merit/gear_change/closing_merit are all fit via _fit_simple_adj_
model with a fixed LightGBM config (n_estimators=150, max_depth=3,
learning_rate=0.05, num_leaves=8 - see wpr_projection.py). That config
was never swept once fitting against real (uncorrupted) targets became
possible today. Sweeps a small grid per term, bidirectionally, evaluating
held-out MAE of each term's own residual prediction (target - career_avg,
matching _fit_simple_adj_model's actual training objective).

USAGE
  python wpr_slope_and_hyperparam_recheck.py

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np
import pandas as pd
import lightgbm as lgb
from sklearn.metrics import mean_absolute_error

import wpr_projection as wpr
from wpr_adj_term_ablation_test import build_frame, ALL_CANDIDATES, fit_and_apply_all_terms

HP_GRID = [
    {"n_estimators": 150, "max_depth": 3, "learning_rate": 0.05, "num_leaves": 8},   # current shipped
    {"n_estimators": 150, "max_depth": 4, "learning_rate": 0.05, "num_leaves": 16},
    {"n_estimators": 150, "max_depth": 5, "learning_rate": 0.05, "num_leaves": 31},
    {"n_estimators": 300, "max_depth": 3, "learning_rate": 0.03, "num_leaves": 8},
    {"n_estimators": 300, "max_depth": 4, "learning_rate": 0.03, "num_leaves": 16},
    {"n_estimators": 80,  "max_depth": 2, "learning_rate": 0.08, "num_leaves": 4},
]

POP_TERMS = {
    "track_barrier": wpr._TRACK_BARRIER_FEATURES,
    "trainer_merit": wpr._TRAINER_MERIT_FEATURES,
    "jockey_merit": wpr._JOCKEY_MERIT_FEATURES,
    "gear_change": wpr._GEAR_CHANGE_FEATURES,
    "closing_merit": wpr._CLOSING_MERIT_FEATURES,
}


def fit_lgb(trn, feats, label, hp):
    d = trn.dropna(subset=feats + ["target", "career_avg"])
    if len(d) < 200:
        return None
    resid = d["target"] - d["career_avg"]
    model = lgb.LGBMRegressor(objective="quantile", alpha=0.5, random_state=42, verbosity=-1, **hp)
    model.fit(d[feats], resid)
    return model


def eval_lgb(model, held, feats):
    d = held.dropna(subset=feats + ["target", "career_avg"])
    if model is None or len(d) < 20:
        return None, 0
    pred = d["career_avg"].to_numpy() + model.predict(d[feats])
    return mean_absolute_error(d["target"], pred), len(d)


def prep_term_inputs(D):
    """Ingredients each population term's fit needs, mirroring
    wpr_adj_term_ablation_test.fit_and_apply_all_terms's own prep steps,
    minus the trained-model application (this script fits/evaluates each
    term's OWN residual prediction directly, not the full wprp_proj)."""
    D = D.copy()
    track_categories = sorted(D["track"].dropna().unique())
    track_code_map = {t: i for i, t in enumerate(track_categories)}
    D["track_code"] = D["track"].map(track_code_map).fillna(-1).astype(int)
    D["gear_code"] = D["gear_bucket"].map(wpr._GEAR_BUCKET_CODE).fillna(0).astype(int)

    pace_baseline_lookup = wpr._fit_pace_baseline("wpr_form_history.csv.gz", D["date"].max())

    def _closing_raw_resid_one(pairs):
        vals = []
        for sect, bucket in pairs:
            exp = pace_baseline_lookup.get(bucket)
            if exp is not None and sect is not None and sect == sect:
                vals.append(float(sect) - float(exp))
        return (float(np.mean(vals)), float(len(vals))) if vals else (np.nan, 0.0)

    _computed = [_closing_raw_resid_one(p) for p in D["closing_pairs"]]
    D["closing_raw_resid"] = [c[0] for c in _computed]
    D["closing_n_pairs"] = [c[1] for c in _computed]
    return D


def hyperparam_sweep(h1, h2):
    print(f"\n{'='*90}\nITEM 4: population-term hyperparameter sweep\n{'='*90}")
    h1p, h2p = prep_term_inputs(h1), prep_term_inputs(h2)
    for term, feats in POP_TERMS.items():
        print(f"\n--- {term} ---")
        print(f"{'config':<55} {'A: H1->H2 MAE':>14} {'B: H2->H1 MAE':>14}")
        for hp in HP_GRID:
            m_a = fit_lgb(h1p, feats, term, hp)
            mae_a, n_a = eval_lgb(m_a, h2p, feats)
            m_b = fit_lgb(h2p, feats, term, hp)
            mae_b, n_b = eval_lgb(m_b, h1p, feats)
            tag = " <- current shipped" if hp == HP_GRID[0] else ""
            mae_a_s = f"{mae_a:.4f}" if mae_a is not None else "n/a"
            mae_b_s = f"{mae_b:.4f}" if mae_b is not None else "n/a"
            print(f"{str(hp):<55} {mae_a_s:>14} {mae_b_s:>14}{tag}")


def fit_decomposed_slope(D):
    """actual = a + b_base*_base + b_adj*adj_sum, via OLS (matching the
    original _CALIB_ADJ_SLOPE derivation - see this file's docstring)."""
    d = D.dropna(subset=["target", "_base"] + list(wpr.ADJ_TERMS))
    adj_sum = wpr._cap_adj_sum(d[wpr.ADJ_TERMS].to_numpy()).sum(axis=1)
    X = np.column_stack([np.ones(len(d)), d["_base"].to_numpy(), adj_sum])
    y = d["target"].to_numpy()
    coef, *_ = np.linalg.lstsq(X, y, rcond=None)
    a, b_base, b_adj = coef
    return a, b_base, b_adj


def eval_slope_mae(D, a, b_base, b_adj, use_slope):
    d = D.dropna(subset=["target", "_base"] + list(wpr.ADJ_TERMS))
    adj_sum = wpr._cap_adj_sum(d[wpr.ADJ_TERMS].to_numpy()).sum(axis=1)
    if use_slope:
        pred = a + b_base * d["_base"].to_numpy() + b_adj * adj_sum
    else:
        pred = d["_base"].to_numpy() + adj_sum
    return mean_absolute_error(d["target"], pred), len(d)


def slope_recheck(h1_scored, h2_scored):
    """h1_scored/h2_scored: ADJ_TERMS already computed OUT-OF-SAMPLE (terms
    fit on the OPPOSITE half, matching fit_and_apply_all_terms's own
    convention) - fitting the slope on one and evaluating on the other
    keeps both the term-fitting AND the slope-fitting leak-free."""
    print(f"\n{'='*90}\nITEM 2: calibration slope re-check (fixed _base)\n{'='*90}")
    a_a, bb_a, ba_a = fit_decomposed_slope(h1_scored)
    print(f"Direction A (fit slope on H1, terms out-of-sample from H2): "
          f"a={a_a:.4f}  b_base={bb_a:.4f}  b_adj={ba_a:.4f}")
    mae_noslope_a, n_a = eval_slope_mae(h2_scored, a_a, bb_a, ba_a, use_slope=False)
    mae_slope_a, _ = eval_slope_mae(h2_scored, a_a, bb_a, ba_a, use_slope=True)
    print(f"  H2 held-out MAE: no-slope(current shipped)={mae_noslope_a:.4f}  "
          f"with-fitted-slope={mae_slope_a:.4f}  (n={n_a})")

    a_b, bb_b, ba_b = fit_decomposed_slope(h2_scored)
    print(f"Direction B (fit slope on H2, terms out-of-sample from H1): "
          f"a={a_b:.4f}  b_base={bb_b:.4f}  b_adj={ba_b:.4f}")
    mae_noslope_b, n_b = eval_slope_mae(h1_scored, a_b, bb_b, ba_b, use_slope=False)
    mae_slope_b, _ = eval_slope_mae(h1_scored, a_b, bb_b, ba_b, use_slope=True)
    print(f"  H1 held-out MAE: no-slope(current shipped)={mae_noslope_b:.4f}  "
          f"with-fitted-slope={mae_slope_b:.4f}  (n={n_b})")

    both_slope_better = mae_slope_a < mae_noslope_a and mae_slope_b < mae_noslope_b
    print(f"\nVerdict: slope helps MAE in both directions: {both_slope_better}")
    print(f"  (b_adj fitted at {ba_a:.4f} / {ba_b:.4f} - compare to the old removed "
          f"_CALIB_ADJ_SLOPE=0.1791)")


def run():
    D = build_frame()
    mid = D["date"].quantile(0.5)
    h1, h2 = D[D["date"] < mid].copy(), D[D["date"] >= mid].copy()
    print(f"H1: {len(h1):,} rows, H2: {len(h2):,} rows")

    print("Scoring ADJ_TERMS out-of-sample for the slope re-check "
          "(terms fit on one half, applied to the other)...")
    h2_scored = fit_and_apply_all_terms(h1, h2, h1["date"].max())
    h1_scored = fit_and_apply_all_terms(h2, h1, h2["date"].max())
    slope_recheck(h1_scored, h2_scored)

    hyperparam_sweep(h1, h2)


if __name__ == "__main__":
    run()
