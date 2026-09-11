"""
wpr_trainer_change_rebase_test.py - tests whether trainer_change's
population model should be fit against a RECENT-FORM baseline
(avg_last3 or ewm7, the just-shipped base anchor) instead of the
generic career_avg every other simple population term uses (see
_fit_simple_adj_model).

WHY: investigating a real screenshot (Flywheel, Sep 2026 - see chat)
found the raw (undemeaned) trainer_change model predicts +1.47 for
"no trainer change" and -1.05 for "changed" at field_size=7 - a
positive bonus just for keeping the same trainer, which doesn't sound
right on its face. Root cause hypothesis: trainer_change is fit as
(target - career_avg) ~ f(trainer_change, field_size); most rows have
trainer_change=0 (the default case), and horses racing again soon
under the same stable tend to be in decent CURRENT form, so target
naturally runs a bit above their FULL-CAREER average from recency
alone, unrelated to the trainer. The minority with trainer_change=1
skews toward stables that changed BECAUSE the horse wasn't going well.
So the "no change" arm may be absorbing a generic "current form beats
full-career baseline" bias that has nothing to do with trainer
identity, rather than a clean isolated trainer-change effect.

TEST: refit trainer_change against (target - avg_last3) and
(target - ewm7) instead of (target - career_avg), keeping the exact
same LightGBM hyperparams (_fit_simple_adj_model's own config) for a
fair comparison. Report (1) the raw model's own two predictions
(changed vs not, same representative field_size) for each variant -
does a recent-form baseline shrink the "no change" arm toward zero,
(2) held-out MAE for the full shipped model with each variant swapped
in, leave-one-era-out on the 10-year dataset, same methodology as
every other test this session. ROI stays deliberately deferred.

NO EM DASHES policy: hyphens only in this file.
"""
import pickle

import numpy as np
import pandas as pd
import lightgbm as lgb

import wpr_projection as wp
from wpr_base_calc_10yr_retest import (
    load_combined, vectorized_ewm, compute_void_mask, assign_era, ERA_BOUNDS, D_CACHE,
)
from wpr_base_anchor_roi_backtest import base_with_anchor
from wpr_base_anchor_fullmodel_roi_backtest import fit_terms_on_fold, FITTED_TERMS, _merit_batch

OWN_HISTORY_KEEP = ["own_first_up", "own_second_up", "own_long_spell"]
SHIPPED_NEW_TERMS = ["trainer_change", "pop_distance", "pop_going"]
CURRENT_TERMS = FITTED_TERMS + OWN_HISTORY_KEEP + SHIPPED_NEW_TERMS  # actual live composition (testable subset)

# pop_distance/pop_going still fit the standard career_avg way - only
# trainer_change is the subject of this test.
OTHER_NEW_TERM_FEATURES = {
    "pop_distance": ("dist_vs_last", wp._POP_DISTANCE_FEATURES),
    "pop_going": ("going_delta", wp._POP_GOING_FEATURES),
}
TC_FEATURES = wp._TRAINER_CHANGE_FEATURES  # ["trainer_change", "field_size"]

BASELINE_CANDIDATES = ["career_avg", "avg_last3", "ewm7"]


def load_D():
    print(f"Loading cached D from {D_CACHE} ...")
    with open(D_CACHE, "rb") as f:
        D = pickle.load(f)
    print(f"  {len(D):,} rows")
    return D


def fit_shipped_new_term(fit_half, apply_to, value_col, features, label):
    trn = fit_half.dropna(subset=[value_col, "target", "career_avg"])
    trn = trn.rename(columns={value_col: features[0]}) if value_col != features[0] else trn
    model = wp._fit_simple_adj_model(trn, features, label)
    for _f in apply_to:
        _f.loc[:, label] = _merit_batch(_f[value_col], _f["field_size"], model, features)
    return model


def fit_trainer_change_rebased(fit_half, apply_to, baseline_col, label):
    """Same LightGBM config as _fit_simple_adj_model, but regresses
    against (target - baseline_col) instead of the hardcoded
    (target - career_avg). fit_half's raw flag column is named
    trainer_change_raw (to avoid clashing with the ADJ_TERM output
    columns already being written) - renamed to match TC_FEATURES[0]
    ("trainer_change") before fitting, same pattern fit_shipped_new_term
    uses for its own value_col rename."""
    d = fit_half.dropna(subset=["trainer_change_raw", "field_size", "target", baseline_col])
    d = d.rename(columns={"trainer_change_raw": TC_FEATURES[0]})
    if len(d) < 200:
        print(f"    {label}: only {len(d):,} covered rows, skipping fit (need >=200)")
        model = None
    else:
        model = lgb.LGBMRegressor(n_estimators=150, max_depth=3, learning_rate=0.05,
                                  num_leaves=8, random_state=42, verbosity=-1,
                                  objective="quantile", alpha=0.5)
        model.fit(d[TC_FEATURES], d["target"] - d[baseline_col])
        print(f"    {label}: fitted on {len(d):,} rows (baseline={baseline_col})")
    for _f in apply_to:
        _f.loc[:, label] = _merit_batch(_f["trainer_change_raw"], _f["field_size"], model, TC_FEATURES)
    return model


def additive_predict(frame, terms):
    return frame["_base"].to_numpy() + wp._cap_adj_sum(frame[terms].to_numpy()).sum(axis=1)


def run():
    combined = load_combined()
    D = load_D()

    print("\nMerging jockey/trainer/track...")
    side_cols = ["horse_id", "date", "race_id", "trainer"]
    side = combined[side_cols].copy()
    side["date"] = pd.to_datetime(side["date"], errors="coerce")
    side["race_id"] = side["race_id"].astype(str)
    side = side.dropna(subset=["date"]).drop_duplicates(subset=["horse_id", "date", "race_id"], keep="first")
    D = D.copy()
    D["race_id"] = D["race_id"].astype(str)
    key_cols = ["horse_id", "date", "race_id"]
    before = len(D)
    D = D.merge(side, on=key_cols, how="left")
    assert len(D) == before, "trainer merge changed row count"
    D = D.sort_values(["horse_id", "date"])
    D["prior_trainer"] = D.groupby("horse_id")["trainer"].shift(1)
    D["trainer_change_raw"] = ((D["trainer"] != D["prior_trainer"]) & D["prior_trainer"].notna()).astype(float)

    print("\nComputing ewm7 (the shipped base anchor, not in the cached D)...")
    void_mask = compute_void_mask(combined)
    c = vectorized_ewm(combined, 7, "wpr", void_mask_col=void_mask)
    c = c.rename(columns={"ewm7_wpr": "ewm7"})
    D = D.merge(c, on=key_cols, how="left")

    D["_era"] = assign_era(D["date"])
    era_names = [e[0] for e in ERA_BOUNDS]
    print(f"\nEra row counts:\n{D['_era'].value_counts().reindex(era_names)}")

    per_era_mae = {}
    raw_predictions_by_era = {}

    for era in era_names:
        fit_half = D[D["_era"] != era].copy()
        held_out = D[D["_era"] == era].copy()
        if len(held_out) < 200:
            continue
        print(f"\nFitting on every era EXCEPT {era}, scoring held-out {era}...")
        fit_terms_on_fold(fit_half, [fit_half, held_out], "wpr_form_history.csv.gz")
        held_out["_base"] = base_with_anchor(held_out, "ewm7")
        fit_half["_base"] = base_with_anchor(fit_half, "ewm7")

        for new_term, (value_col, features) in OTHER_NEW_TERM_FEATURES.items():
            fit_shipped_new_term(fit_half, [fit_half, held_out], value_col, features, new_term)

        variant_models = {}
        for baseline_col in BASELINE_CANDIDATES:
            label = f"trainer_change_{baseline_col}"
            if baseline_col == "career_avg":
                # the CURRENT shipped behavior - via the real _fit_simple_adj_model,
                # not the rebase helper, so this arm is a genuine no-op control.
                model = fit_shipped_new_term(
                    fit_half, [fit_half, held_out], "trainer_change_raw", TC_FEATURES, label)
            else:
                model = fit_trainer_change_rebased(fit_half, [fit_half, held_out], baseline_col, label)
            variant_models[baseline_col] = model

        fillna_cols = ([t for t in CURRENT_TERMS if t != "trainer_change"]
                       + [f"trainer_change_{b}" for b in BASELINE_CANDIDATES])
        for _f in (fit_half, held_out):
            for term in SHIPPED_NEW_TERMS[1:] + [f"trainer_change_{b}" for b in BASELINE_CANDIDATES]:
                _f[term] = _f[term] - _f.groupby("race_id")[term].transform("mean")
            _f[fillna_cols] = _f[fillna_cols].fillna(0.0)

        maes = {}
        for baseline_col in BASELINE_CANDIDATES:
            terms = [t for t in CURRENT_TERMS if t != "trainer_change"] + [f"trainer_change_{baseline_col}"]
            pred = additive_predict(held_out, terms)
            mae = float(np.abs(held_out["target"].to_numpy() - pred).mean())
            maes[baseline_col] = (mae, len(held_out))
        per_era_mae[era] = maes
        print(f"  {era}: " + "  ".join(f"{k}={v[0]:.4f}" for k, v in maes.items()))

        # Raw (pre-demean), representative-field-size model outputs - the
        # actual diagnostic question: does "no change" shrink toward 0.
        raw_predictions_by_era[era] = {}
        for baseline_col, model in variant_models.items():
            if model is None:
                raw_predictions_by_era[era][baseline_col] = (None, None)
                continue
            X0 = pd.DataFrame([{TC_FEATURES[0]: 0.0, TC_FEATURES[1]: 8.0}])
            X1 = pd.DataFrame([{TC_FEATURES[0]: 1.0, TC_FEATURES[1]: 8.0}])
            raw_predictions_by_era[era][baseline_col] = (
                float(model.predict(X0)[0]), float(model.predict(X1)[0]))

    print(f"\n{'='*90}\nRAW MODEL OUTPUT (pre-demean, field_size=8): no-change vs changed, by era and baseline\n{'='*90}")
    print(f"{'era':<14}{'baseline':<14}{'no_change':>12}{'changed':>12}{'gap':>10}")
    for era in era_names:
        if era not in raw_predictions_by_era:
            continue
        for baseline_col in BASELINE_CANDIDATES:
            no_change, changed = raw_predictions_by_era[era][baseline_col]
            if no_change is None:
                continue
            print(f"{era:<14}{baseline_col:<14}{no_change:>12.3f}{changed:>12.3f}{changed-no_change:>10.3f}")

    print(f"\n{'='*90}\nMAE COMPARISON (leave-one-era-out, pooled across 5 real eras)\n{'='*90}")
    total_n = sum(per_era_mae[e]["career_avg"][1] for e in era_names if e in per_era_mae)
    base_pooled = sum(per_era_mae[e]["career_avg"][0] * per_era_mae[e]["career_avg"][1]
                       for e in era_names if e in per_era_mae) / total_n
    print(f"{'baseline':<16}{'pooled avg MAE':>18}{'delta vs career_avg':>22}")
    for baseline_col in BASELINE_CANDIDATES:
        pooled = sum(per_era_mae[e][baseline_col][0] * per_era_mae[e][baseline_col][1]
                     for e in era_names if e in per_era_mae) / total_n
        delta = pooled - base_pooled
        flag = ""
        if baseline_col != "career_avg":
            flag = "  <-- BETTER than shipped" if delta < -0.01 else (
                   "  <-- WORSE than shipped" if delta > 0.01 else "  <-- ~same")
        print(f"{baseline_col:<16}{pooled:>18.4f}{delta:>+22.4f}{flag}")

    print("\nReading this: 'career_avg' is the currently-shipped behavior (control arm, fit via")
    print("the real _fit_simple_adj_model, not a re-implementation). If avg_last3/ewm7 shrink the")
    print("no-change/changed gap toward a cleaner split (no-change nearer 0) AND don't hurt MAE,")
    print("that is a real improvement worth shipping. If MAE gets WORSE despite a 'cleaner' story,")
    print("the career_avg version was capturing real predictive signal, not just an artifact.")
    print("\nSame multiple-comparisons caveat as every backtest in this codebase:")
    print("treat this as a hypothesis, not a result to ship blind.")
    print("\nDone.")


if __name__ == "__main__":
    run()
