"""
wpr_tier2_adj_terms_candidate_test.py - builds proper leak-free
candidate ADJ_TERMS for the two Tier-2 signals that showed real,
era-stable residual bias in wpr_tier2_signals_audit.py: jockey-track
win rate (a clean monotonic gradient, ~1.0 WPR points spread from
worst to best band, t-stats -17 to -72 across every band) and trainer
stable-wide 30-day win rate (also monotonic, ~0.5 point spread,
t-stats -27 to -55).

Same pattern as wpr_new_adj_terms_candidate_test.py (the Tier-1
version that shipped trainer_change): each new term is fit as
wp._fit_simple_adj_model(trn, [value, field_size], label), applied via
the batch-vectorized _merit_batch helper, then per-race demeaned like
every other population-level term. Tested against the CURRENT shipped
baseline (FITTED_TERMS + own-history-keep + the already-shipped
trainer_change/pop_distance/pop_going), base anchor ewm7 (the just-
shipped swap from ewm5 - see wpr_base_anchor_vs_new_architecture_
test.py and the ewm7 retrain, Sep 2026).

METHOD: leave-one-era-out (5 real eras), MAE only. ROI stays
deliberately deferred per the user's own explicit direction until a
dedicated, trustworthy pricing methodology exists.

NO EM DASHES policy: hyphens only in this file.
"""
import itertools
import pickle

import numpy as np
import pandas as pd

import wpr_projection as wp
from wpr_base_calc_10yr_retest import (
    load_combined, vectorized_ewm, compute_void_mask, assign_era, ERA_BOUNDS, D_CACHE,
)
from wpr_base_anchor_roi_backtest import base_with_anchor
from wpr_base_anchor_fullmodel_roi_backtest import fit_terms_on_fold, FITTED_TERMS, _merit_batch

OWN_HISTORY_KEEP = ["own_first_up", "own_second_up", "own_long_spell"]
SHIPPED_NEW_TERMS = ["trainer_change", "pop_distance", "pop_going"]
CURRENT_TERMS = FITTED_TERMS + OWN_HISTORY_KEEP + SHIPPED_NEW_TERMS  # actual live composition (testable subset)

SHIPPED_NEW_TERM_FEATURES = {
    "trainer_change": ("trainer_change_raw", wp._TRAINER_CHANGE_FEATURES),
    "pop_distance": ("dist_vs_last", wp._POP_DISTANCE_FEATURES),
    "pop_going": ("going_delta", wp._POP_GOING_FEATURES),
}

NEW_CANDIDATES = ["jockey_track_term", "stable_form_term"]
NEW_FEATURES = {
    "jockey_track_term": "jockey_track_win_pct",
    "stable_form_term": "stable_form_30d",
}


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


def fit_candidate_term(fit_half, apply_to, value_col, label):
    trn = fit_half.dropna(subset=[value_col, "target", "career_avg"])
    model = wp._fit_simple_adj_model(trn, [value_col, "field_size"], label)
    for _f in apply_to:
        _f.loc[:, label] = _merit_batch(_f[value_col], _f["field_size"], model, [value_col, "field_size"])
    return model


def additive_predict(frame, terms):
    return frame["_base"].to_numpy() + wp._cap_adj_sum(frame[terms].to_numpy()).sum(axis=1)


def run():
    combined = load_combined()
    D = load_D()

    print("\nMerging jockey/trainer/track and computing won (positionFinish==1)...")
    side_cols = ["horse_id", "date", "race_id", "jockey", "trainer", "positionFinish"]
    side = combined[side_cols].copy()
    side["date"] = pd.to_datetime(side["date"], errors="coerce")
    side["race_id"] = side["race_id"].astype(str)
    side["won"] = (pd.to_numeric(side["positionFinish"], errors="coerce") == 1).astype(int)
    side = side.dropna(subset=["date"]).drop_duplicates(subset=["horse_id", "date", "race_id"], keep="first")

    D = D.copy()
    D["race_id"] = D["race_id"].astype(str)
    key_cols = ["horse_id", "date", "race_id"]
    before = len(D)
    D = D.merge(side[key_cols + ["jockey", "trainer", "won"]], on=key_cols, how="left")
    assert len(D) == before, "signal merge changed row count"
    D = D.sort_values(["horse_id", "date"])
    D["prior_trainer"] = D.groupby("horse_id")["trainer"].shift(1)
    D["trainer_change_raw"] = ((D["trainer"] != D["prior_trainer"]) & D["prior_trainer"].notna()).astype(float)

    print("\nBuilding leak-free jockey-track win rate (expanding, shift(1))...")
    # See wpr_tier2_signals_audit.py's comment for why .to_numpy() is
    # deliberately NOT used here: jt is sorted into a different row
    # order than D, and a plain (index-aligned) Series assignment is
    # what keeps every row matched to its own horse/race.
    jt = D[["jockey", "track", "date", "won"]].copy().sort_values(["jockey", "track", "date"])
    jt["jt_wins"] = jt.groupby(["jockey", "track"])["won"].transform(lambda s: s.shift(1).expanding().sum())
    jt["jt_starts"] = jt.groupby(["jockey", "track"])["won"].transform(lambda s: s.shift(1).expanding().count())
    jt["jockey_track_win_pct"] = jt["jt_wins"] / jt["jt_starts"].replace(0, np.nan)
    D["jockey_track_win_pct"] = jt["jockey_track_win_pct"]
    D.loc[jt["jt_starts"] < 5, "jockey_track_win_pct"] = np.nan  # match the audit's >=5-starts coverage gate

    print("\nBuilding leak-free trainer stable-wide 30-day rolling win rate...")
    tr = D[["trainer", "date", "won"]].copy()
    tr["_orig_idx"] = tr.index
    tr = tr.sort_values(["trainer", "date"]).set_index("date")

    def _rolling_30d(g):
        g = g.sort_index()
        shifted = g["won"].shift(1)
        shifted.index = g.index
        return shifted.rolling("30D").mean()

    tr["stable_form_30d"] = tr.groupby("trainer", group_keys=False).apply(_rolling_30d)
    tr = tr.reset_index(drop=True).set_index("_orig_idx")
    D["stable_form_30d"] = tr["stable_form_30d"]

    print("\nComputing ewm7 (the shipped base anchor, not in the cached D)...")
    void_mask = compute_void_mask(combined)
    c = vectorized_ewm(combined, 7, "wpr", void_mask_col=void_mask)
    c = c.rename(columns={"ewm7_wpr": "ewm7"})
    D = D.merge(c, on=key_cols, how="left")

    D["_era"] = assign_era(D["date"])
    era_names = [e[0] for e in ERA_BOUNDS]
    print(f"\nEra row counts:\n{D['_era'].value_counts().reindex(era_names)}")

    per_era_results = {}
    new_term_fits_by_era = {}

    for era in era_names:
        fit_half = D[D["_era"] != era].copy()
        held_out = D[D["_era"] == era].copy()
        if len(held_out) < 200:
            continue
        print(f"\nFitting on every era EXCEPT {era}, scoring held-out {era}...")
        fit_terms_on_fold(fit_half, [fit_half, held_out], "wpr_form_history.csv.gz")
        held_out["_base"] = base_with_anchor(held_out, "ewm7")
        fit_half["_base"] = base_with_anchor(fit_half, "ewm7")

        for new_term, (value_col, features) in SHIPPED_NEW_TERM_FEATURES.items():
            fit_shipped_new_term(fit_half, [fit_half, held_out], value_col, features, new_term)

        term_models = {}
        for cand in NEW_CANDIDATES:
            value_col = NEW_FEATURES[cand]
            model = fit_candidate_term(fit_half, [fit_half, held_out], value_col, cand)
            term_models[cand] = model
        new_term_fits_by_era[era] = term_models

        for _f in (fit_half, held_out):
            for term in SHIPPED_NEW_TERMS + NEW_CANDIDATES:
                _f[term] = _f[term] - _f.groupby("race_id")[term].transform("mean")
            _f[NEW_CANDIDATES] = _f[NEW_CANDIDATES].fillna(0.0)
            _f[CURRENT_TERMS] = _f[CURRENT_TERMS].fillna(0.0)

        variants = {
            "current": CURRENT_TERMS,
            "current_plus_both_new": CURRENT_TERMS + NEW_CANDIDATES,
        }
        for cand in NEW_CANDIDATES:
            variants[f"current_plus_{cand}"] = CURRENT_TERMS + [cand]
        for pair in itertools.combinations(NEW_CANDIDATES, 2):
            variants[f"current_plus_{'_and_'.join(pair)}"] = CURRENT_TERMS + list(pair)

        maes = {}
        for name, terms in variants.items():
            pred = additive_predict(held_out, terms)
            mae = float(np.abs(held_out["target"].to_numpy() - pred).mean())
            maes[name] = (mae, len(held_out))
        per_era_results[era] = maes
        print(f"  {era}: current={maes['current'][0]:.4f}  "
              f"current_plus_both_new={maes['current_plus_both_new'][0]:.4f}")

    print(f"\n{'='*90}\nMAE COMPARISON (leave-one-era-out, pooled across 5 real eras)\n{'='*90}")
    all_variant_names = list(per_era_results[era_names[0]].keys())
    total_n = sum(per_era_results[e]["current"][1] for e in era_names if e in per_era_results)
    current_pooled = sum(per_era_results[e]["current"][0] * per_era_results[e]["current"][1]
                          for e in era_names if e in per_era_results) / total_n

    print(f"{'variant':<28}{'pooled avg MAE':>18}{'delta vs current':>18}")
    for name in all_variant_names:
        pooled = sum(per_era_results[e][name][0] * per_era_results[e][name][1]
                     for e in era_names if e in per_era_results) / total_n
        delta = pooled - current_pooled
        flag = ""
        if name != "current":
            flag = "  <-- BETTER than current" if delta < -0.01 else (
                   "  <-- WORSE than current" if delta > 0.01 else "  <-- ~same")
        print(f"{name:<28}{pooled:>18.4f}{delta:>+18.4f}{flag}")

    print("\nReading this: 'current' is the live-equivalent MAE (scoped to what's testable")
    print("this deep, base anchor ewm7). 'current_plus_X' isolates each new term's OWN")
    print("marginal contribution on top of the shipped baseline.")

    print(f"\n{'='*90}\nNEW-TERM STABILITY CHECK (5 independent era-fits, same as track_barrier's)\n{'='*90}")
    print(f"{'term':<20}{'mean pairwise corr':>20}{'mean |diff|':>14}{'std across fits (avg)':>24}")
    for cand in NEW_CANDIDATES:
        value_col = NEW_FEATURES[cand]
        scored = {}
        for era, term_models in new_term_fits_by_era.items():
            frame = D.copy()
            scored[era] = _merit_batch(frame[value_col], frame["field_size"],
                                        term_models[cand], [value_col, "field_size"])
        vals = np.stack(list(scored.values()), axis=1)
        mask = ~np.isnan(vals).any(axis=1)
        vals = vals[mask]
        corrs, diffs = [], []
        for i in range(vals.shape[1]):
            for j in range(i + 1, vals.shape[1]):
                corrs.append(np.corrcoef(vals[:, i], vals[:, j])[0, 1])
                diffs.append(np.mean(np.abs(vals[:, i] - vals[:, j])))
        std_across = np.std(vals, axis=1).mean()
        print(f"{cand:<20}{np.mean(corrs):>20.3f}{np.mean(diffs):>14.3f}{std_across:>24.3f}")

    print("\nSame multiple-comparisons caveat as every backtest in this codebase:")
    print("treat this as a hypothesis, not a result to ship blind.")
    print("\nDone.")


if __name__ == "__main__":
    run()
