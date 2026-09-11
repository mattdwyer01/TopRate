"""
wpr_base_anchor_fullmodel_roi_backtest.py - a more decisive follow-up to
wpr_base_anchor_roi_backtest.py's inconclusive result (see chat, Sep
2026). That script scored the base anchor ALONE (ewm5 vs ewm7 vs
ewm10) and found small, direction-inconsistent ROI differences between
candidates - but two things make that result untrustworthy as a real
answer, not just inconclusive:

  1. The fitted price-softmax beta was pinned at the FLOOR of its grid
     (0.1, occasionally 0.15) in every single era-fold for all three
     candidates - meaning the Brier fit wanted an even flatter softmax
     than the grid allowed. That is the signature of a genuinely weak
     signal, and any 1-3 point ROI difference between candidates riding
     on top of that weak a signal is not something to trust either way.
  2. Base alone was never meant to stand as the shipped prediction - the
     live model always adds the ADJ_TERMS sum on top. Testing a cruder,
     never-shipped object is not a fair trial of "would swapping ewm5
     for ewm7/ewm10 change the ACTUAL model's market edge".

FIX: builds the FULL additive prediction (base + every ADJ_TERM that
does not depend on toprate_runners.csv's recency-limited columns) for
each anchor candidate, refits the trained-model terms (track_barrier,
closing_merit) per era-fold from race_results alone (same per-row
term functions the live model uses - _track_barrier_term, _closing_
merit_term), keeps the six own-history terms as-is (no fitting - pure
per-horse lookups, already correctly computed by build_training_frame),
and widens the beta grid down to 0.01 to see whether an even flatter
softmax is genuinely optimal or 0.1 was a real local answer.

EXCLUDED: trainer_merit, jockey_merit, pace_shape. The first two need
trainer_win_pct_365d/jockey_win_pct_90d, which only exist in the last
~4 months of toprate_runners.csv daily snapshots - including them would
collapse this back to a recency-limited test. pace_shape is excluded
for the same fold-aware-leak-safety reason scratch_joint_model_roi_
eval.py and scratch_joint_model_kfold_eval.py already exclude it.

DATA/METHOD: same as wpr_base_anchor_roi_backtest.py otherwise - reuses
the cached D (no rebuild), derives won/sp from race_results itself
(positionFinish==1, priceStarting), leave-one-era-out with a price-
softmax beta refit per candidate per fold, WPR-price edge method.

NO EM DASHES policy: hyphens only in this file.
"""
import pickle

import numpy as np
import pandas as pd

import wpr_projection as wp
from wpr_base_calc_10yr_retest import (
    load_combined, vectorized_ewm, compute_void_mask, assign_era,
    ERA_BOUNDS, D_CACHE,
)
from wpr_base_anchor_roi_backtest import base_with_anchor, report, report_edge

BETA_GRID = [0.01, 0.02, 0.03, 0.05, 0.08, 0.10, 0.15, 0.20, 0.25, 0.30, 0.40]
EDGE_THRESHOLDS = [0.0, 0.02, 0.04, 0.06, 0.08, 0.10, 0.13, 0.15, 0.20]
PRICE_CAPS = [15.0, 26.0]

CANDIDATES = {
    "full_ewm5_current": "ewm5",
    "full_ewm7": "ewm7",
    "full_ewm10": "ewm10",
}

OWN_HISTORY_TERMS = ["own_distance", "own_going", "own_first_up", "own_second_up",
                      "own_trend", "own_long_spell"]
FITTED_TERMS = ["track_barrier", "closing_merit"]
FULL_TERMS = FITTED_TERMS + OWN_HISTORY_TERMS


def _closing_raw_resid_one(pairs, pace_baseline_lookup):
    vals = []
    for sect, bucket in pairs:
        exp = pace_baseline_lookup.get(bucket)
        if exp is not None and sect is not None and sect == sect:
            vals.append(float(sect) - float(exp))
    return (float(np.mean(vals)), float(len(vals))) if vals else (np.nan, 0.0)


def fit_terms_on_fold(fit_half, apply_to, form_csv):
    """Fits track_barrier + closing_merit on fit_half ONLY, applies to
    every frame in apply_to (in place) via the SAME per-row term
    functions the live model uses."""
    track_categories = sorted(fit_half["track"].dropna().unique())
    track_code_map = {t: i for i, t in enumerate(track_categories)}
    for _f in apply_to:
        _f.loc[:, "track_code"] = _f["track"].map(track_code_map).fillna(-1).astype(int)
    track_barrier_model = wp._fit_simple_adj_model(fit_half, wp._TRACK_BARRIER_FEATURES, "track_barrier")

    pace_baseline_lookup = wp._fit_pace_baseline(form_csv, fit_half["date"].max())
    for _f in apply_to:
        _computed = [_closing_raw_resid_one(p, pace_baseline_lookup) for p in _f["closing_pairs"]]
        _f.loc[:, "closing_raw_resid"] = [c[0] for c in _computed]
        _f.loc[:, "closing_n_pairs"] = [c[1] for c in _computed]
    closing_merit_model = wp._fit_simple_adj_model(fit_half, wp._CLOSING_MERIT_FEATURES, "closing_merit")

    for _f in apply_to:
        _f.loc[:, "track_barrier"] = [
            wp._track_barrier_term(trk, dist, bar, fs, track_code_map, track_barrier_model)
            for trk, dist, bar, fs in zip(_f["track"], _f["cur_distance"], _f["barrier"], _f["field_size"])
        ]
        _f.loc[:, "closing_merit"] = [
            wp._closing_merit_term(pairs, pace_baseline_lookup, fs, closing_merit_model)
            for pairs, fs in zip(_f["closing_pairs"], _f["field_size"])
        ]
        for _term in FITTED_TERMS:
            _f[_term] = _f[_term] - _f.groupby("race_id")[_term].transform("mean")
        _f[FULL_TERMS] = _f[FULL_TERMS].fillna(0.0)


def _brier(data, beta, pred_col):
    rows = []
    for rid, g in data.groupby("race_id"):
        if len(g) < 4:
            continue
        pv = g[pred_col].to_numpy(dtype=float)
        e = np.exp(beta * (pv - pv.max()))
        p = e / e.sum()
        rows.extend(zip(p, g["won"]))
    arr = pd.DataFrame(rows, columns=["p", "won"])
    return float(((arr["p"] - arr["won"]) ** 2).mean()) if len(arr) else float("nan")


def _fit_beta(fit_half, pred_col):
    best_beta, best_brier = None, float("inf")
    for b in BETA_GRID:
        br = _brier(fit_half, b, pred_col)
        if br < best_brier:
            best_brier, best_beta = br, b
    return best_beta


def _edge_from_pred(frame, pred_col, beta):
    e = np.exp(beta * (frame[pred_col] - frame.groupby("race_id")[pred_col].transform("max")))
    denom = frame.groupby("race_id")[pred_col].transform(
        lambda s: np.exp(beta * (s - s.max())).sum())
    p_model = e / denom
    p_mkt = (1.0 / frame["sp"]) / frame.groupby("race_id")["sp"].transform(lambda s: (1.0 / s).sum())
    return p_model - p_mkt


def load_D():
    print(f"Loading cached D from {D_CACHE} ...")
    with open(D_CACHE, "rb") as f:
        D = pickle.load(f)
    print(f"  {len(D):,} rows")
    return D


def run():
    combined = load_combined()
    D = load_D()

    print("\nDeriving won/sp from race_results itself...")
    side = combined[["horse_id", "date", "race_id", "positionFinish", "priceStarting"]].copy()
    side["date"] = pd.to_datetime(side["date"], errors="coerce")
    side["race_id"] = side["race_id"].astype(str)
    side["won"] = (pd.to_numeric(side["positionFinish"], errors="coerce") == 1).astype(int)
    side["sp"] = pd.to_numeric(side["priceStarting"], errors="coerce")
    side = side.dropna(subset=["date", "sp"]).drop_duplicates(
        subset=["horse_id", "date", "race_id"], keep="first")
    side = side[side["sp"] > 1.0]

    D = D.copy()
    D["race_id"] = D["race_id"].astype(str)
    key_cols = ["horse_id", "date", "race_id"]
    before = len(D)
    D = D.merge(side[key_cols + ["won", "sp"]], on=key_cols, how="left")
    assert len(D) == before, "won/sp merge changed row count"
    D = D.dropna(subset=["won", "sp"]).copy()
    print(f"  {len(D):,} rows with a usable price and outcome")

    print("\nComputing extra-span candidates (ewm7/ewm10)...")
    void_mask = compute_void_mask(combined)
    for span in (7, 10):
        c = vectorized_ewm(combined, span, "wpr", void_mask_col=void_mask)
        c = c.rename(columns={f"ewm{span}_wpr": f"ewm{span}"})
        D = D.merge(c, on=key_cols, how="left")

    D["_era"] = assign_era(D["date"])
    era_names = [e[0] for e in ERA_BOUNDS]
    print(f"\nEra row counts:\n{D['_era'].value_counts().reindex(era_names)}")

    from wpr_base_calc_10yr_retest import COMBINED_CSV
    form_csv = str(COMBINED_CSV)

    for label, anchor_col in CANDIDATES.items():
        pooled_parts, betas = [], []
        for era in era_names:
            fit_half = D[D["_era"] != era].copy()
            held_out = D[D["_era"] == era].copy()
            if len(held_out) < 200:
                continue
            fit_terms_on_fold(fit_half, [fit_half, held_out], form_csv)
            fit_half["_base"] = base_with_anchor(fit_half, anchor_col)
            held_out["_base"] = base_with_anchor(held_out, anchor_col)
            for _f in (fit_half, held_out):
                _f["pred"] = _f["_base"].to_numpy() + wp._cap_adj_sum(
                    _f[FULL_TERMS].to_numpy()).sum(axis=1)
            beta = _fit_beta(fit_half, "pred")
            betas.append(beta)
            held_out["edge"] = _edge_from_pred(held_out, "pred", beta)
            pooled_parts.append(held_out)
        pooled = pd.concat(pooled_parts, ignore_index=True)
        print(f"\n{label}: per-era betas = {betas}")
        report_edge(pooled, "edge", f"{label} (full model, leave-one-era-out, pooled)")

    print("\nSame multiple-comparisons caveat as every backtest in this codebase:")
    print("treat this as a hypothesis, not a result to ship blind.")
    print("\nDone.")


if __name__ == "__main__":
    run()
