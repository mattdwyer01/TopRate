"""
wpr_adj_term_ablation_and_stability.py - answers the user's "I don't
trust the current additive model with adjustments (they're too many
and too volatile)" concern (see chat, Sep 2026) with data, in two parts:

1. LEAVE-ONE-TERM-OUT ROI ABLATION: for each ADJ_TERM, scores the full
   additive model and a variant with that ONE term zeroed out (every
   other term unchanged), both leak-free (bidirectional H1/H2 split,
   population terms refit on the fit-half only, scored on the held-out
   half - same discipline as scratch_joint_model_roi_eval.py, which
   this script's fit_and_score() closely follows). Edge is the WPR-PRICE
   method (softmax of the raw WPR-scale prediction, beta re-fit per
   variant by Brier minimization, same convention calibrate_price_beta.py
   uses) - NOT the z-score feature-blend edge from wpr_bet_selection_
   leakfree_eval.py, which the user has separately said to ignore (see
   chat). A term whose removal does not hurt ROI (or improves it) is a
   candidate for cutting; a term whose removal clearly hurts is earning
   its keep.

2. RETRAIN-STABILITY CHECK: for each of the four TRAINED-MODEL terms
   (track_barrier, closing_merit, trainer_merit, jockey_merit), fits
   the term twice, independently, on H1 and on H2, then scores the SAME
   full population with BOTH fits and compares the two outputs directly
   (correlation, mean absolute difference, and the spread of the
   difference) - this is not an accuracy check (no target involved), it
   is a direct measure of how much a term's value for the identical
   horse/race would have come out differently if it happened to be fit
   on a different slice of history. High divergence here IS the
   "volatile" the user is worried about, made concrete instead of
   assumed.

SCOPE: pace_shape is excluded from both parts (fixed at 0.0 everywhere,
consistently across every variant so it does not distort the
comparison) - same reason scratch_joint_model_kfold_eval.py and
scratch_joint_model_roi_eval.py both exclude it: _fit_pace_shape_model's
leak-safe window is hardcoded to the global max date, not fold-aware,
so a fold-based refit of it would not be genuinely leak-free. The six
own-history terms (own_distance, own_going, own_first_up, own_second_up,
own_trend, own_long_spell) need no refitting (they are pure per-horse
lookups, already correctly computed by build_training_frame) and so are
not part of the stability check (nothing to refit) - they ARE part of
the ablation (each can still be zeroed out and ROI compared).

Does NOT modify wpr_projection.py, does NOT touch wpr_models/*.joblib
or config.json. Read-only, safe to run repeatedly.

NO EM DASHES policy: hyphens only in this file.
"""
import pickle
from pathlib import Path

import numpy as np
import pandas as pd

import wpr_projection as wp
from wpr_own_pace_backtest import merge_won_by_horse_date
from wpr_bet_selection_post_retrain import merge_price_pfm, report

FORM_CSV = "wpr_form_history.csv.gz"
BETA_GRID = [0.05, 0.10, 0.15, 0.20, 0.25, 0.30, 0.40]
EDGE_THRESHOLDS = [0.0, 0.02, 0.04, 0.06, 0.08, 0.10, 0.13, 0.15, 0.20]
PRICE_CAPS = [15.0, 26.0]

TRAINED_TERMS = ["track_barrier", "closing_merit", "trainer_merit", "jockey_merit"]
OWN_HISTORY_TERMS = ["own_distance", "own_going", "own_first_up", "own_second_up",
                      "own_trend", "own_long_spell"]
ABLATION_TERMS = TRAINED_TERMS + OWN_HISTORY_TERMS  # pace_shape excluded, see docstring

_CACHE = Path("/tmp/claude-0/-home-user-TopRate/95a262de-71bd-5daf-b05e-b7e3031f09dd/scratchpad/adj_term_ablation_D_cache.pkl")


def _load_D():
    if _CACHE.exists():
        print(f"Loading cached prepped D from {_CACHE} (skipping rebuild)...")
        with open(_CACHE, "rb") as f:
            return pickle.load(f)

    print("Building training frame (n_jobs=-1, parallel) ...")
    D = wp.build_training_frame(FORM_CSV, n_jobs=-1).dropna(
        subset=["target", "date"]).sort_values("date")
    print(f"{len(D):,} training rows")

    print("Merging won/race_id from toprate_runners.csv (leak-safe horse+date join)...")
    D = merge_won_by_horse_date(D, form_csv=FORM_CSV)
    print(f"  {len(D):,} rows after won/race_id merge")

    print("Merging price/pfm_score from toprate_runners.csv...")
    D = merge_price_pfm(D)
    sp = pd.to_numeric(D["fixed_win_price"], errors="coerce")
    sp_fallback = pd.to_numeric(D["starting_price_sp"], errors="coerce")
    D["used_sp_fallback"] = sp.isna() & sp_fallback.notna()
    D["sp"] = sp.fillna(sp_fallback)
    D = D.dropna(subset=["sp"])
    D = D[D["sp"] > 1.0]
    print(f"  {len(D):,} rows with a usable price")

    if "going" in D.columns:
        g = D["going"].astype(str).str.strip().str.lower()
        blank_going = D["going"].isna() | g.isin(["", "nan", "none", "<na>"])
        n_blank = int(blank_going.sum())
        if n_blank:
            D = D[~blank_going].copy()
            print(f"  surface filter: excluded {n_blank:,} rows, {len(D):,} remain")

    D["_base"] = wp._BASE_BLEND_ALPHA * D["wpr_nett"] + (1 - wp._BASE_BLEND_ALPHA) * D["ewm5"]
    D["_base"] = D["_base"].fillna(D["wpr_nett"]).fillna(D["ewm5"]) \
        .fillna(D["avg_last3"]).fillna(D["career_avg"])
    D = D.dropna(subset=["_base"]).copy()

    med = D[wp.FEATURES].median()
    D[wp.FEATURES] = D[wp.FEATURES].fillna(med)

    # pace_shape excluded (see module docstring) - fixed at 0.0 everywhere,
    # consistently, so it cancels out of every comparison below.
    D["pace_shape"] = 0.0

    print(f"Caching prepped D to {_CACHE} ...")
    with open(_CACHE, "wb") as f:
        pickle.dump(D, f)
    return D


def _closing_raw_resid_one(pairs, pace_baseline_lookup):
    vals = []
    for sect, bucket in pairs:
        exp = pace_baseline_lookup.get(bucket)
        if exp is not None and sect is not None and sect == sect:
            vals.append(float(sect) - float(exp))
    return (float(np.mean(vals)), float(len(vals))) if vals else (np.nan, 0.0)


def fit_trained_terms(fit_half, apply_to):
    """Fits the four trained-model population terms on fit_half ONLY,
    applies to every frame in apply_to (in place). Returns the four
    fitted models/lookups so the stability check can re-apply them to a
    DIFFERENT population later."""
    fit_half = fit_half.copy()
    track_categories = sorted(fit_half["track"].dropna().unique())
    track_code_map = {t: i for i, t in enumerate(track_categories)}
    trainer_merit_trn = wp._fit_coverage_aware_trn(fit_half, ["trainer_win_pct_365d"])
    trainer_merit_model = wp._fit_simple_adj_model(trainer_merit_trn, wp._TRAINER_MERIT_FEATURES, "trainer_merit")
    jockey_merit_trn = wp._fit_coverage_aware_trn(fit_half, ["jockey_win_pct_90d"])
    jockey_merit_model = wp._fit_simple_adj_model(jockey_merit_trn, wp._JOCKEY_MERIT_FEATURES, "jockey_merit")
    for _f in apply_to:
        _f.loc[:, "track_code"] = _f["track"].map(track_code_map).fillna(-1).astype(int)
    track_barrier_model = wp._fit_simple_adj_model(fit_half, wp._TRACK_BARRIER_FEATURES, "track_barrier")
    pace_baseline_lookup = wp._fit_pace_baseline(FORM_CSV, fit_half["date"].max())
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
        _f.loc[:, "trainer_merit"] = [
            wp._merit_term(v, fs, trainer_merit_model, wp._TRAINER_MERIT_FEATURES)
            for v, fs in zip(_f["trainer_win_pct_365d"], _f["field_size"])
        ]
        _f.loc[:, "jockey_merit"] = [
            wp._merit_term(v, fs, jockey_merit_model, wp._JOCKEY_MERIT_FEATURES)
            for v, fs in zip(_f["jockey_win_pct_90d"], _f["field_size"])
        ]
        _f.loc[:, "closing_merit"] = [
            wp._closing_merit_term(pairs, pace_baseline_lookup, fs, closing_merit_model)
            for pairs, fs in zip(_f["closing_pairs"], _f["field_size"])
        ]
        for _term in TRAINED_TERMS:
            _f[_term] = _f[_term] - _f.groupby("race_id")[_term].transform("mean")
        _f[wp.ADJ_TERMS] = _f[wp.ADJ_TERMS].fillna(0.0)

    return {
        "track_code_map": track_code_map,
        "track_barrier_model": track_barrier_model,
        "trainer_merit_model": trainer_merit_model,
        "jockey_merit_model": jockey_merit_model,
        "closing_merit_model": closing_merit_model,
        "pace_baseline_lookup": pace_baseline_lookup,
    }


def _additive_predict(frame, drop_term=None):
    terms = [t for t in wp.ADJ_TERMS if t != drop_term] if drop_term else list(wp.ADJ_TERMS)
    return frame["_base"].to_numpy() + wp._cap_adj_sum(frame[terms].to_numpy()).sum(axis=1)


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


def fit_and_score(fit_half, held_out):
    """Fits the trained terms on fit_half, applies to both frames, then
    computes a FULL prediction and one LEAVE-ONE-TERM-OUT prediction per
    ADJ_TERM in ABLATION_TERMS - all on held_out, all using ONLY
    fit_half's fits. Returns held_out with one edge_<variant> column per
    variant plus the fitted models (for the stability check)."""
    fit_half = fit_half.copy()
    held_out = held_out.copy()
    models = fit_trained_terms(fit_half, [fit_half, held_out])

    variants = ["full"] + [f"minus_{t}" for t in ABLATION_TERMS]
    for f in (fit_half, held_out):
        for v in variants:
            drop = None if v == "full" else v[len("minus_"):]
            f[f"pred_{v}"] = _additive_predict(f, drop_term=drop)

    held_out = held_out.copy()
    for v in variants:
        pred_col = f"pred_{v}"
        beta = _fit_beta(fit_half, pred_col)
        held_out[f"edge_{v}"] = _edge_from_pred(held_out, pred_col, beta)
        held_out[f"beta_{v}"] = beta
    return held_out, models


def report_edge(bets, edge_col, label):
    print(f"\n{'='*70}\n{label}\n{'='*70}")
    print(f"total held-out bets: {len(bets):,}  [population avg price ${bets['sp'].mean():.2f}]\n")
    for thr in EDGE_THRESHOLDS:
        base = bets[bets[edge_col] >= thr]
        for cap in PRICE_CAPS:
            report(base[base["sp"] <= cap], f"edge>={thr:.2f}, price<={cap:.0f}")


def run_ablation(D):
    mid = D["date"].quantile(0.5)
    h1, h2 = D[D["date"] < mid].copy(), D[D["date"] >= mid].copy()
    print(f"\nH1: {len(h1):,} rows (< {mid.date()}), H2: {len(h2):,} rows (>= {mid.date()})")

    print("\nFitting on H1, scoring held-out H2...")
    h2_scored, models_h1 = fit_and_score(h1, h2)
    print("\nFitting on H2, scoring held-out H1...")
    h1_scored, models_h2 = fit_and_score(h2, h1)

    pooled = pd.concat([h1_scored, h2_scored], ignore_index=True)
    print(f"\nPooled leak-free held-out set: {len(pooled):,} rows")

    report_edge(pooled, "edge_full", "FULL additive model (every ADJ_TERM, pace_shape fixed 0.0)")
    for t in ABLATION_TERMS:
        report_edge(pooled, f"edge_minus_{t}", f"WITHOUT {t} (every other term unchanged)")

    return h1, h2, models_h1, models_h2


def run_stability(h1, h2, models_h1, models_h2):
    """Applies the H1-fit and H2-fit trained-term models to the SAME
    fixed population (the pooled full dataset) and compares the two
    independently-fit outputs directly - no target/accuracy involved,
    purely "how much does this term's value for the same row shift
    depending on which half of history it was fit on"."""
    print(f"\n{'='*70}\nRETRAIN-STABILITY CHECK (same rows, scored by two independent fits)\n{'='*70}")
    pooled = pd.concat([h1, h2], ignore_index=True).copy()

    def _apply(models, frame):
        frame = frame.copy()
        tcm = models["track_code_map"]
        frame.loc[:, "track_code"] = frame["track"].map(tcm).fillna(-1).astype(int)
        frame.loc[:, "track_barrier"] = [
            wp._track_barrier_term(trk, dist, bar, fs, tcm, models["track_barrier_model"])
            for trk, dist, bar, fs in zip(frame["track"], frame["cur_distance"], frame["barrier"], frame["field_size"])
        ]
        frame.loc[:, "trainer_merit"] = [
            wp._merit_term(v, fs, models["trainer_merit_model"], wp._TRAINER_MERIT_FEATURES)
            for v, fs in zip(frame["trainer_win_pct_365d"], frame["field_size"])
        ]
        frame.loc[:, "jockey_merit"] = [
            wp._merit_term(v, fs, models["jockey_merit_model"], wp._JOCKEY_MERIT_FEATURES)
            for v, fs in zip(frame["jockey_win_pct_90d"], frame["field_size"])
        ]
        _computed = [_closing_raw_resid_one(p, models["pace_baseline_lookup"]) for p in frame["closing_pairs"]]
        frame.loc[:, "closing_raw_resid"] = [c[0] for c in _computed]
        frame.loc[:, "closing_n_pairs"] = [c[1] for c in _computed]
        frame.loc[:, "closing_merit"] = [
            wp._closing_merit_term(pairs, models["pace_baseline_lookup"], fs, models["closing_merit_model"])
            for pairs, fs in zip(frame["closing_pairs"], frame["field_size"])
        ]
        for _term in TRAINED_TERMS:
            frame[_term] = frame[_term] - frame.groupby("race_id")[_term].transform("mean")
        return frame

    scored_h1fit = _apply(models_h1, pooled)
    scored_h2fit = _apply(models_h2, pooled)

    print(f"\n{'n same-row comparisons':>28}: {len(pooled):,}")
    print(f"{'term':<16}{'corr':>10}{'mean|diff|':>14}{'std(diff)':>12}{'p90|diff|':>12}")
    for t in TRAINED_TERMS:
        a = scored_h1fit[t].to_numpy()
        b = scored_h2fit[t].to_numpy()
        mask = ~(np.isnan(a) | np.isnan(b))
        diff = a[mask] - b[mask]
        corr = np.corrcoef(a[mask], b[mask])[0, 1] if mask.sum() > 1 else float("nan")
        print(f"{t:<16}{corr:>10.3f}{np.mean(np.abs(diff)):>14.3f}{np.std(diff):>12.3f}{np.percentile(np.abs(diff),90):>12.3f}")

    print("\nReading this: corr close to 1.0 and small mean|diff| = stable (this term's ")
    print("value for a given horse/race barely depends on which half of history fit it).")
    print("Low corr or large mean|diff| relative to the term's own typical magnitude =")
    print("volatile - this term would give a meaningfully different number to the user")
    print("depending on the accident of which retrain window it was fit on.")


def run():
    D = _load_D()
    h1, h2, models_h1, models_h2 = run_ablation(D)
    run_stability(h1, h2, models_h1, models_h2)
    print("\nSame multiple-comparisons caveat as every backtest in this codebase:")
    print("treat this as a hypothesis, not a result to ship blind.")
    print("\nDone.")


if __name__ == "__main__":
    run()
