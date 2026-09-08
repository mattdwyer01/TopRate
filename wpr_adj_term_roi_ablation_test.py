"""wpr_adj_term_roi_ablation_test.py - ROI/edge version of wpr_adj_term_
ablation_test.py (user follow-up request, Sep 2026): does each ADJ_TERM's
inclusion actually improve the model's OVERLAY-DETECTION value, not just
point-accuracy MAE? The MAE-based ablation (wpr_adj_term_ablation_test.py)
showed nearly every term "hurts MAE" once the calibration slope was removed
- an expected side effect of summing noisy-but-real terms without shrinkage,
not evidence the terms are bad - so MAE is no longer the right lens to judge
individual terms under the current (slope-removed) architecture. This script
re-runs the same idea against the metric that actually matters for bet
selection: held-out ROI / t-stat on flagged overlays (edge = model_prob -
market_prob, same definition as wpr_projection.compute_edge_scores(), see
that function's docstring - mattdwyer01/TopRate#146).

Methodology: same walk-forward fold structure as wpr_walkforward_shipped_
roi_test.py (monthly expanding window, always fit strictly-prior data, no
leakage) - fits every population-term model ONCE per fold (shared across all
term variants below, for speed) exactly as score_shipped_fold() does, then
ALSO fits a gear_change model (trained, but never added to live ADJ_TERMS -
see wpr_adj_term_ablation_test.py's docstring for why it's tested as a
candidate ADD here too). For each candidate term:
  - if it's a live ADJ_TERM: recombine the already-computed term columns
    into an alternate wprp_proj with that term REMOVED, refit beta on the
    alternate fit_data projection, score held_out, and compare pooled
    edge>=0.10 ROI/strike/t against the FULL (all-terms) model at the same
    threshold. A term is earning its ROI keep if full > without.
  - gear_change (not live): the alternate wprp_proj has it ADDED to the
    full set instead. It passes if with-added > full.

USAGE
  python wpr_adj_term_roi_ablation_test.py

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np
import pandas as pd
import joblib

import wpr_projection as wpr
from wpr_own_pace_backtest import add_base, merge_won_by_horse_date
from wpr_trainer_jockey_adj_strike_eval import FORM_CSV, merge_trainer_jockey_by_horse_date
from wpr_bet_selection_post_retrain import merge_price_pfm
from wpr_bet_selection_leakfree_eval import _edge_from_score
from wpr_adj_term_ablation_test import build_frame as build_mae_frame

EDGE_THRESHOLD = 0.10
BETA_GRID = [0.05, 0.10, 0.15, 0.20, 0.25, 0.30, 0.40]
FOLD_MONTHS = ["2026-05", "2026-06", "2026-07", "2026-08", "2026-09"]

ALL_TERMS_FULL = list(wpr.ADJ_TERMS)
CANDIDATES = ALL_TERMS_FULL + ["gear_change"]


def build_frame():
    print("Building training frame...")
    full = wpr.build_training_frame(FORM_CSV, verbose=True, n_jobs=-1)
    full["date"] = pd.to_datetime(full["date"])
    full = merge_won_by_horse_date(full)
    full = merge_trainer_jockey_by_horse_date(full)
    full = merge_price_pfm(full)
    full = add_base(full)

    non_pop_terms = [t for t in wpr.ADJ_TERMS
                     if t not in ("track_barrier", "closing_merit", "trainer_merit", "jockey_merit", "pace_shape")]
    full = full.dropna(subset=["target", "_base", "career_avg"] + non_pop_terms +
                        ["barrier", "field_size", "track", "cur_distance"])
    sp = pd.to_numeric(full["fixed_win_price"], errors="coerce")
    sp_fallback = pd.to_numeric(full["starting_price_sp"], errors="coerce")
    full["sp"] = sp.fillna(sp_fallback)
    full = full.dropna(subset=["sp"])
    full = full[full["sp"] > 1.0]

    print("  building pace_shape (shipped model, fixed input)...")
    since = (full["date"].max() - pd.Timedelta(days=365)).strftime("%Y-%m-%d")
    race_id_to_score = wpr._build_pace_shape_race_scores(since)
    _name_map, _ = wpr._load_trainer_jockey_by_horse_date(FORM_CSV)
    full["horse_lc"] = full["horse_id"].map(_name_map).astype(str).str.lower()
    settle_lookup = wpr._build_pace_shape_settle_lookup(since)
    full["pace_score"] = full["race_id"].map(race_id_to_score)
    full["predicted_rel_settle"] = [settle_lookup.get((h, d)) for h, d in zip(full["horse_lc"], full["date"])]
    _pace_model = joblib.load("wpr_models/pace_shape.joblib")
    full["pace_shape"] = [
        wpr._pace_shape_term(ps, prs, fs, _pace_model)
        for ps, prs, fs in zip(full["pace_score"], full["predicted_rel_settle"], full["field_size"])
    ]

    # gear_change ingredients (candidate-only, not in ALL_TERMS_FULL)
    full["gear_bucket"] = full["gear_changes"].apply(wpr._gear_change_bucket)
    print(f"Scoped rows: {len(full):,}  date range {full['date'].min().date()} to {full['date'].max().date()}")
    return full


def _brier(data, col, beta):
    rows = []
    for rid, g in data.groupby("race_id"):
        if len(g) < 4:
            continue
        pv = g[col].to_numpy(dtype=float)
        e = np.exp(beta * (pv - pv.max()))
        p = e / e.sum()
        rows.extend(zip(p, g["won"]))
    arr = pd.DataFrame(rows, columns=["p", "won"])
    return float(((arr["p"] - arr["won"]) ** 2).mean()) if len(arr) else float("nan")


def _fit_beta(fit_data, col):
    best_beta, best_brier = None, float("inf")
    for b in BETA_GRID:
        br = _brier(fit_data, col, b)
        if br < best_brier:
            best_brier, best_beta = br, b
    return best_beta


def fit_fold_terms(fit_data, held_out):
    """Fits every population-term model (including gear_change) ONCE on
    fit_data, applies to BOTH fit_data and held_out (with per-race
    demeaning matching live serving). Leaves individual term columns in
    place on both frames so the ablation step below can recombine them
    without re-fitting anything per-candidate."""
    fit_data = fit_data.copy()
    held_out = held_out.copy()
    track_categories = sorted(fit_data["track"].dropna().unique())
    track_code_map = {t: i for i, t in enumerate(track_categories)}
    fit_data["track_code"] = fit_data["track"].map(track_code_map).fillna(-1).astype(int)
    tb_model = wpr._fit_simple_adj_model(fit_data, wpr._TRACK_BARRIER_FEATURES, "track_barrier")

    trm_trn = wpr._fit_coverage_aware_trn(fit_data, ["trainer_win_pct_365d"])
    trm_model = wpr._fit_simple_adj_model(trm_trn, wpr._TRAINER_MERIT_FEATURES, "trainer_merit")
    jm_trn = wpr._fit_coverage_aware_trn(fit_data, ["jockey_win_pct_90d"])
    jm_model = wpr._fit_simple_adj_model(jm_trn, wpr._JOCKEY_MERIT_FEATURES, "jockey_merit")

    fit_data["gear_code"] = fit_data["gear_bucket"].map(wpr._GEAR_BUCKET_CODE).fillna(0).astype(int)
    gc_model = wpr._fit_simple_adj_model(fit_data, wpr._GEAR_CHANGE_FEATURES, "gear_change")

    pace_baseline_lookup = wpr._fit_pace_baseline(FORM_CSV, fit_data["date"].max())

    def _closing_raw_resid_one(pairs):
        vals = []
        for sect, bucket in pairs:
            exp = pace_baseline_lookup.get(bucket)
            if exp is not None and sect is not None and sect == sect:
                vals.append(float(sect) - float(exp))
        return (float(np.mean(vals)), float(len(vals))) if vals else (np.nan, 0.0)

    for f in (fit_data, held_out):
        _computed = [_closing_raw_resid_one(p) for p in f["closing_pairs"]]
        f["closing_raw_resid"] = [c[0] for c in _computed]
        f["closing_n_pairs"] = [c[1] for c in _computed]
    cm_model = wpr._fit_simple_adj_model(fit_data, wpr._CLOSING_MERIT_FEATURES, "closing_merit")

    for f in (fit_data, held_out):
        f["track_code"] = f["track"].map(track_code_map).fillna(-1).astype(int)
        f["track_barrier"] = [
            wpr._track_barrier_term(trk, dist, bar, fs, track_code_map, tb_model)
            for trk, dist, bar, fs in zip(f["track"], f["cur_distance"], f["barrier"], f["field_size"])
        ]
        f["trainer_merit"] = [
            wpr._merit_term(v, fs, trm_model, wpr._TRAINER_MERIT_FEATURES)
            for v, fs in zip(f["trainer_win_pct_365d"], f["field_size"])
        ]
        f["jockey_merit"] = [
            wpr._merit_term(v, fs, jm_model, wpr._JOCKEY_MERIT_FEATURES)
            for v, fs in zip(f["jockey_win_pct_90d"], f["field_size"])
        ]
        f["closing_merit"] = [
            wpr._closing_merit_term(pairs, pace_baseline_lookup, fs, cm_model)
            for pairs, fs in zip(f["closing_pairs"], f["field_size"])
        ]
        f["gear_code"] = f["gear_bucket"].map(wpr._GEAR_BUCKET_CODE).fillna(0).astype(int)
        f["gear_change"] = [
            wpr._gear_change_term(b, fs, fu, su, nr, gc_model)
            for b, fs, fu, su, nr in zip(f["gear_bucket"], f["field_size"], f["first_up"], f["second_up"], f["n_runs"])
        ]
        for term in ("track_barrier", "closing_merit", "trainer_merit", "jockey_merit", "gear_change"):
            f[term] = f[term] - f.groupby("race_id")[term].transform("mean")
        f["wprp_proj"] = f["_base"].to_numpy() + wpr._cap_adj_sum(f[ALL_TERMS_FULL].to_numpy()).sum(axis=1)

    return fit_data, held_out


def score_variant(fit_data, held_out, term_list):
    """Recombines already-fitted term columns into an alternate wprp_proj
    using exactly term_list, refits beta on fit_data's alternate
    projection, scores held_out. No model is refit here - only the sum and
    beta search, so this is cheap to call once per candidate per fold."""
    fit_data = fit_data.copy()
    held_out = held_out.copy()
    col = "_alt_proj"
    fit_data[col] = fit_data["_base"].to_numpy() + wpr._cap_adj_sum(fit_data[term_list].to_numpy()).sum(axis=1)
    held_out[col] = held_out["_base"].to_numpy() + wpr._cap_adj_sum(held_out[term_list].to_numpy()).sum(axis=1)
    beta = _fit_beta(fit_data, col)
    held_out["score_wpr"] = beta * held_out[col]
    held_out["edge_wpr"] = _edge_from_score(held_out, "score_wpr")
    return held_out


def roi_stats(sub):
    n = len(sub)
    if n < 20:
        return {"n": n, "strike": None, "roi": None, "t": None}
    profit = np.where(sub["won"] == 1, sub["sp"] - 1, -1.0)
    se = profit.std(ddof=1) / np.sqrt(n)
    t = float(profit.mean() / se) if se > 0 else float("nan")
    return {"n": n, "strike": round(float(sub["won"].mean() * 100), 2),
            "roi": round(float(profit.sum() / n * 100), 2), "t": round(t, 2)}


def run():
    full = build_frame()

    # pooled held-out frame per variant: "full" (all live terms) plus one
    # variant per candidate (without it, or with-added for gear_change)
    pooled = {"full": []}
    for term in CANDIDATES:
        pooled[term] = []

    for month in FOLD_MONTHS:
        fold_start = pd.Timestamp(month + "-01")
        fold_end = fold_start + pd.offsets.MonthBegin(1)
        fit_data = full[full["date"] < fold_start]
        held_out = full[(full["date"] >= fold_start) & (full["date"] < fold_end)]
        print(f"\nFold {month}: fit={len(fit_data):,} (< {fold_start.date()}), "
              f"held_out={len(held_out):,} races={held_out['race_id'].nunique()}")
        if len(fit_data) < 2000 or len(held_out) < 50:
            print("  skipping fold (insufficient data)")
            continue

        fit_scored, held_scored = fit_fold_terms(fit_data, held_out)

        pooled["full"].append(score_variant(fit_scored, held_scored, ALL_TERMS_FULL))
        for term in CANDIDATES:
            if term in ALL_TERMS_FULL:
                term_list = [t for t in ALL_TERMS_FULL if t != term]
            else:
                term_list = ALL_TERMS_FULL + [term]
            pooled[term].append(score_variant(fit_scored, held_scored, term_list))

    full_pooled = pd.concat(pooled["full"], ignore_index=True)
    full_stats = roi_stats(full_pooled[full_pooled["edge_wpr"] >= EDGE_THRESHOLD])
    print(f"\n{'='*90}")
    print(f"FULL MODEL (all {len(ALL_TERMS_FULL)} live terms), edge>={EDGE_THRESHOLD:.2f}: "
          f"n={full_stats['n']}  strike={full_stats['strike']}%  ROI={full_stats['roi']}%  t={full_stats['t']}")
    print(f"{'='*90}")
    print(f"{'term':<16} {'variant':<14} {'n':>7} {'strike%':>8} {'ROI%':>8} {'t':>7}   verdict")
    for term in CANDIDATES:
        term_pooled = pd.concat(pooled[term], ignore_index=True)
        stats = roi_stats(term_pooled[term_pooled["edge_wpr"] >= EDGE_THRESHOLD])
        is_add = term not in ALL_TERMS_FULL
        variant_label = "with-added" if is_add else "without"
        if stats["roi"] is None or full_stats["roi"] is None:
            verdict = "REVIEW (insufficient n)"
        elif is_add:
            verdict = "ADD (improves ROI)" if stats["roi"] > full_stats["roi"] else "SKIP (does not improve ROI)"
        else:
            verdict = "KEEP (removing hurts ROI)" if full_stats["roi"] > stats["roi"] else "REVIEW (removing does not hurt ROI)"
        print(f"{term:<16} {variant_label:<14} {stats['n']:>7} {str(stats['strike']):>8} "
              f"{str(stats['roi']):>8} {str(stats['t']):>7}   {verdict}")


if __name__ == "__main__":
    run()
