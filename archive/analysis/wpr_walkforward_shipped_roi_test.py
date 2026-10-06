"""wpr_walkforward_shipped_roi_test.py - the rigorous version of "is the
ACTUAL shipped architecture profitable" (user request, Sep 2026, after
correctly pushing back on wpr_slope_roi_test.py's single bidirectional
half-split as too weak a bar - this codebase's own history
(calibrate_edge_score.py) already has an example of a promising single-
split ROI result that evaporated under a proper walk-forward re-check).

IMPORTANT SCOPE NOTE: wpr_slope_roi_test.py tested the calibration-slope
question using the OLD shrunk-lookup track_barrier/trainer_merit/jockey_
merit/closing_merit (via wpr_own_pace_backtest.add_track_barrier etc,
which were deliberately frozen to the pre-conversion architecture - see
their own docstrings). That test is NOT contaminated by the separate bug
found live (trained models producing a uniform whole-field bias, fixed by
per-race demeaning in wpr_projection.py) - but it also never validated the
ACTUAL shipped architecture (trained models + demeaning + no slope) on
ROI grounds at all. This script does exactly that: walk-forward (monthly
expanding-window refits on strictly-prior data, not one split), using
wpr_projection.py's OWN current functions directly (so it is testing
precisely what compute_wpr_projection() actually serves, demeaning fix
included), comparing:
  - BASELINE: original shipped-before-today architecture (old lookups,
    slope=0.1791) - reconstructed via the SAME frozen helpers wpr_slope_
    roi_test.py uses, for a true like-for-like baseline.
  - NEW: today's actual shipped architecture (trained models, demeaned,
    no slope).

Reports strike rate / ROI / t-stat by edge threshold, pooled across every
fold's held-out bets - each row here is genuinely a held-out result from
a model that never saw that fold's data (expanding window, always fit on
strictly-prior months only).

USAGE
  python wpr_walkforward_shipped_roi_test.py

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np
import pandas as pd
import joblib

import wpr_projection as wpr
from wpr_own_pace_backtest import add_base, add_track_barrier, merge_won_by_horse_date
from wpr_trainer_jockey_adj_strike_eval import FORM_CSV, merge_trainer_jockey_by_horse_date, \
    add_closing_merit, fit_bucket_lookup, apply_bucket
from wpr_bet_selection_post_retrain import merge_price_pfm, report
from wpr_bet_selection_leakfree_eval import _edge_from_score

EDGE_THRESHOLDS = [0.0, 0.02, 0.04, 0.06, 0.08, 0.10, 0.13, 0.15, 0.20]
BETA_GRID = [0.05, 0.10, 0.15, 0.20, 0.25, 0.30, 0.40]
FOLD_MONTHS = ["2026-05", "2026-06", "2026-07", "2026-08", "2026-09"]


def _brier(data, beta):
    rows = []
    for rid, g in data.groupby("race_id"):
        if len(g) < 4:
            continue
        pv = g["wprp_proj"].to_numpy(dtype=float)
        e = np.exp(beta * (pv - pv.max()))
        p = e / e.sum()
        rows.extend(zip(p, g["won"]))
    arr = pd.DataFrame(rows, columns=["p", "won"])
    return float(((arr["p"] - arr["won"]) ** 2).mean()) if len(arr) else float("nan")


def _fit_beta(fit_data):
    best_beta, best_brier = None, float("inf")
    for b in BETA_GRID:
        br = _brier(fit_data, b)
        if br < best_brier:
            best_brier, best_beta = br, b
    return best_beta


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
    print(f"Scoped rows: {len(full):,}  date range {full['date'].min().date()} to {full['date'].max().date()}")
    return full


def score_baseline_fold(fit_data, held_out, fit_cutoff):
    """OLD shrunk-lookup architecture (track_barrier/trainer_merit/jockey_
    merit/closing_merit), slope=0.1791 - the architecture actually shipped
    before today's session, using the SAME frozen helpers wpr_slope_roi_
    test.py validated with."""
    fit_data = fit_data.copy()
    held_out = held_out.copy()
    add_track_barrier(fit_data, [fit_data, held_out])
    add_closing_merit([fit_data, held_out], fit_cutoff)
    edges_t, lookup_t = fit_bucket_lookup(fit_data, "trainer_win_pct_365d")
    edges_j, lookup_j = fit_bucket_lookup(fit_data, "jockey_win_pct_90d")
    for f in (fit_data, held_out):
        apply_bucket(f, "trainer_win_pct_365d", edges_t, lookup_t, "trainer_merit")
        apply_bucket(f, "jockey_win_pct_90d", edges_j, lookup_j, "jockey_merit")
        f["wprp_proj"] = f["_base"].to_numpy() + wpr._cap_adj_sum(
            f[wpr.ADJ_TERMS].to_numpy()).sum(axis=1) * 0.1791
    beta = _fit_beta(fit_data)
    held_out["score_wpr"] = beta * held_out["wprp_proj"]
    held_out["edge_wpr"] = _edge_from_score(held_out, "score_wpr")
    return held_out


def score_shipped_fold(fit_data, held_out):
    """The ACTUAL shipped architecture: trained models for track_barrier/
    trainer_merit/jockey_merit/closing_merit (wpr_projection.py's own
    _fit_simple_adj_model/_fit_coverage_aware_trn), per-race demeaning
    (the bug fix), no calibration slope - fit strictly on fit_data, scored
    on held_out, using wpr_projection's CURRENT functions directly so this
    is testing exactly what compute_wpr_projection() serves today."""
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
        # per-race demeaning - the bug fix, must match project_race() exactly
        for term in ("track_barrier", "closing_merit", "trainer_merit", "jockey_merit"):
            f[term] = f[term] - f.groupby("race_id")[term].transform("mean")
        f["wprp_proj"] = f["_base"].to_numpy() + wpr._cap_adj_sum(f[wpr.ADJ_TERMS].to_numpy()).sum(axis=1)

    beta = _fit_beta(fit_data)
    held_out["score_wpr"] = beta * held_out["wprp_proj"]
    held_out["edge_wpr"] = _edge_from_score(held_out, "score_wpr")
    return held_out


def report_edge(bets, label):
    print(f"\n{'='*70}\n{label}\n{'='*70}")
    if len(bets) == 0:
        print("  no bets")
        return
    print(f"total held-out bets: {len(bets):,}  [population avg price ${bets['sp'].mean():.2f}]")
    for thr in EDGE_THRESHOLDS:
        report(bets[bets["edge_wpr"] >= thr], f"edge>={thr:.2f}")


def run():
    full = build_frame()
    full["month"] = full["date"].dt.to_period("M").astype(str)

    baseline_bets, shipped_bets = [], []
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
        baseline_bets.append(score_baseline_fold(fit_data, held_out, fit_data["date"].max()))
        shipped_bets.append(score_shipped_fold(fit_data, held_out))

    baseline_pooled = pd.concat(baseline_bets, ignore_index=True)
    shipped_pooled = pd.concat(shipped_bets, ignore_index=True)

    report_edge(baseline_pooled, "WALK-FORWARD: BASELINE (old lookups, slope=0.1791) - shipped before today")
    report_edge(shipped_pooled, "WALK-FORWARD: SHIPPED TODAY (trained models, demeaned, no slope)")


if __name__ == "__main__":
    run()
