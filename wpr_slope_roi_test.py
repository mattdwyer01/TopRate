"""wpr_slope_roi_test.py - the ROI-relevant version of the calibration-slope
question (user request, Sep 2026): MAE rewards a rating that hugs the
consensus (base) and rarely disagrees with it sharply - which is close to
the OPPOSITE of what finds a genuine market overlay. A rating allowed to
move further from base (higher variance, worse MAE) might be "wrong" more
often in absolute terms while still being MORE profitable, if the extra
movement is real signal the market hasn't priced. This tests that directly
against real starting prices and results, using the exact same leak-free
bidirectional half-split methodology already validated in
wpr_bet_selection_leakfree_eval.py (fit every population ADJ_TERM lookup +
price-softmax beta on one half, score/bet purely on the other, pool both
directions) - the only thing varied here is _CALIB_ADJ_SLOPE itself, at
several candidate values, all other architecture held at the SHIPPED
config.

Reports strike rate / ROI / t-stat by edge threshold (WPR price alone -
already validated in calibrate_edge_score.py to beat every blend variant
on ROI, so this isolates the slope question rather than re-litigating the
blend question) for each candidate slope.

USAGE
  python wpr_slope_roi_test.py

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np
import pandas as pd

import wpr_projection as wpr
from wpr_own_pace_backtest import add_base, add_track_barrier, merge_won_by_horse_date
from wpr_trainer_jockey_adj_strike_eval import FORM_CSV, merge_trainer_jockey_by_horse_date, \
    add_closing_merit, fit_bucket_lookup, apply_bucket
from wpr_bet_selection_post_retrain import merge_price_pfm, report
from wpr_bet_selection_leakfree_eval import _edge_from_score

SLOPES = [0.1791, 0.35, 0.50, 0.70, 1.00]
EDGE_THRESHOLDS = [0.0, 0.02, 0.04, 0.06, 0.08, 0.10, 0.13, 0.15, 0.20]
BETA_GRID = [0.05, 0.10, 0.15, 0.20, 0.25, 0.30, 0.40]


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


def _fit_beta(fit_half):
    best_beta, best_brier = None, float("inf")
    for b in BETA_GRID:
        br = _brier(fit_half, b)
        if br < best_brier:
            best_brier, best_beta = br, b
    return best_beta


def fit_and_score(fit_half, held_out, fit_cutoff, slope):
    """Same population-term fitting as wpr_bet_selection_leakfree_eval's
    fit_and_score, but wprp_proj uses the PASSED-IN slope instead of the
    live wpr._CALIB_ADJ_SLOPE constant - isolates the slope question while
    keeping every other artifact (lookups, beta) fit exactly the same way."""
    add_track_barrier(fit_half, [fit_half, held_out])
    add_closing_merit([fit_half, held_out], fit_cutoff)
    edges_t, lookup_t = fit_bucket_lookup(fit_half, "trainer_win_pct_365d")
    edges_j, lookup_j = fit_bucket_lookup(fit_half, "jockey_win_pct_90d")
    for f in (fit_half, held_out):
        apply_bucket(f, "trainer_win_pct_365d", edges_t, lookup_t, "trainer_merit")
        apply_bucket(f, "jockey_win_pct_90d", edges_j, lookup_j, "jockey_merit")
        f["wprp_proj"] = f["_base"].to_numpy() + wpr._cap_adj_sum(
            f[wpr.ADJ_TERMS].to_numpy()).sum(axis=1) * slope

    beta = _fit_beta(fit_half)
    held_out = held_out.copy()
    held_out["score_wpr"] = beta * held_out["wprp_proj"]
    held_out["edge_wpr"] = _edge_from_score(held_out, "score_wpr")
    held_out["fit_beta"] = beta
    return held_out


def report_edge(bets, label):
    print(f"\n{'='*70}\n{label}\n{'='*70}")
    print(f"total held-out bets: {len(bets):,}  [population avg price ${bets['sp'].mean():.2f}]")
    for thr in EDGE_THRESHOLDS:
        report(bets[bets["edge_wpr"] >= thr], f"edge>={thr:.2f}")


def run():
    print("Rebuilding training frame...")
    full = wpr.build_training_frame(FORM_CSV, verbose=True, n_jobs=-1)
    full["date"] = pd.to_datetime(full["date"])

    print("\nMerging result, trainer/jockey win-rate, price and pfm_score...")
    full = merge_won_by_horse_date(full)
    full = merge_trainer_jockey_by_horse_date(full)
    full = merge_price_pfm(full)
    full = add_base(full)

    # pace_shape: added to ADJ_TERMS this session, not part of
    # wpr_own_pace_backtest's own_* set the older bet-selection scripts were
    # written against. Only has leak-safe coverage for the last ~365 days
    # (see its own module docstring) - applying the ALREADY-SHIPPED, already
    # -validated model as a FIXED input here (not re-fit per half) is the
    # same "reuse a validated fixed input" pattern the term itself already
    # uses for its own two ingredients, and keeps this test focused on the
    # slope question rather than re-deriving pace_shape's own day-by-day
    # scoring twice per slope value. Falls back to 0.0 (its live "unseen ->
    # 0" contract) outside that window, same as track_barrier/gear_change/
    # etc - NOT required in the dropna below (that would gut the dataset to
    # one year for no reason relevant to this test).
    print("  building pace_shape (shipped model, fixed input)...")
    since = (full["date"].max() - pd.Timedelta(days=365)).strftime("%Y-%m-%d")
    race_id_to_score = wpr._build_pace_shape_race_scores(since)
    _name_map, _ = wpr._load_trainer_jockey_by_horse_date(FORM_CSV)
    full["horse_lc"] = full["horse_id"].map(_name_map).astype(str).str.lower()
    settle_lookup = wpr._build_pace_shape_settle_lookup(since)
    full["pace_score"] = full["race_id"].map(race_id_to_score)
    full["predicted_rel_settle"] = [settle_lookup.get((h, d)) for h, d in zip(full["horse_lc"], full["date"])]
    import joblib
    _pace_model = joblib.load("wpr_models/pace_shape.joblib")
    full["pace_shape"] = [
        wpr._pace_shape_term(ps, prs, fs, _pace_model)
        for ps, prs, fs in zip(full["pace_score"], full["predicted_rel_settle"], full["field_size"])
    ]

    non_pop_terms = [t for t in wpr.ADJ_TERMS
                     if t not in ("track_barrier", "closing_merit", "trainer_merit", "jockey_merit", "pace_shape")]
    full = full.dropna(subset=["target", "_base", "career_avg"] + non_pop_terms +
                        ["barrier", "field_size", "track", "cur_distance"])
    sp = pd.to_numeric(full["fixed_win_price"], errors="coerce")
    sp_fallback = pd.to_numeric(full["starting_price_sp"], errors="coerce")
    full["sp"] = sp.fillna(sp_fallback)
    full = full.dropna(subset=["sp"])
    full = full[full["sp"] > 1.0]
    print(f"\nScoped rows: {len(full):,}")

    mid = full["date"].quantile(0.5)
    h1, h2 = full[full["date"] < mid].copy(), full[full["date"] >= mid].copy()
    print(f"H1: {len(h1):,} rows (< {mid.date()}), H2: {len(h2):,} rows (>= {mid.date()})")

    for slope in SLOPES:
        print(f"\n\n{'#'*70}\n# SLOPE = {slope}\n{'#'*70}")
        h2_scored = fit_and_score(h1.copy(), h2.copy(), h1["date"].max(), slope)
        h1_scored = fit_and_score(h2.copy(), h1.copy(), h2["date"].max(), slope)
        pooled = pd.concat([h1_scored, h2_scored], ignore_index=True)
        tag = " <- shipped" if abs(slope - 0.1791) < 1e-6 else (" <- removed" if slope >= 1.0 else "")
        report_edge(pooled, f"slope={slope}{tag}  (WPR price alone, beta refit per direction)")


if __name__ == "__main__":
    run()
