"""
wpr_passage_risk_adj_term_test.py - builds "passage_risk" as a real
candidate ADJ_TERM and tests it against this codebase's actual adoption
bar, following up on wpr_passage_quality_predictive_test.py /
wpr_passage_risk_vs_residual_test.py (barrier+field_size predict a
runner's bad-passage risk with real, held-out-confirmed skill: AUC 0.632,
and that risk correlates with the actual WPR residual out of sample,
diff=-0.46 top-vs-bottom quintile, t=-2.81, p=0.005).

ARCHITECTURE CHOICE: a ONE-STAGE model (barrier+field_size -> residual
directly via wp._fit_simple_adj_model), not the two-stage "predict bad-
passage label, then correlate" version used for validation - the label
was a diagnostic tool to confirm the mechanism was real, not something
the shipped term needs. This matches EXACTLY how pop_distance/pop_going/
track_barrier are already built (raw pre-race feature -> residual,
never via an intermediate text-derived label), and has a real practical
advantage: barrier and field_size are ALWAYS known pre-race, unlike
comments_video which is sparse/historical only.

SCOPE LIMITATION (stated plainly): the canonical adoption test for new
ADJ_TERMS in this codebase (wpr_new_adj_terms_candidate_test.py) uses a
leave-one-era-out test across 5 real 10-year eras via a cached D
(wpr_10yr_D_cache.pkl) - that cache does not exist in this session (it
lived in a different session's scratchpad and was never rebuilt here;
rebuilding it from race_results_*.csv.gz is a substantial undertaking
of its own). This test instead uses the SAME leak-free bidirectional
half-split already validated and used repeatedly tonight
(wpr_slope_roi_test.py's fit_and_score pattern) over the ~5-month window
build_training_frame() can cover with current price/pfm data. Smaller
and more recent than the canonical 10-year test, not a substitute for
it - flagged here so nobody mistakes this for the full adoption
methodology.

TWO METRICS, both reported (tonight's own lesson: MAE and ROI can
diverge - the slope-removal decision itself is proof of that in this
exact codebase):
  1. Held-out MAE, baseline vs baseline+passage_risk (this codebase's
     own historical adoption bar for a new ADJ_TERM has ranged ~0.01-
     0.03 delta depending on the term - see ADJ_TERMS history comments
     in wpr_projection.py).
  2. Held-out ROI/strike/t-stat by edge threshold, same convention as
     wpr_slope_roi_test.py, at the LIVE shipped slope (0.1791) - this is
     testing "should this be added to the current model", not
     re-litigating the slope question.

Per-race demeaning applied to passage_risk before scoring, same
treatment every other population-level term (track_barrier/closing_
merit/trainer_merit/jockey_merit/pop_distance/pop_going) already gets in
the canonical test - only a runner's value RELATIVE to its own race
matters for picking a winner, not the model's absolute predicted level.

NO EM DASHES policy: hyphens only.
"""
import numpy as np
import pandas as pd

import wpr_projection as wpr
from wpr_bet_selection_post_retrain import report
from wpr_slope_roi_test import EDGE_THRESHOLDS, _fit_beta
from wpr_slope_roi_first_up_slice import add_pop_distance_going
import wpr_slope_roi_test as roi

SHIPPED_SLOPE = 0.1791


def add_passage_risk(fit_half, apply_frames):
    """Fit passage_risk on fit_half only (leak-free), apply + per-race
    demean on every frame in apply_frames. Same fit-on-one-half/apply-to-
    both/demean-per-race pattern the canonical adoption test uses for
    every population-level candidate term."""
    trn = fit_half.dropna(subset=["target", "career_avg", "barrier", "field_size"])
    model = wpr._fit_simple_adj_model(trn, ["barrier", "field_size"], "passage_risk")
    for frame in apply_frames:
        frame["passage_risk"] = [
            wpr._merit_term(b, fs, model, ["barrier", "field_size"])
            for b, fs in zip(frame["barrier"], frame["field_size"])
        ]
        frame["passage_risk"] = (
            frame["passage_risk"] - frame.groupby("race_id")["passage_risk"].transform("mean")
        ).fillna(0.0)
    return model


def fit_and_score_full(fit_half, held_out, fit_cutoff, slope=SHIPPED_SLOPE):
    """Same population-term fitting as wpr_slope_roi_test.fit_and_score,
    but ALSO adds pop_distance/pop_going (the staleness fix from
    wpr_slope_roi_first_up_slice.py) and passage_risk - so both variants
    tested below (with/without passage_risk) share every other term
    identically, isolating passage_risk's own marginal contribution."""
    from wpr_own_pace_backtest import add_track_barrier
    from wpr_trainer_jockey_adj_strike_eval import add_closing_merit, fit_bucket_lookup, apply_bucket

    add_track_barrier(fit_half, [fit_half, held_out])
    add_closing_merit([fit_half, held_out], fit_cutoff)
    edges_t, lookup_t = fit_bucket_lookup(fit_half, "trainer_win_pct_365d")
    edges_j, lookup_j = fit_bucket_lookup(fit_half, "jockey_win_pct_90d")
    for f in (fit_half, held_out):
        apply_bucket(f, "trainer_win_pct_365d", edges_t, lookup_t, "trainer_merit")
        apply_bucket(f, "jockey_win_pct_90d", edges_j, lookup_j, "jockey_merit")
    add_pop_distance_going(fit_half, [fit_half, held_out])
    add_passage_risk(fit_half, [fit_half, held_out])

    # _fit_beta/_brier need wprp_proj on fit_half - compute it using the
    # BASELINE (current shipped 10-term) formula at the live slope, not a
    # passage_risk-inclusive one: beta should reflect how the model is
    # ACTUALLY priced today, so both variants scored later share one beta
    # and the comparison isolates passage_risk's own effect rather than
    # also re-optimizing beta jointly with the candidate term.
    fit_half["wprp_proj"] = fit_half["_base"].to_numpy() + wpr._cap_adj_sum(
        fit_half[wpr.ADJ_TERMS].fillna(0.0).to_numpy()).sum(axis=1) * SHIPPED_SLOPE

    beta = _fit_beta(fit_half)
    return fit_half, held_out, beta


def score_variant(held_out, beta, terms):
    """Additive prediction using exactly `terms` (a list of ADJ_TERMS
    column names, already present on held_out), capped the same way
    project_race() caps the adjustment sum, at the live shipped slope."""
    adj = wpr._cap_adj_sum(held_out[terms].fillna(0.0).to_numpy()).sum(axis=1) * SHIPPED_SLOPE
    proj = held_out["_base"].to_numpy() + adj
    mae = float(np.abs(held_out["target"].to_numpy() - proj).mean())

    scored = held_out.copy()
    scored["wprp_proj"] = proj
    scored["score_wpr"] = beta * scored["wprp_proj"]
    scored["edge_wpr"] = roi._edge_from_score(scored, "score_wpr")
    return mae, scored


def run():
    print("Rebuilding training frame (same as wpr_slope_roi_test.py)...")
    full = wpr.build_training_frame(roi.FORM_CSV, verbose=True, n_jobs=-1)
    full["date"] = pd.to_datetime(full["date"])

    from wpr_own_pace_backtest import add_base, merge_won_by_horse_date
    from wpr_trainer_jockey_adj_strike_eval import merge_trainer_jockey_by_horse_date
    from wpr_bet_selection_post_retrain import merge_price_pfm
    import joblib

    print("Merging result, trainer/jockey win-rate, price and pfm_score...")
    full = merge_won_by_horse_date(full)
    full = merge_trainer_jockey_by_horse_date(full)
    full = merge_price_pfm(full)
    full = add_base(full)

    print("  building pace_shape (shipped model, fixed input)...")
    since = (full["date"].max() - pd.Timedelta(days=365)).strftime("%Y-%m-%d")
    race_id_to_score = wpr._build_pace_shape_race_scores(since)
    _name_map, _ = wpr._load_trainer_jockey_by_horse_date(roi.FORM_CSV)
    full["horse_lc"] = full["horse_id"].map(_name_map).astype(str).str.lower()
    settle_lookup = wpr._build_pace_shape_settle_lookup(since)
    full["pace_score"] = full["race_id"].map(race_id_to_score)
    full["predicted_rel_settle"] = [settle_lookup.get((h, d)) for h, d in zip(full["horse_lc"], full["date"])]
    _pace_model = joblib.load("wpr_models/pace_shape.joblib")
    full["pace_shape"] = [
        wpr._pace_shape_term(ps, prs, fs, _pace_model)
        for ps, prs, fs in zip(full["pace_score"], full["predicted_rel_settle"], full["field_size"])
    ]

    own_history_terms = ["own_first_up", "own_second_up", "own_long_spell"]
    full = full.dropna(subset=["target", "_base", "career_avg"] + own_history_terms +
                        ["barrier", "field_size", "track", "cur_distance", "race_id"])
    sp = pd.to_numeric(full["fixed_win_price"], errors="coerce")
    sp_fallback = pd.to_numeric(full["starting_price_sp"], errors="coerce")
    full["sp"] = sp.fillna(sp_fallback)
    full = full.dropna(subset=["sp"])
    full = full[full["sp"] > 1.0]
    print(f"Scoped rows: {len(full):,}")

    mid = full["date"].quantile(0.5)
    h1, h2 = full[full["date"] < mid].copy(), full[full["date"] >= mid].copy()
    print(f"H1: {len(h1):,} rows (< {mid.date()}), H2: {len(h2):,} rows (>= {mid.date()})")

    BASELINE_TERMS = list(wpr.ADJ_TERMS)  # current shipped 10-term set
    CANDIDATE_TERMS = BASELINE_TERMS + ["passage_risk"]

    total_mae = {"baseline": 0.0, "candidate": 0.0}
    total_n = 0
    pooled_scored = {"baseline": [], "candidate": []}

    for fit_h, held_h, cutoff_label in [(h1, h2, h1["date"].max()), (h2, h1, h2["date"].max())]:
        fit_half, held_out, beta = fit_and_score_full(fit_h.copy(), held_h.copy(), cutoff_label)
        n = len(held_out)
        total_n += n
        for name, terms in [("baseline", BASELINE_TERMS), ("candidate", CANDIDATE_TERMS)]:
            mae, scored = score_variant(held_out, beta, terms)
            total_mae[name] += mae * n
            pooled_scored[name].append(scored)
            print(f"  direction (held-out n={n}): {name} MAE={mae:.4f}")

    print("\n" + "=" * 78)
    print("MAE ADOPTION CHECK (pooled bidirectional held-out)")
    print("=" * 78)
    baseline_mae = total_mae["baseline"] / total_n
    candidate_mae = total_mae["candidate"] / total_n
    delta = candidate_mae - baseline_mae
    print(f"baseline (current shipped {len(BASELINE_TERMS)} terms): MAE = {baseline_mae:.4f}")
    print(f"candidate (+ passage_risk):                              MAE = {candidate_mae:.4f}")
    print(f"delta: {delta:+.4f}  ({'IMPROVEMENT' if delta < 0 else 'WORSE'})")
    print("(this codebase's own historical adoption bar for a new ADJ_TERM has ranged")
    print(" roughly -0.01 to -0.03 delta depending on the term - see ADJ_TERMS history")
    print(" comments in wpr_projection.py for precedents)")

    print("\n" + "=" * 78)
    print("ROI CHECK (pooled bidirectional held-out, live shipped slope 0.1791)")
    print("=" * 78)
    for name in ("baseline", "candidate"):
        pooled = pd.concat(pooled_scored[name], ignore_index=True)
        print(f"\n--- {name} ---")
        print(f"total held-out bets: {len(pooled):,}  [population avg price ${pooled['sp'].mean():.2f}]")
        for thr in EDGE_THRESHOLDS:
            report(pooled[pooled["edge_wpr"] >= thr], f"edge>={thr:.2f}")


if __name__ == "__main__":
    run()
