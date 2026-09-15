"""
wpr_review_terms_removal_test.py - follow-up to wpr_adj_term_roi_ablation_test.py's
monthly walk-forward ablation, which flagged 5 live ADJ_TERMS as REVIEW
(removing them did not hurt ROI at edge>=0.10 in that test): own_second_up,
own_long_spell, pace_shape, pop_distance, pop_going.

WHY THIS EXISTS: that walk-forward test has much less statistical power per
term than this session's other tests tonight (~2,000-2,200 held-out rows
per term at one edge threshold, one point-estimate comparison, no
significance test on the delta itself) - "REVIEW" there means "not proven
to help", not "proven useless". This retests the same 5 terms' removal
(individually AND jointly) against the SAME leak-free bidirectional
half-split MAE+ROI adoption bar used for closing_merit/passage_risk
tonight (~48,000 pooled held-out rows, both chronological directions),
for a fairer read with real statistical power behind it.

Same scope limitation as every test tonight: ~5-month bidirectional
half-split (build_training_frame()'s real coverage), not the canonical
leave-one-era-out 10-year test (its cache lives in another session).

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
REVIEW_TERMS = ["own_second_up", "own_long_spell", "pace_shape", "pop_distance", "pop_going"]


def fit_and_score_full(fit_half, held_out, fit_cutoff):
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

    fit_half["wprp_proj"] = fit_half["_base"].to_numpy() + wpr._cap_adj_sum(
        fit_half[wpr.ADJ_TERMS].fillna(0.0).to_numpy()).sum(axis=1) * SHIPPED_SLOPE
    beta = _fit_beta(fit_half)
    return fit_half, held_out, beta


def score_variant(held_out, beta, terms):
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
                        ["pace_shape", "barrier", "field_size", "track", "cur_distance", "race_id"])
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
    VARIANTS = {"baseline": BASELINE_TERMS}
    for t in REVIEW_TERMS:
        VARIANTS[f"minus_{t}"] = [x for x in BASELINE_TERMS if x != t]
    VARIANTS["minus_all_review"] = [x for x in BASELINE_TERMS if x not in REVIEW_TERMS]

    total_mae = {name: 0.0 for name in VARIANTS}
    total_n = 0
    pooled_scored = {name: [] for name in VARIANTS}

    for fit_h, held_h, cutoff_label in [(h1, h2, h1["date"].max()), (h2, h1, h2["date"].max())]:
        fit_half, held_out, beta = fit_and_score_full(fit_h.copy(), held_h.copy(), cutoff_label)
        n = len(held_out)
        total_n += n
        for name, terms in VARIANTS.items():
            mae, scored = score_variant(held_out, beta, terms)
            total_mae[name] += mae * n
            pooled_scored[name].append(scored)
            print(f"  direction (held-out n={n}): {name} MAE={mae:.4f}")

    print("\n" + "=" * 78)
    print("MAE CHECK: does REMOVING each REVIEW term improve held-out MAE?")
    print("=" * 78)
    baseline_mae = total_mae["baseline"] / total_n
    print(f"baseline (current shipped {len(BASELINE_TERMS)} terms): MAE = {baseline_mae:.4f}")
    for name in VARIANTS:
        if name == "baseline":
            continue
        mae = total_mae[name] / total_n
        delta = mae - baseline_mae
        print(f"{name:<20s}: MAE = {mae:.4f}  delta = {delta:+.4f}  "
              f"({'IMPROVEMENT from removing' if delta < 0 else 'WORSE without'})")

    print("\n" + "=" * 78)
    print("ROI CHECK (pooled bidirectional held-out, live shipped slope 0.1791)")
    print("=" * 78)
    for name in VARIANTS:
        pooled = pd.concat(pooled_scored[name], ignore_index=True)
        print(f"\n--- {name} ---")
        print(f"total held-out bets: {len(pooled):,}  [population avg price ${pooled['sp'].mean():.2f}]")
        for thr in EDGE_THRESHOLDS:
            report(pooled[pooled["edge_wpr"] >= thr], f"edge>={thr:.2f}")


if __name__ == "__main__":
    run()
