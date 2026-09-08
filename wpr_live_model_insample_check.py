"""wpr_live_model_insample_check.py - "what would the ROI be if you ran
this on the current dashboard" (user request, Sep 2026). Applies the
ACTUAL currently-shipped model (wpr_models/, no refitting) and its actual
beta to the full historical scoped dataset, using the real project_race()
formula (per-race demeaning included).

IMPORTANT: this is NOT a fair held-out test - the current live model was
trained on most of this same historical data, so this necessarily shows
an optimistic, in-sample-biased number, not a real estimate of future
performance. It answers a different, narrower question ("what does the
live model say about history it has already seen") than the walk-forward
test (wpr_walkforward_shipped_roi_test.py) does. Reported side by side
with that comparison made explicit, not as a competing "real" estimate.

USAGE
  python wpr_live_model_insample_check.py

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np
import pandas as pd
import joblib

import wpr_projection as wpr
from wpr_own_pace_backtest import add_base, merge_won_by_horse_date
from wpr_trainer_jockey_adj_strike_eval import FORM_CSV, merge_trainer_jockey_by_horse_date
from wpr_bet_selection_post_retrain import merge_price_pfm, report
from wpr_bet_selection_leakfree_eval import _edge_from_score

EDGE_THRESHOLDS = [0.0, 0.02, 0.04, 0.06, 0.08, 0.10, 0.13, 0.15, 0.20]


def run():
    wpr._load_models()
    beta = wpr._CFG.get("beta", 0.4)
    pop = wpr._POP_ADJ_MODELS or {}
    print(f"Live beta: {beta}")
    print(f"Live pop_adj_models present: {sorted(pop.keys())}")

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
    full["used_sp_fallback"] = sp.isna() & sp_fallback.notna()
    full["sp"] = sp.fillna(sp_fallback)
    full = full.dropna(subset=["sp"])
    full = full[full["sp"] > 1.0]
    print(f"Scoped rows: {len(full):,}  fallback-to-SP: {full['used_sp_fallback'].mean()*100:.1f}%")

    print("Applying LIVE (already-fit, not refit) population models...")
    tb_model = pop.get("track_barrier")
    tb_code_map = pop.get("track_code_map") or {}
    full["track_barrier"] = [
        wpr._track_barrier_term(trk, dist, bar, fs, tb_code_map, tb_model)
        for trk, dist, bar, fs in zip(full["track"], full["cur_distance"], full["barrier"], full["field_size"])
    ]
    trm_model = pop.get("trainer_merit")
    jm_model = pop.get("jockey_merit")
    full["trainer_merit"] = [
        wpr._merit_term(v, fs, trm_model, wpr._TRAINER_MERIT_FEATURES)
        for v, fs in zip(full["trainer_win_pct_365d"], full["field_size"])
    ]
    full["jockey_merit"] = [
        wpr._merit_term(v, fs, jm_model, wpr._JOCKEY_MERIT_FEATURES)
        for v, fs in zip(full["jockey_win_pct_90d"], full["field_size"])
    ]
    pace_baseline_lookup = wpr._CFG.get("pace_baseline_lookup") or {}
    cm_model = pop.get("closing_merit")
    full["closing_merit"] = [
        wpr._closing_merit_term(pairs, pace_baseline_lookup, fs, cm_model)
        for pairs, fs in zip(full["closing_pairs"], full["field_size"])
    ]
    # per-race demeaning - must match project_race() exactly (the bug fix)
    for term in ("track_barrier", "closing_merit", "trainer_merit", "jockey_merit"):
        full[term] = full[term] - full.groupby("race_id")[term].transform("mean")

    print("Applying LIVE pace_shape model...")
    since = (full["date"].max() - pd.Timedelta(days=365)).strftime("%Y-%m-%d")
    race_id_to_score = wpr._build_pace_shape_race_scores(since)
    _name_map, _ = wpr._load_trainer_jockey_by_horse_date(FORM_CSV)
    full["horse_lc"] = full["horse_id"].map(_name_map).astype(str).str.lower()
    settle_lookup = wpr._build_pace_shape_settle_lookup(since)
    full["pace_score"] = full["race_id"].map(race_id_to_score)
    full["predicted_rel_settle"] = [settle_lookup.get((h, d)) for h, d in zip(full["horse_lc"], full["date"])]
    pace_model = joblib.load("wpr_models/pace_shape.joblib")
    full["pace_shape"] = [
        wpr._pace_shape_term(ps, prs, fs, pace_model)
        for ps, prs, fs in zip(full["pace_score"], full["predicted_rel_settle"], full["field_size"])
    ]

    full["wprp_proj"] = full["_base"].to_numpy() + wpr._cap_adj_sum(full[wpr.ADJ_TERMS].to_numpy()).sum(axis=1)
    full["score_wpr"] = beta * full["wprp_proj"]
    full["edge_wpr"] = _edge_from_score(full, "score_wpr")

    print(f"\n{'='*70}\nIN-SAMPLE: current live model + live beta ({beta}), full history "
          f"({full['date'].min().date()} to {full['date'].max().date()})\n{'='*70}")
    print("WARNING: the live model was trained on most of this data - this is")
    print("an optimistic upper bound, NOT a held-out estimate. See the walk-")
    print("forward test (wpr_walkforward_shipped_roi_test.py) for the honest number.\n")
    print(f"total bets: {len(full):,}  [population avg price ${full['sp'].mean():.2f}]")
    for thr in EDGE_THRESHOLDS:
        report(full[full["edge_wpr"] >= thr], f"edge>={thr:.2f}")


if __name__ == "__main__":
    run()
