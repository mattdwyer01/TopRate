"""wpr_slope_roi_first_up_slice.py - does the slope-removal ROI finding
(wpr_slope_roi_test.py: removing _CALIB_ADJ_SLOPE's shrinkage hurts MAE
but improves strike rate/ROI/t-stats on the general population) hold
specifically for first-up/long-spell runners (user request, Sep 2026)?

MOTIVATION: a point-accuracy review of Flemington 12 Sept, then the full
~5-month toprate_runners.csv history, found first-up runners (60+ day
gap since last run, real debuts excluded) carry a mean miss (wprp_proj -
wpr_actual) of +3.92 vs +1.94 for the rest of the field (Welch t=9.6,
p<0.0001), growing further with spell length (up to +6.81 at 365+
days) - i.e. the SAME "raw/uncalibrated base runs hot" signature the
slope-removal decision already knowingly accepted for the general
population, just larger in this higher-variance subgroup. The open
question the point-accuracy check alone cannot answer: does slope=1.0
(removed, shipped) still win on ROI/strike-rate for THIS subgroup
specifically, or does the subgroup's larger raw bias translate into
worse betting performance once no shrinkage is reining it in?

Reuses the EXACT SAME leak-free bidirectional fit (wpr_slope_roi_test.py's
fit_and_score - same population-term fits, same beta refit per
direction, same edge-from-WPR-price scoring already validated in
calibrate_edge_score.py) so nothing about the model or methodology
changes; only the REPORTING slice changes, to first-up / long-spell rows
within that same pooled held-out set. first_up/days_since are read
directly from build_training_frame's own output (project_race's
already-debut-safe computation - see wpr_projection.py's days_since/
runs_this_camp Aug 2026 bug-fix comment), not recomputed here.

USAGE
  python wpr_slope_roi_first_up_slice.py

NO EM DASHES policy: hyphens only in this file.
"""
import pandas as pd

import wpr_projection as wpr
from wpr_bet_selection_post_retrain import report
from wpr_slope_roi_test import fit_and_score, EDGE_THRESHOLDS
import wpr_slope_roi_test as roi

LONG_SPELL_DAYS = 180


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

    non_pop_terms = [t for t in wpr.ADJ_TERMS
                     if t not in ("track_barrier", "closing_merit", "trainer_merit", "jockey_merit", "pace_shape")]
    full = full.dropna(subset=["target", "_base", "career_avg"] + non_pop_terms +
                        ["barrier", "field_size", "track", "cur_distance", "first_up", "days_since"])
    sp = pd.to_numeric(full["fixed_win_price"], errors="coerce")
    sp_fallback = pd.to_numeric(full["starting_price_sp"], errors="coerce")
    full["sp"] = sp.fillna(sp_fallback)
    full = full.dropna(subset=["sp"])
    full = full[full["sp"] > 1.0]
    print(f"Scoped rows: {len(full):,}")
    print(f"  first-up (raw feature, 60+ day gap): {(full['first_up']==1).sum():,}")
    print(f"  long-spell (180+ days since last run): {(full['days_since']>=LONG_SPELL_DAYS).sum():,}")

    mid = full["date"].quantile(0.5)
    h1, h2 = full[full["date"] < mid].copy(), full[full["date"] >= mid].copy()
    print(f"H1: {len(h1):,} rows (< {mid.date()}), H2: {len(h2):,} rows (>= {mid.date()})")

    for slope, tag in [(0.1791, "shipped"), (1.00, "removed")]:
        print(f"\n{'#'*70}\n# SLOPE = {slope} ({tag})\n{'#'*70}")
        h2_scored = fit_and_score(h1.copy(), h2.copy(), h1["date"].max(), slope)
        h1_scored = fit_and_score(h2.copy(), h1.copy(), h2["date"].max(), slope)
        pooled = pd.concat([h1_scored, h2_scored], ignore_index=True)

        first_up = pooled[pooled["first_up"] == 1]
        long_spell = pooled[pooled["days_since"] >= LONG_SPELL_DAYS]
        rest = pooled[pooled["first_up"] != 1]

        print(f"\n--- FIRST-UP runners (n={len(first_up):,} runner-rows, "
              f"{first_up['race_id'].nunique():,} races) ---")
        for thr in EDGE_THRESHOLDS:
            report(first_up[first_up["edge_wpr"] >= thr], f"edge>={thr:.2f}")

        print(f"\n--- LONG-SPELL runners (180+ days, n={len(long_spell):,} runner-rows, "
              f"{long_spell['race_id'].nunique():,} races) ---")
        for thr in EDGE_THRESHOLDS:
            report(long_spell[long_spell["edge_wpr"] >= thr], f"edge>={thr:.2f}")

        print(f"\n--- REST of field (not first-up, n={len(rest):,} runner-rows, for comparison) ---")
        for thr in EDGE_THRESHOLDS:
            report(rest[rest["edge_wpr"] >= thr], f"edge>={thr:.2f}")


if __name__ == "__main__":
    run()
