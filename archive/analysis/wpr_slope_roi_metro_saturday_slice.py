"""wpr_slope_roi_metro_saturday_slice.py - does the slope-removal ROI
finding (wpr_slope_roi_test.py) hold specifically on recent Saturday
Melbourne/Sydney metro racing (user request, Sep 2026) - the highest-
quality, most heavily bet racing, and a natural worry that a result
averaged across two years of every midweek/provincial/country meeting
might not transfer to the exact racing someone would actually bet.

Reuses the EXACT SAME leak-free bidirectional fit (wpr_slope_roi_test.py's
fit_and_score - same population-term fits, same beta refit per direction)
so nothing about the model or methodology changes; only the REPORTING
slice changes, to recent Saturday metro rows within that same pooled
held-out set.

USAGE
  python wpr_slope_roi_metro_saturday_slice.py

NO EM DASHES policy: hyphens only in this file.
"""
import pandas as pd

import wpr_projection as wpr
from wpr_bet_selection_post_retrain import report
from wpr_slope_roi_test import fit_and_score, EDGE_THRESHOLDS
import wpr_slope_roi_test as roi

# Melbourne + Sydney metro tracks. Substring-matched, case-insensitive,
# against the raw track name (toprate's own track strings - "Flemington",
# "Royal Randwick", "Rosehill Gardens", etc. - substring match covers the
# "Royal"/"Gardens" naming variants without needing an exact enumeration).
METRO_TRACKS = [
    "flemington", "caulfield", "moonee valley", "sandown",
    "randwick", "rosehill", "warwick farm", "canterbury",
]
N_RECENT_SATURDAYS = 8


def is_metro(track):
    t = str(track).lower()
    return any(m in t for m in METRO_TRACKS)


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
                        ["barrier", "field_size", "track", "cur_distance"])
    sp = pd.to_numeric(full["fixed_win_price"], errors="coerce")
    sp_fallback = pd.to_numeric(full["starting_price_sp"], errors="coerce")
    full["sp"] = sp.fillna(sp_fallback)
    full = full.dropna(subset=["sp"])
    full = full[full["sp"] > 1.0]
    print(f"Scoped rows: {len(full):,}")

    mid = full["date"].quantile(0.5)
    h1, h2 = full[full["date"] < mid].copy(), full[full["date"] >= mid].copy()
    print(f"H1: {len(h1):,} rows (< {mid.date()}), H2: {len(h2):,} rows (>= {mid.date()})")

    # Identify the N most recent Saturdays actually present in the data,
    # metro or not - "the last few Saturdays" means calendar-recent, not
    # just the Nth-most-recent metro Saturday (a track could have a Sydney
    # rain-affected abandonment some week, and that week should still count
    # as "recent", just contribute zero rows).
    saturdays = sorted(full.loc[full["date"].dt.dayofweek == 5, "date"].dt.date.unique())
    recent_saturdays = set(saturdays[-N_RECENT_SATURDAYS:])
    print(f"Recent Saturdays considered: {sorted(recent_saturdays)}")

    for slope, tag in [(0.1791, "shipped"), (1.00, "removed")]:
        print(f"\n{'#'*70}\n# SLOPE = {slope} ({tag})\n{'#'*70}")
        h2_scored = fit_and_score(h1.copy(), h2.copy(), h1["date"].max(), slope)
        h1_scored = fit_and_score(h2.copy(), h1.copy(), h2["date"].max(), slope)
        pooled = pd.concat([h1_scored, h2_scored], ignore_index=True)

        pooled["is_metro"] = pooled["track"].apply(is_metro)
        pooled["is_saturday"] = pooled["date"].dt.dayofweek == 5
        pooled["is_recent_sat"] = pooled["date"].dt.date.isin(recent_saturdays)

        metro_sat = pooled[pooled["is_metro"] & pooled["is_saturday"]]
        recent_metro_sat = pooled[pooled["is_metro"] & pooled["is_recent_sat"]]

        print(f"\n--- ALL Saturday Melb/Syd metro racing (n={len(metro_sat):,} runner-rows, "
              f"{metro_sat['race_id'].nunique():,} races) ---")
        for thr in EDGE_THRESHOLDS:
            report(metro_sat[metro_sat["edge_wpr"] >= thr], f"edge>={thr:.2f}")

        print(f"\n--- LAST {N_RECENT_SATURDAYS} SATURDAYS, Melb/Syd metro only "
              f"(n={len(recent_metro_sat):,} runner-rows, {recent_metro_sat['race_id'].nunique():,} races) ---")
        if recent_metro_sat["race_id"].nunique() < 20:
            print("  (very few races in this slice - treat any number below as directional only)")
        for thr in EDGE_THRESHOLDS:
            report(recent_metro_sat[recent_metro_sat["edge_wpr"] >= thr], f"edge>={thr:.2f}")


if __name__ == "__main__":
    run()
