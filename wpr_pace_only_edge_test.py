"""
wpr_pace_only_edge_test.py - tests whether an edge signal built from JUST
pace_shape (race-shape/settling-position, "does this horse get an easy
uncontested run or get buried wide/held up") finds better overlays than
the current all-10-terms-blended edge, at the same ROI adoption bar used
all night.

WHY THIS EXISTS (see chat, Sep 2026): a user question - "what if we
focused on fine-tuning the WPR rating around jockey/fitness/pace-position
and found bets from there, instead of deriving a price and comparing to
market" - led to a sharper, testable version: jockey quality and recent
fitness are things every serious punter already prices into the market
(low genuine edge likely available there), but a horse's exact pace
scenario/settling position (will it get an easy lead, or get caught
three-wide and buried) requires real pre-race pace-mapping work that
casual market money likely under-does. If that's true, an edge signal
built mostly from pace_shape specifically (rather than the current blend
of all 10 ADJ_TERMS, which mixes in the easier-to-price trainer_merit/
jockey_merit/track_barrier signals) should find a CLEANER, stronger
overlay signal than the current all-terms edge.

TWO VARIANTS COMPARED (both against the same held-out real market
prices):
  1. FULL (current live): proj = base + sum(all 10 ADJ_TERMS)
  2. PACE-ONLY: proj = base + pace_shape (own-history terms own_first_up/
     own_second_up/own_long_spell deliberately EXCLUDED too, not just the
     population terms - this isolates the "pace scenario specifically"
     hypothesis as cleanly as possible, not just "own-form minus
     jockey/trainer/barrier")
Both use the SAME shipped softmax beta (0.15) and the SAME per-direction
leak-free fitting for track_barrier/closing_merit/trainer_merit/
jockey_merit/pop_distance/pop_going (fit once per direction so the FULL
variant is scored fairly against the live architecture - the pace-only
variant doesn't need any of those terms, only pace_shape and base, but
they still need to be fit so the FULL baseline is a fair, real
comparison, not a strawman).

NO slope multiplier on the adjustment sum (matches live: "adjustment is
now added to base UNSHRUNK", see wpr_projection.py's "Serving-time
calibration - REMOVED" history) - this session found and fixed a real
bug earlier tonight where several scripts incorrectly multiplied by a
stale pre-removal slope constant; this script does not repeat that.

NO EM DASHES policy: hyphens only.
"""
import numpy as np
import pandas as pd

import wpr_projection as wpr
from wpr_own_pace_backtest import add_base, merge_won_by_horse_date
from wpr_bet_selection_post_retrain import report, merge_price_pfm
from wpr_slope_roi_test import EDGE_THRESHOLDS
import wpr_slope_roi_test as roi

SHIPPED_BETA = 0.15
FORM_CSV = "wpr_form_history.csv.gz"


def fit_other_pop_terms(fit_half, held_out, fit_cutoff):
    from wpr_own_pace_backtest import add_track_barrier
    from wpr_trainer_jockey_adj_strike_eval import add_closing_merit, fit_bucket_lookup, apply_bucket
    from wpr_slope_roi_first_up_slice import add_pop_distance_going

    add_track_barrier(fit_half, [fit_half, held_out])
    add_closing_merit([fit_half, held_out], fit_cutoff)
    edges_t, lookup_t = fit_bucket_lookup(fit_half, "trainer_win_pct_365d")
    edges_j, lookup_j = fit_bucket_lookup(fit_half, "jockey_win_pct_90d")
    for f in (fit_half, held_out):
        apply_bucket(f, "trainer_win_pct_365d", edges_t, lookup_t, "trainer_merit")
        apply_bucket(f, "jockey_win_pct_90d", edges_j, lookup_j, "jockey_merit")
    add_pop_distance_going(fit_half, [fit_half, held_out])


def build_pace_shape_once(full):
    import joblib
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


def score_variant(held_out, terms):
    """proj = base + sum(terms), NO slope (matches live), softmax at the
    shipped beta, edge vs real market price."""
    adj = wpr._cap_adj_sum(held_out[terms].fillna(0.0).to_numpy()).sum(axis=1) if len(terms) > 1 else \
          held_out[terms[0]].fillna(0.0).to_numpy()
    proj = held_out["_base"].to_numpy() + adj
    scored = held_out.copy()
    scored["wprp_proj"] = proj
    # softmax win prob at the shipped beta, race-scoped
    model_prob = pd.Series(np.nan, index=scored.index)
    for rid, g in scored.groupby("race_id"):
        if len(g) < 2:
            continue
        pv = g["wprp_proj"].to_numpy(dtype=float)
        e = np.exp(SHIPPED_BETA * (pv - pv.max()))
        model_prob.loc[g.index] = e / e.sum()
    scored["score_wpr"] = model_prob
    scored["mkt_prob"] = scored.groupby("race_id")["sp"].transform(lambda x: (1 / x) / (1 / x).sum())
    scored["edge_wpr"] = scored["score_wpr"] - scored["mkt_prob"]
    return scored.dropna(subset=["edge_wpr"])


def run():
    print("Rebuilding training frame...")
    full = wpr.build_training_frame(FORM_CSV, verbose=True, n_jobs=-1)
    full["date"] = pd.to_datetime(full["date"])

    from wpr_trainer_jockey_adj_strike_eval import merge_trainer_jockey_by_horse_date
    full = merge_won_by_horse_date(full)
    full = merge_trainer_jockey_by_horse_date(full)
    full = merge_price_pfm(full)
    full = add_base(full)

    print("  building pace_shape (shipped model, fixed input)...")
    build_pace_shape_once(full)

    own_history_terms = ["own_first_up", "own_second_up", "own_long_spell"]
    full = full.dropna(subset=["target", "_base", "career_avg"] + own_history_terms +
                        ["pace_shape", "barrier", "field_size", "track", "cur_distance", "race_id"])
    sp = pd.to_numeric(full["fixed_win_price"], errors="coerce")
    sp_fb = pd.to_numeric(full["starting_price_sp"], errors="coerce")
    full["sp"] = sp.fillna(sp_fb)
    full = full.dropna(subset=["sp"])
    full = full[full["sp"] > 1.0]
    print(f"Scoped rows: {len(full):,} ({full['race_id'].nunique():,} races)")

    mid = full["date"].quantile(0.5)
    h1, h2 = full[full["date"] < mid].copy(), full[full["date"] >= mid].copy()
    print(f"H1: {len(h1):,} rows (< {mid.date()}), H2: {len(h2):,} rows (>= {mid.date()})")

    FULL_TERMS = list(wpr.ADJ_TERMS)
    PACE_ONLY_TERMS = ["pace_shape"]

    pooled = {"full": [], "pace_only": []}
    for fit_h, held_h, label in [(h1, h2, "H1->H2"), (h2, h1, "H2->H1")]:
        fit_half, held_out = fit_h.copy(), held_h.copy()
        print(f"\n{label}: fitting other population terms...")
        fit_other_pop_terms(fit_half, held_out, fit_half["date"].max())

        for name, terms in [("full", FULL_TERMS), ("pace_only", PACE_ONLY_TERMS)]:
            scored = score_variant(held_out, terms)
            pooled[name].append(scored)
            print(f"  {label} {name}: n={len(scored):,}")

    print("\n" + "=" * 78)
    print("ROI CHECK: FULL (all 10 terms, current live) vs PACE-ONLY edge")
    print("=" * 78)
    for name in ("full", "pace_only"):
        p = pd.concat(pooled[name], ignore_index=True)
        print(f"\n--- {name} ---")
        print(f"total held-out bets: {len(p):,}  [population avg price ${p['sp'].mean():.2f}]")
        for thr in EDGE_THRESHOLDS:
            report(p[p["edge_wpr"] >= thr], f"edge>={thr:.2f}")


if __name__ == "__main__":
    run()
