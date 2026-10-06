"""wpr_live_model_insample_monthly_check.py - is the pooled-positive
in-sample result (wpr_live_model_insample_check.py) hiding a genuine
recent decline, or is the walk-forward-vs-live-tracker mismatch purely a
simulation artifact? This applies the ACTUAL currently-shipped production
models (wpr._POP_ADJ_MODELS, loaded straight from wpr_models/ - NOT
independently refit, unlike wpr_walkforward_shipped_roi_test.py's fold
models) to the full historical scoped dataset, exactly as wpr_live_model_
insample_check.py does, but reports the result BROKEN DOWN BY MONTH
instead of pooled - if April-July are strongly positive and August-
September are negative even here (same live model, in-sample, real
production artifacts), that proves the recent negative result is a real
recent decline in this model's edge, not an artifact of the walk-forward
test's own fold-refitting differing from production.

Already confirmed separately (Sep 2026): toprate_runners.csv's persisted
wprp_proj for a sample date (2026-08-15) is bit-identical to a fresh
recompute via the real production compute_wpr_projection() - so staleness
of the backfilled historical data is ruled out as an explanation.

PRICE ONLY (follow-up instruction): never uses the old model_prob/
market_prob difference ("edge") - reports price_edge_pct = sp/blend_price
- 1 at both live beta candidates (0.15, 0.3) instead.

USAGE
  python wpr_live_model_insample_monthly_check.py

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np
import pandas as pd
import joblib

import wpr_projection as wpr
from wpr_own_pace_backtest import add_base, merge_won_by_horse_date
from wpr_trainer_jockey_adj_strike_eval import FORM_CSV, merge_trainer_jockey_by_horse_date
from wpr_bet_selection_post_retrain import merge_price_pfm

PRICE_EDGE_THRESHOLDS = [0.0, 0.10, 0.20, 0.30, 0.50]
BETAS_TO_TEST = [0.15, 0.3]


def blend_price_per_race(df, beta):
    out = np.full(len(df), np.nan)
    proj = df["wprp_proj"].to_numpy(dtype=float)
    for rid, idx in df.groupby("race_id").indices.items():
        idx = np.asarray(idx)
        pv = proj[idx]
        e = np.exp(beta * (pv - pv.max()))
        prob = e / e.sum()
        out[idx] = np.minimum(1.0 / prob, 999.0)
    return out


def roi_stats(sub):
    n = len(sub)
    if n < 20:
        return {"n": n, "strike": None, "roi": None, "t": None}
    profit = np.where(sub["won"] == 1, sub["sp"] - 1, -1.0)
    se = profit.std(ddof=1) / np.sqrt(n)
    t = float(profit.mean() / se) if se > 0 else float("nan")
    return {"n": n, "strike": round(float(sub["won"].mean() * 100), 2),
            "roi": round(float(profit.sum() / n * 100), 2), "t": round(t, 2)}


def print_row(label, stats):
    print(f"    {label:<16} n={stats['n']:>6}  strike={str(stats['strike']):>7}%  "
          f"ROI={str(stats['roi']):>8}%  t={str(stats['t']):>7}")


def run():
    wpr._load_models()
    pop = wpr._POP_ADJ_MODELS or {}
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
    full["sp"] = sp.fillna(sp_fallback)
    full = full.dropna(subset=["sp"])
    full = full[full["sp"] > 1.0]
    print(f"Scoped rows: {len(full):,}  date range {full['date'].min().date()} to {full['date'].max().date()}")

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
    full["month"] = full["date"].dt.to_period("M").astype(str)

    for beta in BETAS_TO_TEST:
        print(f"\n{'='*90}\nBETA = {beta}  (LIVE production models, IN-SAMPLE, price only)\n{'='*90}")
        full[f"blend_price_b{beta}"] = blend_price_per_race(full, beta)
        full[f"price_edge_pct_b{beta}"] = full["sp"] / full[f"blend_price_b{beta}"] - 1.0
        for month, g in full.groupby("month"):
            print(f"\n  --- {month} (n_races={g['race_id'].nunique()}) ---")
            for thr in PRICE_EDGE_THRESHOLDS:
                print_row(f"price_edge>={thr:.2f}", roi_stats(g[g[f"price_edge_pct_b{beta}"] >= thr]))
        print(f"\n  --- POOLED ALL MONTHS ---")
        for thr in PRICE_EDGE_THRESHOLDS:
            print_row(f"price_edge>={thr:.2f}", roi_stats(full[full[f"price_edge_pct_b{beta}"] >= thr]))


if __name__ == "__main__":
    run()
