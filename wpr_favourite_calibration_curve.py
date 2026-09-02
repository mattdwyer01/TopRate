"""
wpr_favourite_calibration_curve.py - full calibration curve (not just one
aggregate "market favourites" number) for WPR's beta=0.15 softmax price,
leak-free, on the NOW-FIXED model (post _shrink() NaN-cap fix, Sep 2026).

WHY (Sep 2026, user request): after the _shrink fix closed the aggregate
market-favourite gap (actual 30.5% vs model-implied 31.1%, -0.7pp), the
user still believes beta=0.15 is too harsh specifically on top-rated
runners. An aggregate "every market favourite" number can hide exactly
that: it lumps a barely-favourite (model_prob ~25%) in with a genuinely
dominant one (model_prob ~55%+) into one average, so a real miscalibration
concentrated at the top end wouldn't necessarily show up in the aggregate.
This buckets EVERY runner (not just each race's single favourite) by its
own model-implied probability, leak-free, and reports actual win rate per
bucket - a real reliability diagram, fine-grained at the top where the
question actually is.

METHOD: same leak-free 50/50 split and per-half population-lookup fits as
wpr_summary_tab_backtest_fixed_beta.py, beta held FIXED at FIXED_BETA
(the shipped 0.15) throughout - not refit per half, so this is measuring
calibration of the ACTUAL shipped number, not a re-optimized one.

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np
import pandas as pd

import wpr_projection as wpr
from wpr_own_pace_backtest import add_base, add_track_barrier, merge_won_by_horse_date
from wpr_trainer_jockey_adj_strike_eval import FORM_CSV, merge_trainer_jockey_by_horse_date, \
    add_closing_merit, fit_bucket_lookup, apply_bucket
from wpr_bet_selection_post_retrain import merge_price_pfm

FIXED_BETA = 0.15  # the pipeline's own shipped PRICE_BETA
# Fine-grained at the top end, where the disagreement actually is.
PROB_BUCKETS = [0.0, 0.05, 0.10, 0.15, 0.20, 0.25, 0.30, 0.35, 0.40, 0.50, 1.01]


def fit_and_score(fit_half, held_out):
    add_track_barrier(fit_half, [fit_half, held_out])
    add_closing_merit([fit_half, held_out], fit_half["date"].max())
    edges_t, lookup_t = fit_bucket_lookup(fit_half, "trainer_win_pct_365d")
    edges_j, lookup_j = fit_bucket_lookup(fit_half, "jockey_win_pct_90d")
    for f in (fit_half, held_out):
        apply_bucket(f, "trainer_win_pct_365d", edges_t, lookup_t, "trainer_merit")
        apply_bucket(f, "jockey_win_pct_90d", edges_j, lookup_j, "jockey_merit")
        f["wprp_proj"] = f["_base"].to_numpy() + wpr._cap_adj_sum(
            f[wpr.ADJ_TERMS].to_numpy()).sum(axis=1) * wpr._CALIB_ADJ_SLOPE
    return held_out.copy()


def add_model_prob(frame, beta):
    """Per-race softmax of wprp_proj at the FIXED beta - model_prob for
    EVERY runner, not just each race's favourite."""
    frame = frame.copy()

    def _prob(g):
        pv = g["wprp_proj"].to_numpy(dtype=float)
        e = np.exp(beta * (pv - pv.max()))
        return pd.Series(e / e.sum(), index=g.index)

    frame["model_prob"] = frame.groupby("race_id", group_keys=False).apply(_prob)
    return frame


def run():
    print("Rebuilding training frame...")
    full = wpr.build_training_frame(FORM_CSV, verbose=True, n_jobs=-1)
    full["date"] = pd.to_datetime(full["date"])

    print("\nMerging result, trainer/jockey win-rate, price from toprate_runners.csv...")
    full = merge_won_by_horse_date(full)
    full = merge_trainer_jockey_by_horse_date(full)
    full = merge_price_pfm(full)
    full = add_base(full)

    non_pop_terms = [t for t in wpr.ADJ_TERMS
                     if t not in ("track_barrier", "closing_merit", "trainer_merit", "jockey_merit")]
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

    print(f"\nFitting on H1, scoring held-out H2 (beta fixed at {FIXED_BETA})...")
    h2_scored = add_model_prob(fit_and_score(h1.copy(), h2.copy()), FIXED_BETA)
    print(f"Fitting on H2, scoring held-out H1 (beta fixed at {FIXED_BETA})...")
    h1_scored = add_model_prob(fit_and_score(h2.copy(), h1.copy()), FIXED_BETA)

    pooled = pd.concat([h1_scored, h2_scored], ignore_index=True)
    print(f"\nPooled leak-free held-out set: {len(pooled):,} runners "
          f"(every runner, not just each race's favourite; beta fixed at {FIXED_BETA})")

    print(f"\n{'='*78}\nFull calibration curve: every runner bucketed by its OWN model_prob\n{'='*78}")
    pooled["bucket"] = pd.cut(pooled["model_prob"], bins=PROB_BUCKETS, right=False)
    for b, g in pooled.groupby("bucket", observed=True):
        if len(g) < 20:
            print(f"  {b}: n={len(g)} (too small, skipped)")
            continue
        actual = g["won"].mean()
        implied = g["model_prob"].mean()
        gap = (actual - implied) * 100
        print(f"  model_prob {b}: n={len(g):6,d}  avg model_prob={implied*100:5.1f}%  "
              f"actual win rate={actual*100:5.1f}%  gap={gap:+5.1f}pp")

    print(f"\n{'='*78}\nSame curve, restricted to each race's OWN top-rated-by-WPR runner only\n{'='*78}")
    top_idx = pooled.groupby("race_id")["wprp_proj"].idxmax()
    tops = pooled.loc[top_idx].copy()
    tops["bucket"] = pd.cut(tops["model_prob"], bins=PROB_BUCKETS, right=False)
    for b, g in tops.groupby("bucket", observed=True):
        if len(g) < 20:
            print(f"  {b}: n={len(g)} (too small, skipped)")
            continue
        actual = g["won"].mean()
        implied = g["model_prob"].mean()
        gap = (actual - implied) * 100
        print(f"  model_prob {b}: n={len(g):6,d}  avg model_prob={implied*100:5.1f}%  "
              f"actual win rate={actual*100:5.1f}%  gap={gap:+5.1f}pp")

    print("\nSame multiple-comparisons caveat as the other bet-selection scripts: treat any")
    print("row here as a hypothesis for a future walk-forward period, not a result to ship blindly.")


if __name__ == "__main__":
    run()
