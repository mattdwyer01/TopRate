"""
wpr_summary_tab_backtest_fixed_beta.py - regenerates the Summary tab's
tier backtest numbers (the n=/ROI=/t= sublabels shown under each tier
pill) using ONE fixed beta throughout, instead of wpr_bet_selection_
leakfree_eval.py's per-direction refit (0.15 on H1-fit/H2-score, 0.20 on
H2-fit/H1-score).

WHY (Sep 2026, user request): "roi calculations should have been done on
1 beta, not multiple". Refitting beta separately per direction is the
textbook-correct way to keep a 2-fold walk-forward validation leak-free
(each half is scored using a beta that never saw that half's own data) -
using one beta fit on the FULL dataset and applying it to both halves
would leak information from each held-out half back into its own scoring,
which is exactly the flaw wpr_bet_selection_leakfree_eval.py itself was
built to fix (its predecessor used the shipped, globally-fit config and
got inflated numbers). But the Summary tab ships with ONE fixed beta
(the pipeline's own PRICE_BETA, currently 0.15) - the per-direction-refit
backtest doesn't quite answer "how would the strategy we actually run
have performed", it answers "how would a strategy that re-optimizes beta
every ~2 months have performed". This script answers the first question
directly: same leak-free 50/50 split, same per-half population lookups
(track_barrier/closing_merit/trainer_merit/jockey_merit, still fit
fit-half-only - those DO need the strict split, they directly encode
target), but beta held FIXED at FIXED_BETA for both directions instead
of refit.

ALSO regenerates on the NOW-FIXED model (wpr_projection.py's _shrink()
NaN-to-cap bug, fixed Sep 2026 the same day) - the numbers currently
shown in the Summary tab were computed before that fix shipped, on a
model that silently mis-scored ~3% of _shrink() calls. This run reflects
the corrected model.

Only the WPR-alone variant is computed (edge_wpr) - the pfm_score/
trainer/jockey blend variants (edge_a/edge_b) in the original eval were
superseded by the WPR-alone decision (see wpr_projection.py's
compute_edge_scores docstring) and aren't relevant to what the Summary
tab actually ships.

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np
import pandas as pd

import wpr_projection as wpr
from wpr_own_pace_backtest import add_base, add_track_barrier, merge_won_by_horse_date
from wpr_trainer_jockey_adj_strike_eval import FORM_CSV, merge_trainer_jockey_by_horse_date, \
    add_closing_merit, fit_bucket_lookup, apply_bucket
from wpr_bet_selection_post_retrain import merge_price_pfm, report

FIXED_BETA = 0.15  # the pipeline's own shipped PRICE_BETA
SUMMARY_TAB_THRESHOLDS = [0.05, 0.10, 0.20]  # High Volume / Mid / Value
PRICE_CAP = 26.0


def _edge_from_score(frame, score_col):
    e = np.exp(frame[score_col] - frame.groupby("race_id")[score_col].transform("max"))
    p = e / frame.groupby("race_id")[score_col].transform(lambda s: np.exp(s - s.max()).sum())
    p_mkt = (1.0 / frame["sp"]) / frame.groupby("race_id")["sp"].transform(lambda s: (1.0 / s).sum())
    return p - p_mkt


def fit_and_score(fit_half, held_out):
    """Fits population artifacts on fit_half ONLY (same as the original
    leak-free eval); beta is FIXED, not refit."""
    add_track_barrier(fit_half, [fit_half, held_out])
    add_closing_merit([fit_half, held_out], fit_half["date"].max())
    edges_t, lookup_t = fit_bucket_lookup(fit_half, "trainer_win_pct_365d")
    edges_j, lookup_j = fit_bucket_lookup(fit_half, "jockey_win_pct_90d")
    for f in (fit_half, held_out):
        apply_bucket(f, "trainer_win_pct_365d", edges_t, lookup_t, "trainer_merit")
        apply_bucket(f, "jockey_win_pct_90d", edges_j, lookup_j, "jockey_merit")
        f["wprp_proj"] = f["_base"].to_numpy() + wpr._cap_adj_sum(
            f[wpr.ADJ_TERMS].to_numpy()).sum(axis=1) * wpr._CALIB_ADJ_SLOPE

    held_out = held_out.copy()
    held_out["score_wpr"] = FIXED_BETA * held_out["wprp_proj"]
    held_out["edge_wpr"] = _edge_from_score(held_out, "score_wpr")
    return held_out


def run():
    print("Rebuilding training frame...")
    full = wpr.build_training_frame(FORM_CSV, verbose=True, n_jobs=-1)
    full["date"] = pd.to_datetime(full["date"])

    print("\nMerging result, trainer/jockey win-rate, price and pfm_score "
          "from toprate_runners.csv by (horse, date)...")
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
    full["used_sp_fallback"] = sp.isna() & sp_fallback.notna()
    full["sp"] = sp.fillna(sp_fallback)
    full = full.dropna(subset=["sp"])
    full = full[full["sp"] > 1.0]
    print(f"\nScoped rows: {len(full):,}")

    mid = full["date"].quantile(0.5)
    h1, h2 = full[full["date"] < mid].copy(), full[full["date"] >= mid].copy()
    print(f"H1: {len(h1):,} rows (< {mid.date()}), H2: {len(h2):,} rows (>= {mid.date()})")

    print(f"\nFitting on H1, scoring held-out H2 (beta fixed at {FIXED_BETA})...")
    h2_scored = fit_and_score(h1.copy(), h2.copy())
    print(f"Fitting on H2, scoring held-out H1 (beta fixed at {FIXED_BETA})...")
    h1_scored = fit_and_score(h2.copy(), h1.copy())

    pooled = pd.concat([h1_scored, h2_scored], ignore_index=True)
    print(f"\nPooled leak-free held-out set: {len(pooled):,} rows "
          f"(every row scored using ONLY the other half's fit, beta fixed at {FIXED_BETA} throughout)")

    print(f"\n{'='*78}\nSummary tab tier numbers, single fixed beta={FIXED_BETA}, price<=${PRICE_CAP:.0f}\n{'='*78}")
    for thr in SUMMARY_TAB_THRESHOLDS:
        sub = pooled[(pooled["edge_wpr"] >= thr) & (pooled["sp"] <= PRICE_CAP)]
        report(sub, f"edge>={thr:.2f}, price<=${PRICE_CAP:.0f}")

    print("\nSame multiple-comparisons caveat as the other bet-selection scripts: treat any")
    print("row here as a hypothesis for a future walk-forward period, not a result to ship blindly.")


if __name__ == "__main__":
    run()
