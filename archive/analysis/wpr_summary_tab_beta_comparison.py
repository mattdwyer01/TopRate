"""
wpr_summary_tab_beta_comparison.py - user has their own Settings-panel
price-sharpness beta override set to 0.3, versus the pipeline's shipped
PRICE_BETA of 0.15 (see wpr_summary_tab_backtest_fixed_beta.py, FIXED_BETA
= 0.15). This answers "how would the Summary tab's own tier numbers (n
qualifying picks, ROI) look under 0.15 vs 0.3 vs 0.45" - same leak-free
50/50 split, same per-half population lookups (track_barrier/closing_
merit/trainer_merit/jockey_merit fit fit-half-only), beta held FIXED at
each candidate value for both directions (not refit per half - same
reasoning as wpr_summary_tab_backtest_fixed_beta.py: we want "how would
the strategy we actually run have performed" for a SPECIFIC beta, not
"how would re-optimizing beta every ~2 months have performed").

Higher beta sharpens the softmax over projected WPR within a race
(exp(beta*(proj-max))), which pushes the model's own implied probability
for the top-projected runner(s) further from a flat/market-like
distribution - this widens edges for the model's favourites (more of
them clear a given edge threshold, and by more), while shrinking or
flipping negative the edges of everything else in the race. So higher
beta should mechanically increase n (more edge>=X qualifiers) at looser
thresholds, but isn't guaranteed to improve ROI - a beta too aggressive
relative to how well-calibrated the model's own probabilities actually
are will just make the model overconfident, not more accurate.

Reuses wpr_summary_tab_backtest_fixed_beta.py's fit_and_score, parametrized
by beta instead of a single module-level FIXED_BETA. Reuses the cached
training frame (same cache other K-fold scripts in this repo share) to
avoid the ~15-20 min rebuild on repeat runs.

Staking convention: report()'s ROI is FLAT 1-unit-per-bet (profit = sp-1
on a win, -1 on a loss), the standard convention used throughout this
repo's backtest scripts - NOT the Summary tab UI's own proportional
"stake to return 4 units" convention (RETURN_UNITS in SummaryTab.tsx).
The relative ordering across beta values is what matters here, not an
exact match to the UI's displayed P&L figures.

NO EM DASHES policy: hyphens only in this file.
"""
import pickle
from pathlib import Path

import numpy as np
import pandas as pd

import wpr_projection as wpr
from wpr_own_pace_backtest import add_base, add_track_barrier, merge_won_by_horse_date
from wpr_trainer_jockey_adj_strike_eval import FORM_CSV, merge_trainer_jockey_by_horse_date, \
    add_closing_merit, fit_bucket_lookup, apply_bucket
from wpr_bet_selection_post_retrain import merge_price_pfm, report

CACHE_PATH = Path("/tmp/wpr_full_training_frame_cache.pkl")
BETA_VALUES = [0.15, 0.30, 0.45]
SUMMARY_TAB_THRESHOLDS = [0.05, 0.10, 0.20]  # High Volume / Mid / Value
TIER_NAMES = {0.05: "High Volume", 0.10: "Mid", 0.20: "Value"}
PRICE_CAP = 26.0


def build_full():
    form_mtime = Path(FORM_CSV).stat().st_mtime
    if CACHE_PATH.exists():
        with open(CACHE_PATH, "rb") as fh:
            cached_mtime, full = pickle.load(fh)
        if cached_mtime == form_mtime:
            print(f"Loaded cached training frame ({len(full):,} rows) - skipping the ~15-20 min rebuild.")
            full = full.drop(columns=["_base"], errors="ignore")
            return add_base(full)
        print("Cache is stale - rebuilding.")
    print("Rebuilding training frame (full history, this takes a while)...")
    full = wpr.build_training_frame(FORM_CSV, verbose=True, n_jobs=-1)
    full["date"] = pd.to_datetime(full["date"])
    full = merge_won_by_horse_date(full)
    full = merge_trainer_jockey_by_horse_date(full)
    full = merge_price_pfm(full)
    with open(CACHE_PATH, "wb") as fh:
        pickle.dump((form_mtime, full), fh)
    return add_base(full)


def _edge_from_score(frame, score_col):
    e = np.exp(frame[score_col] - frame.groupby("race_id")[score_col].transform("max"))
    p = e / frame.groupby("race_id")[score_col].transform(lambda s: np.exp(s - s.max()).sum())
    p_mkt = (1.0 / frame["sp"]) / frame.groupby("race_id")["sp"].transform(lambda s: (1.0 / s).sum())
    return p - p_mkt


def fit_pop_terms(fit_half, apply_frames):
    """Population lookups (track_barrier/closing_merit/trainer_merit/
    jockey_merit) fit on fit_half only, applied to every frame in
    apply_frames - shared across all beta values so this only needs
    doing once per direction, not once per (direction, beta) pair."""
    add_track_barrier(fit_half, apply_frames)
    add_closing_merit(apply_frames, fit_half["date"].max())
    edges_t, lookup_t = fit_bucket_lookup(fit_half, "trainer_win_pct_365d")
    edges_j, lookup_j = fit_bucket_lookup(fit_half, "jockey_win_pct_90d")
    for f in apply_frames:
        apply_bucket(f, "trainer_win_pct_365d", edges_t, lookup_t, "trainer_merit")
        apply_bucket(f, "jockey_win_pct_90d", edges_j, lookup_j, "jockey_merit")
        f["wprp_proj"] = f["_base"].to_numpy() + wpr._cap_adj_sum(
            f[wpr.ADJ_TERMS].to_numpy()).sum(axis=1) * wpr._CALIB_ADJ_SLOPE


def score_at_beta(held_out, beta):
    held_out = held_out.copy()
    held_out["score_wpr"] = beta * held_out["wprp_proj"]
    held_out["edge_wpr"] = _edge_from_score(held_out, "score_wpr")
    return held_out


def run():
    full = build_full()
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

    print("\nFitting population terms on H1 (applied to held-out H2)...")
    fit_pop_terms(h1, [h1, h2])
    print("Fitting population terms on H2 (applied to held-out H1)...")
    h1b, h2b = h1.copy(), h2.copy()
    fit_pop_terms(h2b, [h2b, h1b])
    # h1b/h2b now carry the H2-fit wprp_proj (for scoring H1 held out);
    # h1/h2 carry the H1-fit wprp_proj (for scoring H2 held out).

    for beta in BETA_VALUES:
        print(f"\n{'='*90}\nbeta = {beta}\n{'='*90}")
        h2_scored = score_at_beta(h2, beta)     # H1-fit, H2 held out
        h1_scored = score_at_beta(h1b, beta)    # H2-fit, H1 held out
        pooled = pd.concat([h1_scored, h2_scored], ignore_index=True)
        print(f"Pooled leak-free held-out set: {len(pooled):,} rows")
        for thr in SUMMARY_TAB_THRESHOLDS:
            sub = pooled[(pooled["edge_wpr"] >= thr) & (pooled["sp"] <= PRICE_CAP)]
            report(sub, f"{TIER_NAMES[thr]} (edge>={thr:.2f}), price<=${PRICE_CAP:.0f}")

    print("\nSame multiple-comparisons caveat as the other bet-selection scripts: treat any")
    print("row here as a hypothesis for a future walk-forward period, not a result to ship blindly.")


if __name__ == "__main__":
    run()
