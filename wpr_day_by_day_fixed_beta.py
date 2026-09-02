"""
wpr_day_by_day_fixed_beta.py - day-by-day P&L for what the Summary tab's
High Volume tier (edge>=0.05, price<=$26) would have picked and returned,
using the leak-free fixed-beta=0.15 setup (see wpr_summary_tab_backtest_
fixed_beta.py for the full methodology writeup - same split, same
per-half population-lookup fits, beta held fixed throughout, on the
NOW-FIXED model post _shrink() NaN-cap fix).

Staking matches the Summary tab exactly: proportional "to return 4 units"
(stake = 4/price, win profit = 4-stake, loss profit = -stake) - see
SummaryTab.tsx's own RETURN_UNITS constant and docstring.

Caches the expensive merged pre-split frame to CACHE_PATH after building
it once - this exact ~15-20 min rebuild has now been repeated 4+ times
this session for different cuts of the same underlying leak-free
question. Cache is keyed on wpr_form_history.csv.gz's mtime, so it
self-invalidates the moment the form history actually changes (a daily
fetch, a backfill run) rather than silently going stale.

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
from wpr_bet_selection_post_retrain import merge_price_pfm

FIXED_BETA = 0.15
PRICE_CAP = 26.0
RETURN_UNITS = 4.0
EDGE_THRESHOLD = 0.05  # High Volume tier - the broadest, matches the default Summary tab
CACHE_PATH = Path("/tmp/wpr_full_training_frame_cache.pkl")


def _edge_from_score(frame, score_col):
    e = np.exp(frame[score_col] - frame.groupby("race_id")[score_col].transform("max"))
    p = e / frame.groupby("race_id")[score_col].transform(lambda s: np.exp(s - s.max()).sum())
    p_mkt = (1.0 / frame["sp"]) / frame.groupby("race_id")["sp"].transform(lambda s: (1.0 / s).sum())
    return p - p_mkt


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
    held_out = held_out.copy()
    held_out["score_wpr"] = FIXED_BETA * held_out["wprp_proj"]
    held_out["edge_wpr"] = _edge_from_score(held_out, "score_wpr")
    return held_out


def build_full():
    form_mtime = Path(FORM_CSV).stat().st_mtime
    if CACHE_PATH.exists():
        with open(CACHE_PATH, "rb") as fh:
            cached_mtime, full = pickle.load(fh)
        if cached_mtime == form_mtime:
            print(f"Loaded cached training frame ({len(full):,} rows) - skipping the ~15-20 min rebuild.")
            return full
        print("Cache is stale (form history changed since it was built) - rebuilding.")

    print("Rebuilding training frame (full history, this takes a while)...")
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

    with open(CACHE_PATH, "wb") as fh:
        pickle.dump((form_mtime, full), fh)
    print(f"Cached to {CACHE_PATH} for reuse by future runs (until wpr_form_history.csv.gz changes).")
    return full


def run():
    full = build_full()
    print(f"\nScoped rows: {len(full):,}")

    mid = full["date"].quantile(0.5)
    h1, h2 = full[full["date"] < mid].copy(), full[full["date"] >= mid].copy()
    print(f"H1: {len(h1):,} rows (< {mid.date()}), H2: {len(h2):,} rows (>= {mid.date()})")

    print(f"\nFitting on H1, scoring held-out H2 (beta fixed at {FIXED_BETA})...")
    h2_scored = fit_and_score(h1.copy(), h2.copy())
    print(f"Fitting on H2, scoring held-out H1 (beta fixed at {FIXED_BETA})...")
    h1_scored = fit_and_score(h2.copy(), h1.copy())
    pooled = pd.concat([h1_scored, h2_scored], ignore_index=True)

    picks = pooled[(pooled["edge_wpr"] >= EDGE_THRESHOLD) & (pooled["sp"] <= PRICE_CAP)].copy()
    picks["stake"] = RETURN_UNITS / picks["sp"]
    picks["profit"] = np.where(picks["won"] == 1, RETURN_UNITS - picks["stake"], -picks["stake"])

    print(f"\n{'='*90}\nDay-by-day: High Volume tier (edge>={EDGE_THRESHOLD:.2f}, price<=${PRICE_CAP:.0f}), "
          f"beta fixed at {FIXED_BETA}, proportional staking (to return {RETURN_UNITS:.0f}u)\n{'='*90}")
    print(f"{'Date':<12}{'Picks':>7}{'Wins':>6}{'Strike':>9}{'Staked':>9}{'P&L':>9}{'Cum P&L':>10}")

    daily = picks.groupby(picks["date"].dt.date).agg(
        picks=("won", "size"), wins=("won", "sum"), staked=("stake", "sum"), profit=("profit", "sum"),
    ).reset_index().sort_values("date")
    cum = 0.0
    for _, row in daily.iterrows():
        cum += row["profit"]
        strike = row["wins"] / row["picks"] * 100 if row["picks"] else 0.0
        print(f"{str(row['date']):<12}{int(row['picks']):>7}{int(row['wins']):>6}{strike:>8.1f}%"
              f"{row['staked']:>9.2f}{row['profit']:>+9.2f}{cum:>+10.2f}")

    n, wins, staked, profit = len(picks), int(picks["won"].sum()), picks["stake"].sum(), picks["profit"].sum()
    print(f"\n{'TOTAL':<12}{n:>7}{wins:>6}{wins/n*100:>8.1f}%{staked:>9.2f}{profit:>+9.2f}"
          f"{'':<10}  ROI={profit/staked*100:+.1f}%  ({daily['date'].min()} to {daily['date'].max()}, "
          f"{len(daily)} days with a qualifying pick)")

    print("\nSame multiple-comparisons caveat as the other bet-selection scripts: treat any")
    print("row here as a hypothesis for a future walk-forward period, not a result to ship blindly.")


if __name__ == "__main__":
    run()
