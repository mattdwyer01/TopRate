"""
wpr_beta03_daily_state_summary.py - user's Settings-panel price-sharpness
beta is fixed at 0.3 (see wpr_summary_tab_beta_comparison.py for the
0.15/0.3/0.45 comparison that established this isn't a bad choice). This
answers two follow-up questions at that SAME beta: (1) a day-by-day
summary of qualifying bets/results, and (2) a breakdown by state
(NSW/VIC/QLD/SA/WA/TAS/ACT/NT).

Reuses the exact same leak-free 50/50 split and population-term fitting
as wpr_summary_tab_beta_comparison.py (track_barrier/closing_merit/
trainer_merit/jockey_merit fit fit-half-only, beta fixed for both
directions rather than refit) - see that file's docstring for why a
fixed beta answers "how would the strategy we actually run have
performed" rather than "how would re-optimizing beta have performed".

"Bets" here means every runner clearing the Summary tab's loosest
qualifying threshold (edge_wpr >= 0.05, the "High Volume" tier - the
union of all three tiers, since Mid/Value are strict subsets of it) with
price <= $26, same scoping as the Summary tab and the beta-comparison
script. Staking convention: FLAT 1-unit-per-bet (profit = sp-1 on a win,
-1 on a loss) - same convention as report() elsewhere in this repo, NOT
the Summary tab UI's own proportional "stake to return 4 units"
convention.

State comes from toprate_runners.csv (NOT part of build_training_frame's
own columns) - merged by race_id (already recovered via merge_won_by_
horse_date's toprate_runners.csv join), deduplicated to one row per
race_id since state is race-level, not runner-level.

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
from wpr_bet_selection_post_retrain import merge_price_pfm, RUNNERS_CSV

CACHE_PATH = Path("/tmp/wpr_full_training_frame_cache.pkl")
BETA = 0.30
EDGE_THRESHOLD = 0.05  # "High Volume" tier - the union of all Summary tab picks
PRICE_CAP = 26.0
DAILY_CSV_OUT = "/tmp/claude-0/-home-user-TopRate/37b9fca0-b163-5591-8763-1dcf84252930/scratchpad/beta03_daily_summary.csv"
STATE_CSV_OUT = "/tmp/claude-0/-home-user-TopRate/37b9fca0-b163-5591-8763-1dcf84252930/scratchpad/beta03_state_summary.csv"


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


def merge_state(D, runners_csv=RUNNERS_CSV):
    tr = pd.read_csv(runners_csv, dtype={"race_id": str}, low_memory=False,
                      usecols=["race_id", "state"])
    tr = tr.dropna(subset=["race_id", "state"]).drop_duplicates(subset="race_id", keep="first")
    D = D.copy()
    D["race_id"] = D["race_id"].astype(str)
    return D.merge(tr, on="race_id", how="left")


def _edge_from_score(frame, score_col):
    e = np.exp(frame[score_col] - frame.groupby("race_id")[score_col].transform("max"))
    p = e / frame.groupby("race_id")[score_col].transform(lambda s: np.exp(s - s.max()).sum())
    p_mkt = (1.0 / frame["sp"]) / frame.groupby("race_id")["sp"].transform(lambda s: (1.0 / s).sum())
    return p - p_mkt


def fit_pop_terms(fit_half, apply_frames):
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


def summarize(g):
    n = len(g)
    wins = int(g["won"].sum())
    profit = np.where(g["won"] == 1, g["sp"] - 1, -1.0)
    staked = float(n)
    total_profit = float(profit.sum())
    return pd.Series({
        "n_bets": n,
        "wins": wins,
        "strike_pct": wins / n * 100 if n else np.nan,
        "staked_u": staked,
        "profit_u": total_profit,
        "roi_pct": total_profit / staked * 100 if staked else np.nan,
    })


def run():
    full = build_full()
    non_pop_terms = [t for t in wpr.ADJ_TERMS
                     if t not in ("track_barrier", "closing_merit", "trainer_merit", "jockey_merit")]
    full = full.dropna(subset=["target", "_base", "career_avg"] + non_pop_terms +
                        ["barrier", "field_size", "track", "cur_distance"])
    sp = pd.to_numeric(full["fixed_win_price"], errors="coerce")
    sp_fallback = pd.to_numeric(full["starting_price_sp"], errors="coerce")
    full["sp"] = sp.fillna(sp_fallback)
    full = full.dropna(subset=["sp"])
    full = full[full["sp"] > 1.0]
    full = merge_state(full)
    print(f"\nScoped rows: {len(full):,}  (state missing for {full['state'].isna().sum():,})")

    mid = full["date"].quantile(0.5)
    h1, h2 = full[full["date"] < mid].copy(), full[full["date"] >= mid].copy()
    print(f"H1: {len(h1):,} rows (< {mid.date()}), H2: {len(h2):,} rows (>= {mid.date()})")

    print("\nFitting population terms on H1 (applied to held-out H2)...")
    fit_pop_terms(h1, [h1, h2])
    print("Fitting population terms on H2 (applied to held-out H1)...")
    h1b, h2b = h1.copy(), h2.copy()
    fit_pop_terms(h2b, [h2b, h1b])

    h2_scored = score_at_beta(h2, BETA)
    h1_scored = score_at_beta(h1b, BETA)
    pooled = pd.concat([h1_scored, h2_scored], ignore_index=True)
    print(f"\nPooled leak-free held-out set: {len(pooled):,} rows, beta={BETA}")

    bets = pooled[(pooled["edge_wpr"] >= EDGE_THRESHOLD) & (pooled["sp"] <= PRICE_CAP)].copy()
    bets["date"] = pd.to_datetime(bets["date"])
    print(f"Qualifying bets (edge>={EDGE_THRESHOLD}, price<=${PRICE_CAP:.0f}): {len(bets):,}")
    print(f"Date range: {bets['date'].min().date()} to {bets['date'].max().date()}")

    daily = bets.groupby(bets["date"].dt.date).apply(summarize, include_groups=False).reset_index()
    daily = daily.rename(columns={"date": "date"}).sort_values("date")
    daily.to_csv(DAILY_CSV_OUT, index=False)
    print(f"\nDaily summary written to {DAILY_CSV_OUT} ({len(daily)} days)")

    print(f"\n{'='*90}\nDAILY SUMMARY (beta={BETA}, edge>={EDGE_THRESHOLD}, price<=${PRICE_CAP:.0f})\n{'='*90}")
    print(daily.to_string(index=False, formatters={
        "strike_pct": "{:.1f}%".format, "roi_pct": "{:+.1f}%".format,
        "staked_u": "{:.0f}u".format, "profit_u": "{:+.2f}u".format,
    }))

    monthly = bets.groupby(bets["date"].dt.to_period("M")).apply(summarize, include_groups=False).reset_index()
    monthly = monthly.rename(columns={"date": "month"})
    print(f"\n{'='*90}\nMONTHLY ROLLUP\n{'='*90}")
    print(monthly.to_string(index=False, formatters={
        "strike_pct": "{:.1f}%".format, "roi_pct": "{:+.1f}%".format,
        "staked_u": "{:.0f}u".format, "profit_u": "{:+.2f}u".format,
    }))

    state_summary = bets.groupby("state", dropna=False).apply(summarize, include_groups=False).reset_index()
    state_summary = state_summary.sort_values("n_bets", ascending=False)
    state_summary.to_csv(STATE_CSV_OUT, index=False)
    print(f"\n{'='*90}\nBREAKDOWN BY STATE (beta={BETA}, edge>={EDGE_THRESHOLD}, price<=${PRICE_CAP:.0f})\n{'='*90}")
    print(state_summary.to_string(index=False, formatters={
        "strike_pct": "{:.1f}%".format, "roi_pct": "{:+.1f}%".format,
        "staked_u": "{:.0f}u".format, "profit_u": "{:+.2f}u".format,
    }))
    print(f"State summary written to {STATE_CSV_OUT}")

    print("\nSame multiple-comparisons caveat as the other bet-selection scripts: treat this")
    print("as a hypothesis for a future walk-forward period, not a result to ship blindly.")


if __name__ == "__main__":
    run()
