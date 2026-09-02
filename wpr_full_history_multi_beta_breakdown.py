"""
wpr_full_history_multi_beta_breakdown.py - sweeps beta=[0.15, 0.30, 0.45]
on top of the REAL wpr.project_race() projections (not the reconstruction
- see wpr_full_history_current_model_breakdown.py's docstring for why
that distinction matters: the reconstruction disagreed sharply with the
live dashboard, this script and that one both call the real function).

Computing wprp_proj across the full 2026-04-26 to 2026-09-01 history is
the expensive part (~15-20 min); the edge/tier computation from a fixed
set of projections is cheap (a per-race softmax). So this computes
projections ONCE, then sweeps BETA_GRID against that same set, instead
of re-running the projection pass once per beta.

Reuses wpr_full_history_current_model_breakdown.py's exact projection
logic (project_date/load_form_history, verbatim reimplementation of
toprate_daily.compute_wpr_projection()'s per-race construction) via
import, so there is exactly one place that logic lives.

NO EM DASHES policy: hyphens only in this file.
"""
import time

import numpy as np
import pandas as pd

from wpr_full_history_current_model_breakdown import (
    RUNNERS_CSV, load_form_history, project_date, summarize, print_table,
    QUALITY_BINS, QUALITY_LABELS, RETURN_UNITS, PRICE_CAP, EDGE_THRESHOLD,
)

BETA_GRID = [0.15, 0.30, 0.45]
SCRATCH_DIR = "/tmp/claude-0/-home-user-TopRate/37b9fca0-b163-5591-8763-1dcf84252930/scratchpad"


def edge_for_race(g, beta):
    proj = g["proj"].to_numpy(dtype=float)
    price = g["price"].to_numpy(dtype=float)
    e = np.exp(beta * (proj - proj.max()))
    model_prob = e / e.sum()
    inv = 1.0 / price
    mkt_prob = inv / inv.sum()
    return pd.Series(model_prob - mkt_prob, index=g.index)


def run():
    print("Reading toprate_runners.csv...")
    runners = pd.read_csv(RUNNERS_CSV, low_memory=False,
                           dtype={"race_id": str, "horse": str, "venue": str, "state": str})
    runners["date"] = pd.to_datetime(runners["date"], errors="coerce")
    runners["resulted"] = pd.to_numeric(runners["resulted"], errors="coerce")
    runners = runners[runners["resulted"] == 1].copy()
    runners = runners.dropna(subset=["date", "race_id"])
    dates = sorted(runners["date"].dt.date.unique())
    print(f"Resulted rows: {len(runners):,} across {len(dates)} dates "
          f"({dates[0]} to {dates[-1]})")

    form_by_horse, trial_by_horse = load_form_history()

    print("\nProjecting every historical day with wpr.project_race() (ONE pass, shared across all betas)...")
    t0 = time.time()
    proj_col = pd.Series(index=runners.index, dtype=float)
    has_proj_col = pd.Series(False, index=runners.index)
    for di, d in enumerate(dates):
        day_df = runners[runners["date"].dt.date == d]
        result = project_date(day_df, pd.Timestamp(d), form_by_horse, trial_by_horse)
        for idx, r in result.items():
            has_proj_col.at[idx] = r["has_projection"]
            if r["has_projection"]:
                proj_col.at[idx] = r["projected_wpr"]
        if (di + 1) % 10 == 0 or di == len(dates) - 1:
            print(f"  ... {di+1}/{len(dates)} dates ({time.time()-t0:.0f}s elapsed)")

    runners["wprp_proj"] = proj_col
    runners["has_projection"] = has_proj_col
    print(f"\nTotal: {int(has_proj_col.sum()):,} / {len(runners):,} runners got a projection "
          f"in {time.time()-t0:.0f}s")

    bets_pool = runners[runners["has_projection"]].copy()
    sp = pd.to_numeric(bets_pool["fixed_win_price"], errors="coerce")
    sp_fallback = pd.to_numeric(bets_pool["starting_price_sp"], errors="coerce")
    bets_pool["price"] = sp.fillna(sp_fallback)
    bets_pool = bets_pool.dropna(subset=["price"])
    bets_pool = bets_pool[bets_pool["price"] > 1.0]
    bets_pool["won"] = pd.to_numeric(bets_pool["won"], errors="coerce").fillna(0).astype(int)
    bets_pool["proj"] = bets_pool["wprp_proj"]
    bets_pool["quality"] = pd.cut(bets_pool["prize_money"], bins=QUALITY_BINS, labels=QUALITY_LABELS)

    overall_summary = []
    for beta in BETA_GRID:
        print(f"\n{'#'*90}\nBETA = {beta}\n{'#'*90}")
        edges = bets_pool.groupby("race_id", group_keys=False).apply(lambda g: edge_for_race(g, beta))
        pool = bets_pool.copy()
        pool["edge"] = edges
        bets = pool[(pool["edge"] >= EDGE_THRESHOLD) & (pool["price"] <= PRICE_CAP)].copy()
        print(f"Qualifying bets (edge>={EDGE_THRESHOLD}, price<=${PRICE_CAP:.0f}): {len(bets):,}")

        tag = str(beta).replace(".", "")
        bets[["date", "venue", "race", "horse", "state", "quality", "price", "edge", "won"]].to_csv(
            f"{SCRATCH_DIR}/multibeta_{tag}_all_bets.csv", index=False)

        daily = bets.groupby(bets["date"].dt.date).apply(summarize, include_groups=False).reset_index()
        daily = daily.sort_values("date")
        daily.to_csv(f"{SCRATCH_DIR}/multibeta_{tag}_daily_summary.csv", index=False)

        monthly = bets.groupby(bets["date"].dt.to_period("M")).apply(summarize, include_groups=False).reset_index()
        monthly = monthly.rename(columns={"date": "month"})
        print_table(monthly, f"MONTHLY ROLLUP (real model, beta={beta})")

        state_summary = bets.groupby("state", dropna=False).apply(summarize, include_groups=False).reset_index()
        state_summary = state_summary.sort_values("n_bets", ascending=False)
        state_summary.to_csv(f"{SCRATCH_DIR}/multibeta_{tag}_state_summary.csv", index=False)
        print_table(state_summary, f"BREAKDOWN BY STATE (real model, beta={beta})")

        quality_summary = bets.groupby("quality", observed=True).apply(summarize, include_groups=False).reset_index()
        quality_summary = quality_summary.set_index("quality").reindex(QUALITY_LABELS).reset_index()
        quality_summary.to_csv(f"{SCRATCH_DIR}/multibeta_{tag}_quality_summary.csv", index=False)
        print_table(quality_summary, f"BREAKDOWN BY RACE QUALITY (real model, beta={beta})")

        total_staked = bets.apply(lambda r: RETURN_UNITS / r["price"], axis=1).sum()
        total_profit = bets.apply(
            lambda r: (RETURN_UNITS - RETURN_UNITS / r["price"]) if r["won"] == 1 else -(RETURN_UNITS / r["price"]),
            axis=1).sum()
        roi = total_profit / total_staked * 100 if total_staked else float("nan")
        strike = bets["won"].mean() * 100 if len(bets) else float("nan")
        print(f"\nOVERALL beta={beta}: n={len(bets):,}  strike={strike:.1f}%  staked={total_staked:.2f}u  "
              f"profit={total_profit:+.2f}u  ROI={roi:+.1f}%")
        overall_summary.append((beta, len(bets), strike, total_staked, total_profit, roi))

    print(f"\n{'='*90}\nSUMMARY ACROSS BETAS (real model, full history)\n{'='*90}")
    print(f"{'beta':>6}  {'n_bets':>8}  {'strike':>8}  {'staked':>10}  {'profit':>10}  {'ROI':>8}")
    for beta, n, strike, staked, profit, roi in overall_summary:
        print(f"{beta:>6}  {n:>8,}  {strike:>7.1f}%  {staked:>9.2f}u  {profit:>+9.2f}u  {roi:>+7.1f}%")

    print(f"\nAll CSVs written under {SCRATCH_DIR} (prefixed multibeta_<beta>_...)")


if __name__ == "__main__":
    run()
