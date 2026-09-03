"""
wpr_signal_watch_daily_pnl.py - day-by-day P&L for the Signal Watch rule
(edge>=0.05, price<=$26, jockey_win_pct_90d>=16.9 or trainer_win_pct_365d
>=17.3) over the last 30 days, using the PROPER leak-corrected, K-fold-
consistent tiered-model edge values (wpr_roi_filter_search.build_pooled),
NOT the live dashboard's stale pre-backfill numbers.

Proportional staking, same convention as the live dashboard (toprate_
daily.py's RETURN_UNITS=4, 1 unit=$50): stake = RETURN_UNITS / price,
in dollars that's ($50 * 4) / price = $200 / price, targeting a $200
return on every winning bet regardless of price.

NO EM DASHES policy: hyphens only in this file.
"""
import sys

import numpy as np
import pandas as pd

from wpr_roi_filter_search import build_pooled

UNIT_DOLLARS = 50.0
RETURN_UNITS = 4
TARGET_RETURN = UNIT_DOLLARS * RETURN_UNITS  # $200

EDGE_THR = 0.05
PRICE_CAP = 26.0
JOCKEY_CUT = 16.9
TRAINER_CUT = 17.3


def run(full_period=False):
    print("Rebuilding pooled held-out scored data (NEW tiered base)...")
    pooled = build_pooled()

    today = pooled["date"].max()
    if full_period:
        window_start = pooled["date"].min() - pd.Timedelta(days=1)
    else:
        window_start = today - pd.Timedelta(days=30)
    window = pooled[(pooled["date"] > window_start) & (pooled["date"] <= today)].copy()
    print(f"Window: {window_start.date()} to {today.date()}  ({window['date'].nunique()} race days)")

    matches = window[
        (window["edge"] >= EDGE_THR)
        & (window["sp"] <= PRICE_CAP)
        & ((window["jockey_win_pct_90d"] >= JOCKEY_CUT) | (window["trainer_win_pct_365d"] >= TRAINER_CUT))
    ].copy()

    matches["stake"] = TARGET_RETURN / matches["sp"]
    matches["profit"] = np.where(matches["won"] == 1, matches["stake"] * (matches["sp"] - 1), -matches["stake"])

    print(f"\nTotal matches in window: {len(matches)}")
    print(f"Total staked: ${matches['stake'].sum():,.2f}")
    print(f"Total P&L: ${matches['profit'].sum():+,.2f}")
    print(f"Overall ROI: {matches['profit'].sum() / matches['stake'].sum() * 100:+.1f}%")
    print(f"Strike rate: {matches['won'].mean() * 100:.1f}%  (n={len(matches)})")

    print(f"\n{'='*90}\nDAY-BY-DAY P&L\n{'='*90}")
    print(f"  {'date':<12} {'n bets':>6} {'staked':>10} {'p&l':>12} {'cum p&l':>12} {'strike':>8}")
    daily = matches.groupby(matches["date"].dt.date).agg(
        n=("profit", "size"), staked=("stake", "sum"), pnl=("profit", "sum"), wins=("won", "sum")
    ).reset_index()
    # fill in every day in the window, even ones with zero matching bets, so
    # the day-by-day picture isn't silently missing gaps
    all_days = pd.date_range(window_start + pd.Timedelta(days=1), today, freq="D").date
    daily = daily.set_index("date").reindex(all_days, fill_value=0).rename_axis("date").reset_index()
    daily["cum_pnl"] = daily["pnl"].cumsum()
    for _, row in daily.iterrows():
        strike = f"{row['wins']/row['n']*100:.0f}%" if row["n"] > 0 else "-"
        print(f"  {str(row['date']):<12} {int(row['n']):>6} ${row['staked']:>9,.2f} "
              f"${row['pnl']:>+10,.2f} ${row['cum_pnl']:>+10,.2f} {strike:>8}")

    print(f"\nFinal cumulative P&L over {len(all_days)} days: ${daily['cum_pnl'].iloc[-1]:+,.2f}")
    print(f"Days with at least one bet: {(daily['n'] > 0).sum()} / {len(all_days)}")
    print(f"Days with positive P&L (of days with bets): {((daily['pnl'] > 0) & (daily['n'] > 0)).sum()} / {(daily['n'] > 0).sum()}")

    print("\nSame caveats as always: this is the K-fold-consistent MODELLING, not what the live dashboard "
          "actually served on those days (which is running stale pre-backfill projections - see the "
          "conversation). This answers 'what would proportional staking on the new model have returned', "
          "not 'what did the dashboard actually show you'.")


if __name__ == "__main__":
    run(full_period="--full" in sys.argv)
