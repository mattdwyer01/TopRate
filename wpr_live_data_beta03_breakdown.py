"""
wpr_live_data_beta03_breakdown.py - redo the daily/state/quality
breakdowns using the ACTUAL LIVE toprate_data.json payload (the exact
numbers the dashboard shows right now), not a reconstruction.

BACKGROUND (Sep 2026): wpr_beta03_daily_state_summary.py approximates
the model (base + capped_adj_sum*slope, population terms fit on a
leak-free 50/50 split) for aggregate hypothesis testing across full
history. Confirmed live it disagrees with the real dashboard on
specific days - e.g. 2026-08-30: the reconstruction said 26 bets/+36.8%
ROI, the real dashboard said 51 bets/-46.9% ROI. Investigating why
turned up two things:
  1. The reconstruction never included dist_edge_correction/first_up_
     trial_correction (both bypass _CALIB_ADJ_SLOPE, added directly in
     project_race()), and fits population terms on a leak-free split
     rather than the fixed, already-shipped constants the real model
     uses.
  2. Re-running wpr.project_race() directly (the real function) against
     toprate_runners.csv for 2026-08-30 with TODAY's code does NOT
     reproduce toprate_data.json's stored wpjp either (487/580 runners
     differed by 0.5-1.5 WPR points) - because compute_wpr_projection()
     only computes a day's projection ONCE, the first time that date is
     processed as "today" (see its own docstring: "Past runners keep
     whatever wprp_* values they already had"). So a historical day's
     stored wpjp reflects WHATEVER model version was live when the
     daily pipeline first fetched that race day, not today's code -
     recomputing it fresh is a different (also legitimate, but
     different) question from "what does the dashboard actually show".

This script answers the literal question: what does toprate_data.json
(the file the live dashboard fetches right now) actually contain, run
through the Summary tab's own edge/tier logic at beta=0.3. That means
trusting each race's stored wpjp exactly as-is, whatever model version
produced it - which is exactly what a user looking at the dashboard
today sees, mixed model vintage and all.

CAVEAT (important): toprate_data.json is windowed to the last ~30-45
days (TOPRATE_RACES_WINDOW_DAYS) and does NOT recompute past days'
projections when newer model code ships - so this covers a much
shorter and more recent span (2026-08-03 to 2026-09-01 resulted races)
than the ~5-month April-September range in the earlier reconstruction-
based breakdowns, and some of these days' underlying projections may
themselves predate this session's alpha=0.8/dist_edge/first-up-trial/
MIN_RUNS=1 changes (there is no way to tell which vintage a given day's
wpjp is from without re-deriving it, which is exactly the mismatch
above). Treat this as "what the dashboard currently shows", not "what
the current model would show if every day were freshly recomputed".

Edge computed exactly as SummaryTab.tsx's computeEffectiveEdges: per-race
softmax(beta*wpjp) for model_prob (only over active, non-scratched
runners that have a wpjp), market_prob from price (fx ?? sp ?? top), a
whole race skipped unless EVERY active runner has a wpjp (same
eligibility rule as collectPicks). Staking: proportional stake-to-
return-RETURN_UNITS, matching the dashboard's own convention.

NO EM DASHES policy: hyphens only in this file.
"""
import json
from pathlib import Path

import numpy as np
import pandas as pd

DATA_JSON = "toprate_data.json"
BETA = 0.30
EDGE_THRESHOLD = 0.05
PRICE_CAP = 26.0
RETURN_UNITS = 4

SCRATCH_DIR = "/tmp/claude-0/-home-user-TopRate/37b9fca0-b163-5591-8763-1dcf84252930/scratchpad"
DAILY_CSV_OUT = f"{SCRATCH_DIR}/live_data_beta03_daily_summary.csv"
STATE_CSV_OUT = f"{SCRATCH_DIR}/live_data_beta03_state_summary.csv"
QUALITY_CSV_OUT = f"{SCRATCH_DIR}/live_data_beta03_quality_summary.csv"
STATE_QUALITY_CSV_OUT = f"{SCRATCH_DIR}/live_data_beta03_state_quality_summary.csv"
BETS_CSV_OUT = f"{SCRATCH_DIR}/live_data_beta03_all_bets.csv"

QUALITY_BINS = [0, 20_000, 30_000, 50_000, 100_000, float("inf")]
QUALITY_LABELS = ["Bush (<=20k)", "Provincial (20-30k)", "Midweek Metro (30-50k)",
                   "Feature (50-100k)", "Stakes/Group (>100k)"]


def market_price(r):
    return r.get("fx") or r.get("sp") or r.get("top")


def collect_bets(races, beta):
    rows = []
    for race in races:
        if race.get("done") != 1:
            continue
        runners = race.get("runners") or []
        active = [r for r in runners if not r.get("scr")]
        if not active:
            continue
        # eligibility: every active runner must carry a projection, same
        # as SummaryTab.tsx's collectPicks - a race missing a rating for
        # even one runner isn't graded for anyone else in it.
        if any(r.get("wpjp") is None for r in active):
            continue
        scored = []
        for r in active:
            price = market_price(r)
            if price is None or price <= 1:
                continue
            scored.append((r, r["wpjp"], price))
        if len(scored) < 2:
            continue
        projs = np.array([x[1] for x in scored], dtype=float)
        prices = np.array([x[2] for x in scored], dtype=float)
        e = np.exp(beta * (projs - projs.max()))
        model_prob = e / e.sum()
        inv = 1.0 / prices
        mkt_prob = inv / inv.sum()
        edge = model_prob - mkt_prob
        for (r, proj, price), ed in zip(scored, edge):
            if ed < EDGE_THRESHOLD or price > PRICE_CAP:
                continue
            won = r.get("won")
            if won is None:
                continue  # not yet resulted (shouldn't happen once done==1, but be safe)
            rows.append({
                "date": race.get("date"), "venue": race.get("venue"), "race": race.get("race"),
                "state": race.get("state"), "prize": race.get("prize"),
                "horse": r.get("h"), "price": price, "edge": ed, "won": int(won),
            })
    return pd.DataFrame(rows)


def summarize(g):
    n = len(g)
    wins = int(g["won"].sum())
    stake = RETURN_UNITS / g["price"].to_numpy()
    profit = np.where(g["won"] == 1, RETURN_UNITS - stake, -stake)
    staked = float(stake.sum())
    total_profit = float(profit.sum())
    se = profit.std(ddof=1) / np.sqrt(n) if n > 1 else np.nan
    t = profit.mean() / se if se and se > 0 else np.nan
    return pd.Series({
        "n_bets": n, "wins": wins,
        "strike_pct": wins / n * 100 if n else np.nan,
        "staked_u": staked, "profit_u": total_profit,
        "roi_pct": total_profit / staked * 100 if staked else np.nan,
        "t_stat": t,
    })


def print_table(df, title, formatters=None):
    fmt = formatters or {
        "strike_pct": "{:.1f}%".format, "roi_pct": "{:+.1f}%".format,
        "staked_u": "{:.2f}u".format, "profit_u": "{:+.2f}u".format, "t_stat": "{:+.2f}".format,
    }
    print(f"\n{'='*90}\n{title}\n{'='*90}")
    print(df.to_string(index=False, formatters=fmt))


def run():
    with open(DATA_JSON) as f:
        data = json.load(f)
    races = data["RACES"]
    done = [r for r in races if r.get("done") == 1]
    dates = sorted(set(r["date"] for r in done))
    print(f"Live payload: {len(races):,} races total, {len(done):,} resulted (done=1), "
          f"{len(dates)} distinct dates ({dates[0]} to {dates[-1]})")

    bets = collect_bets(races, BETA)
    bets["date"] = pd.to_datetime(bets["date"])
    bets["quality"] = pd.cut(bets["prize"], bins=QUALITY_BINS, labels=QUALITY_LABELS)
    print(f"Qualifying bets (edge>={EDGE_THRESHOLD}, price<=${PRICE_CAP:.0f}, beta={BETA}): {len(bets):,}")
    bets.to_csv(BETS_CSV_OUT, index=False)

    daily = bets.groupby(bets["date"].dt.date).apply(summarize, include_groups=False).reset_index()
    daily = daily.sort_values("date")
    daily.to_csv(DAILY_CSV_OUT, index=False)
    print_table(daily, f"DAILY SUMMARY (live data, beta={BETA})")

    monthly = bets.groupby(bets["date"].dt.to_period("M")).apply(summarize, include_groups=False).reset_index()
    monthly = monthly.rename(columns={"date": "month"})
    print_table(monthly, f"MONTHLY ROLLUP (live data, beta={BETA})")

    state_summary = bets.groupby("state", dropna=False).apply(summarize, include_groups=False).reset_index()
    state_summary = state_summary.sort_values("n_bets", ascending=False)
    state_summary.to_csv(STATE_CSV_OUT, index=False)
    print_table(state_summary, f"BREAKDOWN BY STATE (live data, beta={BETA})")

    quality_summary = bets.groupby("quality", observed=True).apply(summarize, include_groups=False).reset_index()
    quality_summary = quality_summary.set_index("quality").reindex(QUALITY_LABELS).reset_index()
    quality_summary.to_csv(QUALITY_CSV_OUT, index=False)
    print_table(quality_summary, f"BREAKDOWN BY RACE QUALITY (live data, beta={BETA})")

    state_quality = bets.groupby(["state", "quality"], observed=True).apply(
        summarize, include_groups=False).reset_index()
    state_order = state_summary["state"].tolist()
    state_quality["state"] = pd.Categorical(state_quality["state"], categories=state_order, ordered=True)
    state_quality["quality"] = pd.Categorical(state_quality["quality"], categories=QUALITY_LABELS, ordered=True)
    state_quality = state_quality.sort_values(["state", "quality"])
    state_quality.to_csv(STATE_QUALITY_CSV_OUT, index=False)
    print_table(state_quality, f"BREAKDOWN BY STATE x RACE QUALITY (live data, beta={BETA})")

    roi_pivot = state_quality.pivot(index="state", columns="quality", values="roi_pct")
    n_pivot = state_quality.pivot(index="state", columns="quality", values="n_bets")
    print(f"\n{'='*90}\nPIVOT: ROI% by state (rows) x quality (cols)\n{'='*90}")
    print(roi_pivot.to_string(float_format=lambda v: f"{v:+.1f}%" if pd.notna(v) else "-"))
    print(f"\n{'='*90}\nPIVOT: n bets by state (rows) x quality (cols)\n{'='*90}")
    print(n_pivot.to_string(float_format=lambda v: f"{v:.0f}" if pd.notna(v) else "-"))

    total_staked = bets.apply(lambda r: RETURN_UNITS / r["price"], axis=1).sum()
    total_profit = bets.apply(
        lambda r: (RETURN_UNITS - RETURN_UNITS / r["price"]) if r["won"] == 1 else -(RETURN_UNITS / r["price"]),
        axis=1).sum()
    print(f"\nOVERALL: n={len(bets):,}  staked={total_staked:.2f}u  profit={total_profit:+.2f}u  "
          f"ROI={total_profit/total_staked*100:+.1f}%")

    print(f"\nAll CSVs written under {SCRATCH_DIR}")
    print("\nCAVEAT: this window is Aug 3 - Sep 1 only (toprate_data.json's resulted-race window),")
    print("much shorter than the ~5-month reconstruction-based breakdown, and some days' underlying")
    print("wpjp values may predate this session's model changes (see docstring). Treat this as what")
    print("the dashboard currently shows, not a guarantee of what today's model would say if every")
    print("day were freshly recomputed.")


if __name__ == "__main__":
    run()
