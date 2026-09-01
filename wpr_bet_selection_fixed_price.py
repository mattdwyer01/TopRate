"""
wpr_bet_selection_fixed_price.py - re-runs wpr_bet_selection_dimensions.py's
price-cap test using an ACTUALLY-BETTABLE pre-race price instead of the
tote starting price (SP).

WHY THIS EXISTS
  calibrate_edge_score.py (and wpr_bet_selection_dimensions.py, built on
  top of it) compute both the market-implied probability ("edge" = model
  minus market) and the profit/loss simulation using starting_price_sp -
  the tote price the horse actually jumped at. That is a standard,
  defensible backtesting convention for asking "does the model beat the
  fullest-information closing price" - but it is NOT the same question as
  "would a human, backing this shortlist at a price available BEFORE the
  race, have made money" (see chat, Sep 2026): SP does not exist until
  the race starts, so a live selection rule can never be conditioned on
  it, and neither can a real bet be placed at exactly that number after
  the fact.

  This script re-runs the same walk-forward methodology with
  fixed_win_price (the continuously live-refreshed fixed-odds price,
  see toprate_price_refresh.py - naturally frozen at whatever it last
  was once a race stops being "still running" and gets no more
  refreshes) as the price basis for BOTH the market-probability term in
  "edge" and the profit calculation. 92% coverage on resulted races
  (vs open_price's 7% - too sparse to use as the primary source).
  Falls back to starting_price_sp only for the ~8% of rows missing
  fixed_win_price, flagged via a coverage line in the output so a
  reader can judge whether the fallback rate matters.

  This is still not perfect (fixed_win_price is "whatever the price was
  at the last capture before the race", which for a fast-moving market
  could be anywhere from 30 minutes to a few minutes before jump
  depending on the pipeline's own capture cadence - not a fixed,
  guaranteed "X minutes out" price) but it is a genuinely pre-race,
  actionable number, unlike SP.

USAGE
  python wpr_bet_selection_fixed_price.py

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np
import pandas as pd

from calibrate_edge_score import FEATURES, RUNNERS_CSV, _score

BURN_IN_WEEKS = 5
MIN_TRAIN = 300
EDGE_THRESHOLDS = [0.08, 0.10, 0.13, 0.15, 0.20]
PRICE_CAPS = [15.0, 26.0]


def _load_resulted_fixed_price():
    df = pd.read_csv(RUNNERS_CSV, dtype={"run_id": str, "race_id": str}, low_memory=False)
    df["resulted"] = pd.to_numeric(df.get("resulted"), errors="coerce")
    df = df[(df["resulted"] == 1) & (df.get("scratched") != 1)].copy()
    df["date"] = pd.to_datetime(df.get("date"), errors="coerce")
    df["won"] = pd.to_numeric(df.get("won"), errors="coerce").fillna(0)
    fx = pd.to_numeric(df.get("fixed_win_price"), errors="coerce")
    sp_fallback = pd.to_numeric(df.get("starting_price_sp"), errors="coerce")
    df["used_sp_fallback"] = fx.isna() & sp_fallback.notna()
    df["sp"] = fx.fillna(sp_fallback)
    for f in FEATURES:
        df[f] = pd.to_numeric(df.get(f), errors="coerce")
    df = df.dropna(subset=["date", "race_id", "sp"])
    df = df[df["sp"] > 1.0]
    return df.sort_values("date")


def walk_forward_bets(d, burn_in_weeks=BURN_IN_WEEKS, min_train=MIN_TRAIN):
    weeks = sorted(d["date"].dt.to_period("W").unique())
    test_weeks = weeks[burn_in_weeks:]
    bets = []
    for wk in test_weeks:
        train = d[d["date"].dt.to_period("W") < wk]
        test = d[d["date"].dt.to_period("W") == wk].copy()
        if len(train) < min_train or len(test) == 0:
            continue
        mean, std = train[FEATURES].mean(), train[FEATURES].std()
        test["score"] = _score(test, mean, std)
        test = test.dropna(subset=["score"])
        if len(test) == 0:
            continue
        e = np.exp(test["score"] - test.groupby("race_id")["score"].transform("max"))
        p = e / test.groupby("race_id")["score"].transform(lambda s: np.exp(s - s.max()).sum())
        test["p_mkt_norm"] = (1.0 / test["sp"]) / test.groupby("race_id")["sp"].transform(
            lambda s: (1.0 / s).sum())
        test["edge"] = p - test["p_mkt_norm"]
        bets.append(test[["won", "sp", "edge", "used_sp_fallback"]])
    return pd.concat(bets, ignore_index=True)


def report(sub, label):
    if len(sub) < 20:
        print(f"    {label}: n={len(sub)} (too small, skipped)")
        return
    profit = np.where(sub["won"] == 1, sub["sp"] - 1, -1.0)
    se = profit.std(ddof=1) / np.sqrt(len(profit))
    t = profit.mean() / se if se > 0 else float("nan")
    flag = "  ** SIGNIFICANT **" if abs(t) >= 1.96 else ""
    print(f"    {label}: n={len(sub):5d}  strike={sub['won'].mean()*100:5.2f}%  "
          f"ROI={profit.sum()/len(sub)*100:+6.2f}%  t={t:+.2f}{flag}")


def run():
    d = _load_resulted_fixed_price()
    fallback_pct = d["used_sp_fallback"].mean() * 100
    print(f"resulted races: {d['race_id'].nunique():,}  runners: {len(d):,}  "
          f"({d['date'].min().date()} to {d['date'].max().date()})")
    print(f"price basis: fixed_win_price (fell back to starting_price_sp for "
          f"{fallback_pct:.1f}% of rows missing it)\n")

    bets = walk_forward_bets(d)
    print(f"total scored bets across walk-forward weeks: {len(bets):,}\n")

    print("=== Edge threshold alone (fixed-price basis, no cap) ===")
    for thr in EDGE_THRESHOLDS:
        report(bets[bets["edge"] >= thr], f"edge>={thr:.2f}")
    print()

    print("=== Edge threshold x price cap (fixed-price basis) ===")
    for thr in EDGE_THRESHOLDS:
        base = bets[bets["edge"] >= thr]
        report(base, f"edge>={thr:.2f}, no price cap")
        for cap in PRICE_CAPS:
            report(base[base["sp"] <= cap], f"edge>={thr:.2f}, price<={cap:.0f}")
        print()

    print("Same multiple-comparisons caveat as wpr_bet_selection_dimensions.py: treat any")
    print("row here as a hypothesis for a future walk-forward period, not a result to ship.")


if __name__ == "__main__":
    run()
