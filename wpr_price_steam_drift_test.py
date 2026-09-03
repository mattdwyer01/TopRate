"""
wpr_price_steam_drift_test.py - tests price steam/drift (open_price vs
fixed_win_price movement) as a candidate signal, the last item on the
"genuinely different from edge-vs-market" list (see wpr_real_model_
calibration_diagnosis.py / wpr_calibrated_edge_kfold_validation.py /
wpr_top_pick_margin_strategy_kfold.py / wpr_rank_hitrate_vs_market_
favourite.py - all four already show no real edge, and the model's own
ranking trails the market's). This one is genuinely different: it's a
MARKET-ONLY signal (does how a price MOVED predict outcome beyond what
the CLOSING price alone already says), not a WPR-vs-market comparison,
so it doesn't inherit the "model loses to the market" problem at all.

DATA CAVEAT (important, read before trusting any result here): open_
price is only populated in toprate_runners.csv from 2026-08-23 onward
(price_refresh.py's tracking apparently didn't start earlier, or isn't
retained further back) - n=4,287 resulted runners with BOTH open_price
and fixed_win_price, an 11-day window, versus the ~5-month/50,000+ row
samples every other test in this investigation used. Any finding here
carries much less statistical weight by construction - treat a result
from this script as a much weaker hypothesis than the others, not a
confirmed pattern.

METHOD: direction/magnitude from open_price -> fixed_win_price, same
convention as the dashboard's own frontend/src/lib/priceMove.ts
(firmed = price got shorter, drifted = price got longer). Backing at the
CLOSING price (fixed_win_price) with proportional stake-to-return-
RETURN_UNITS, same convention as every other backtest this session.
Two views:
  1. Split into firmed / steady / drifted buckets (a 3% threshold to
     exclude rounding noise, matching MOVE_DISPLAY_THRESHOLD_PCT) and
     compare strike rate / ROI at the closing price for each - if steam
     carries real information beyond the closing price, firmers should
     out-perform their closing odds (positive ROI) and drifters should
     under-perform (negative ROI), since the closing price itself was
     already shown to be close to well-calibrated (wpr_real_model_
     calibration_diagnosis.py's market sanity-check).
  2. The same split WITHIN price bands (favourite/mid/longshot), since
     raw pct-move is naturally larger for longshots and could otherwise
     just be re-discovering the price-band effect rather than a real
     drift signal.

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np
import pandas as pd

RUNNERS_CSV = "toprate_runners.csv"
RETURN_UNITS = 4
PRICE_CAP = 26.0
NOISE_THRESHOLD_PCT = 3.0  # matches frontend's MOVE_DISPLAY_THRESHOLD_PCT
MOVE_BUCKETS = [
    (-float("inf"), -10, "drifted >10%"),
    (-10, -3, "drifted 3-10%"),
    (-3, 3, "steady (<3%)"),
    (3, 10, "firmed 3-10%"),
    (10, float("inf"), "firmed >10%"),
]
PRICE_BANDS = [(1.0, 3.0, "favourite <$3"), (3.0, 8.0, "mid $3-8"), (8.0, 26.0, "longshot $8-26")]


def score(df):
    n = len(df)
    if n == 0:
        return None
    wins = int(df["won"].sum())
    stake = RETURN_UNITS / df["fixed_win_price"].to_numpy()
    profit = np.where(df["won"] == 1, RETURN_UNITS - stake, -stake)
    staked = stake.sum()
    total_profit = profit.sum()
    se = profit.std(ddof=1) / np.sqrt(n) if n > 1 else np.nan
    t = profit.mean() / se if se and se > 0 else np.nan
    return {"n": n, "strike": wins / n * 100, "staked": staked,
             "profit": total_profit, "roi": total_profit / staked * 100 if staked else np.nan, "t": t}


def print_score(label, s):
    if s is None or s["n"] < 10:
        print(f"  {label:<20} n={s['n'] if s else 0} (too small)")
        return
    print(f"  {label:<20} n={s['n']:5d}  strike={s['strike']:5.1f}%  "
          f"ROI={s['roi']:+7.1f}%  t={s['t']:+.2f}")


def run():
    print("Reading toprate_runners.csv...")
    df = pd.read_csv(RUNNERS_CSV, low_memory=False,
                      usecols=["date", "resulted", "won", "scratched", "open_price",
                               "fixed_win_price", "race_id"])
    df["resulted"] = pd.to_numeric(df["resulted"], errors="coerce")
    df["scratched"] = pd.to_numeric(df["scratched"], errors="coerce")
    df["won"] = pd.to_numeric(df["won"], errors="coerce")
    df["date"] = pd.to_datetime(df["date"], errors="coerce")
    df = df[(df["resulted"] == 1) & (df["scratched"] != 1)].dropna(subset=["won", "date"])

    df["open_price"] = pd.to_numeric(df["open_price"], errors="coerce")
    df["fixed_win_price"] = pd.to_numeric(df["fixed_win_price"], errors="coerce")
    df = df.dropna(subset=["open_price", "fixed_win_price"])
    df = df[(df["open_price"] > 1.0) & (df["fixed_win_price"] > 1.0) & (df["fixed_win_price"] <= PRICE_CAP)]
    df["won"] = df["won"].astype(int)

    print(f"Population: {len(df):,} resulted, non-scratched runners with both open_price and "
          f"fixed_win_price, {df['date'].min().date()} to {df['date'].max().date()}")
    print("CAVEAT: this is an 11-day window (open_price coverage starts 2026-08-23) - MUCH")
    print("smaller than the ~5-month samples every other test in this investigation used.")

    df["pct_move"] = (df["open_price"] - df["fixed_win_price"]) / df["open_price"] * 100  # positive = firmed

    print(f"\n{'='*90}\nSTRIKE RATE / ROI BY MOVE BUCKET (backing at closing price)\n{'='*90}")
    for lo, hi, label in MOVE_BUCKETS:
        sub = df[(df["pct_move"] > lo) & (df["pct_move"] <= hi)]
        s = score(sub)
        print_score(label, s)

    print(f"\n{'='*90}\nSAME, WITHIN PRICE BAND (checking it isn't just re-finding the price-band effect)\n{'='*90}")
    for plo, phi, plabel in PRICE_BANDS:
        print(f"\n  --- {plabel} ---")
        band = df[(df["fixed_win_price"] >= plo) & (df["fixed_win_price"] < phi)]
        for lo, hi, label in MOVE_BUCKETS:
            sub = band[(band["pct_move"] > lo) & (band["pct_move"] <= hi)]
            s = score(sub)
            print_score(label, s)

    print(f"\n{'='*90}\nSIMPLE TWO-WAY SPLIT: firmed (>{NOISE_THRESHOLD_PCT}%) vs drifted (>{NOISE_THRESHOLD_PCT}%)\n{'='*90}")
    firmed = df[df["pct_move"] > NOISE_THRESHOLD_PCT]
    drifted = df[df["pct_move"] < -NOISE_THRESHOLD_PCT]
    steady = df[df["pct_move"].abs() <= NOISE_THRESHOLD_PCT]
    print_score("firmed", score(firmed))
    print_score("drifted", score(drifted))
    print_score("steady", score(steady))

    print(f"\n{'='*90}\nCORRELATION CHECK: pct_move vs price (is drift just re-deriving price band?)\n{'='*90}")
    print(f"  corr(pct_move, fixed_win_price) = {df['pct_move'].corr(df['fixed_win_price']):.3f}")
    print(f"  corr(|pct_move|, fixed_win_price) = {df['pct_move'].abs().corr(df['fixed_win_price']):.3f}")

    print("\nSmall-sample caveat applies more here than any other test this session - treat any")
    print("apparent effect as a much weaker hypothesis, not a confirmed pattern, given n.")


if __name__ == "__main__":
    run()
