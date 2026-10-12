"""
own_ratings/backtest.py -- run the chain over races TopRate also rated, to see how far own ratings drift from TopRate's.

Seeds history from TopRate through --start, then chains forward using each race's real margins and weights (as if the margins
had arrived from public sources), comparing own WPR with TopRate WPR by month and scoring both as next-run forecasters.
usage: python -m own_ratings.backtest [--start 2025-07-01] [--end 2026-09-11]
"""
import argparse
import glob

import numpy as np
import pandas as pd

from . import chain, core

COLS = ["race_id", "date", "horse_id", "distance", "weightCarried", "horse_sex", "horse_foaled", "wpr", "marginFinish", "positionFinish",
        "priceStarting", "isBarrierTrial", "is_jumpout", "track"]


def load():
    d = pd.concat((pd.read_csv(f, usecols=lambda c: c in COLS, low_memory=False) for f in sorted(glob.glob("race_results_20*.csv.gz"))), ignore_index=True)
    d = d[(d.isBarrierTrial != 1) & (d.is_jumpout.fillna(0) != 1) & d.wpr.notna()].drop_duplicates(["race_id", "horse_id"])
    return d


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--start", default="2025-07-01")
    ap.add_argument("--end", default="2026-09-11")
    a = ap.parse_args()
    d = load()
    past, fut = d[d.date < a.start], d[(d.date >= a.start) & (d.date <= a.end)].copy()
    hist = chain.seed_history(past[past.date >= "2024-01-01"])
    fut["margin"] = np.where(fut.positionFinish == 1, 0.0, fut.marginFinish)
    o = chain.run_chain(fut, hist)
    o = o[o.wpr_own.notna() & o.wpr.notna()]
    o["err"] = o.wpr_own - o.wpr
    o["ym"] = o.date.str[:7]
    print(f"runs {len(o)} races {o.race_id.nunique()}  overall MAE {o.err.abs().mean():.2f} RMSE {np.sqrt((o.err**2).mean()):.2f} bias {o.err.mean():+.2f}")
    print(o.groupby("ym").agg(n=("err", "size"), bias=("err", "mean"), mae=("err", lambda s: s.abs().mean()), inform=("n_inform", "mean")).round(2).to_string())
    o["r_own"] = o.groupby("race_id").wpr_own.rank(ascending=False)
    o["r_tr"] = o.groupby("race_id").wpr.rank(ascending=False)
    print("within-race rank corr", round(o.r_own.corr(o.r_tr), 3))
    o.to_pickle("/tmp/own_backtest.pkl")


if __name__ == "__main__":
    main()
