"""Flag days whose declared runners are missing a WPR projection (15 Oct 2026).

Reads runners.csv, takes every non-scratched, drawn (barrier above 0) runner of today (Melbourne date) and reports the share with a projection
(`wprp_proj`). Exits 1 when a day with at least MIN_RUNNERS runners is under THRESHOLD, so the step shows red in Actions. Debut runners are
projected by the light model, so every declared runner is expected to have one, apart from jumps races and runners with no usable history.
Only today is checked by default (16 Oct 2026): the daily fetch that brings in tomorrow's and later declarations runs at the same time as the
projection workflow, so new declarations are still unprojected when this step reads them (17 Oct: 29.6% at 09:32, picked up by the next projection run), and
undrawn nominations (barrier 0, 18 Oct: 0 of 1,178) are not projected at all. Pass --days 2 or 3 to look further ahead.
Usage: python check_projection_coverage.py [--threshold 0.9] [--days 1]
"""
import argparse
import sys
import warnings
from datetime import datetime, timedelta
from zoneinfo import ZoneInfo

import pandas as pd

import runners_io

MIN_RUNNERS = 20


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--threshold", type=float, default=0.9)
    ap.add_argument("--days", type=int, default=1)
    a = ap.parse_args()
    warnings.filterwarnings("ignore")
    df = runners_io.read_runners()
    first = datetime.now(ZoneInfo("Australia/Melbourne")).date()
    bad = 0
    for k in range(a.days):
        d = (first + timedelta(days=k)).isoformat()
        x = df[(df["date"].astype(str).str[:10] == d) & (pd.to_numeric(df["scratched"], errors="coerce").fillna(0) != 1)
               & (pd.to_numeric(df["barrier"], errors="coerce") > 0)]
        if len(x) < MIN_RUNNERS:
            print(f"{d}: {len(x)} runners, skipped (under {MIN_RUNNERS})")
            continue
        have = pd.to_numeric(x["wprp_proj"], errors="coerce").notna()
        share = have.mean()
        flag = "LOW" if share < a.threshold else "ok"
        print(f"{d}: {int(have.sum())} of {len(x)} runners projected ({share:.1%}) {flag}")
        if share < a.threshold:
            bad += 1
            miss = x[~have].groupby("venue").size().sort_values(ascending=False).head(5)
            print("   most missing: " + ", ".join(f"{v} {n}" for v, n in miss.items()))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
