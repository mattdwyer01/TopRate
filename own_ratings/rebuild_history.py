"""Rate EVERY past run with our own chain, with no TopRate rating anywhere in the inputs (13 Oct 2026).

The existing chain (chain.py) was seeded from TopRate's ratings. Here it starts from an empty history on the first race in the results
files and uses only observed facts: finishing margin, distance, weight carried, age and sex. A race's strength (RS) is estimated from
the runners that already have two own rated runs; a race where nobody does falls back to a running level that starts at ANCHOR.
The anchor is an arbitrary scale convention (it sets the average rating, not the order), chosen so the numbers stay on a familiar
scale for the dashboard axes and the 2/4/8 gap lines (which are differences, so not affected by it).

TopRate's `wpr` column is read ONLY by --validate, to report how close the result is; it never feeds a rating.

  python -m own_ratings.rebuild_history --out own_ratings_history.csv.gz [--validate]
"""
import argparse
import glob
import sys
import time

import numpy as np
import pandas as pd

from . import chain, core

ANCHOR = 70.0
LEVEL_DAYS = 180        # trailing window for the level correction
LEVEL_WARMUP = 60       # days of data before the correction can use a trailing window
COLS = ["race_id", "date", "horse_id", "horse", "track", "distance", "weightCarried", "positionFinish", "marginFinish", "horse_age",
        "horse_sex", "isBarrierTrial", "is_jumpout", "race_class"]


def load_observations(pattern="race_results_20*.csv.gz"):
    parts = []
    for p in sorted(glob.glob(pattern)):
        d = pd.read_csv(p, low_memory=False)
        d = d[[c for c in COLS + ["wpr"] if c in d.columns]]
        d["src"] = p
        parts.append(d)
    d = pd.concat(parts, ignore_index=True)
    d["date"] = d["date"].astype(str).str[:10]
    # one row per (race, horse); the TopRate-era file wins over the racing.com extension for the same run
    d = d.drop_duplicates(["race_id", "horse_id"], keep="first")
    return d


def prepare(d):
    jumps = d.get("race_class", pd.Series("", index=d.index)).astype(str).str.contains("Hurdle|Steeple|Jump", case=False, na=False)
    ok = ((d.get("isBarrierTrial", 0).fillna(0).astype(float) == 0) & (d.get("is_jumpout", 0).fillna(0).astype(float) == 0) & ~jumps
          & d.positionFinish.notna() & d.marginFinish.notna() & d.distance.notna() & d.horse_id.notna())
    o = d[ok].copy()
    o["horse_id"] = o.horse_id.astype("int64")
    o["margin"] = pd.to_numeric(o.marginFinish, errors="coerce").clip(lower=0)
    # weight missing (about 18% of old rows): the race's median carried weight, else 57 kg
    med = o.groupby("race_id").weightCarried.transform("median")
    o["weightCarried"] = pd.to_numeric(o.weightCarried, errors="coerce").fillna(med).fillna(57.0)
    age = pd.to_numeric(o.horse_age, errors="coerce").fillna(4).clip(2, 12)
    dt = pd.to_datetime(o.date)
    sy = np.where(dt.dt.month >= 8, dt.dt.year, dt.dt.year - 1)
    o["horse_foaled"] = pd.to_datetime((sy - age.values).astype(int).astype(str) + "-09-01")   # racing_age(date, foaled) == age
    return o[["date", "race_id", "horse_id", "horse", "distance", "weightCarried", "horse_sex", "horse_foaled", "margin"]
             + (["wpr"] if "wpr" in o else [])].reset_index(drop=True)


def level_correction(dates, wpr):
    """Per-run offset that keeps the average rating at ANCHOR, using only our own earlier ratings (causal, so a past value never changes
    when later races are added). The chain conserves the field average only approximately and drifted about a point a year; this removes
    that drift without looking at any outside number. Offset on day d = ANCHOR - mean of own ratings in the LEVEL_DAYS before d; the
    first LEVEL_WARMUP days use the mean of those days themselves."""
    df = pd.DataFrame({"d": pd.to_datetime(dates), "w": wpr})
    daily = df.groupby("d").w.agg(["sum", "count"]).sort_index()
    idx = pd.date_range(daily.index.min(), daily.index.max(), freq="D")
    daily = daily.reindex(idx, fill_value=0)
    s = daily["sum"].rolling(LEVEL_DAYS, min_periods=1).sum().shift(1)
    c = daily["count"].rolling(LEVEL_DAYS, min_periods=1).sum().shift(1)
    mean = (s / c)
    first = daily.iloc[:LEVEL_WARMUP]
    warm = first["sum"].sum() / max(first["count"].sum(), 1)
    mean = mean.where(c >= 2000, warm)
    off = ANCHOR - mean
    return df["d"].map(off).values


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default="own_ratings_history.csv.gz")
    ap.add_argument("--validate", action="store_true", help="compare with TopRate's wpr (report only)")
    a = ap.parse_args()
    t0 = time.time()
    d = load_observations()
    o = prepare(d)
    print(f"{len(o):,} rated-eligible runs, {o.race_id.nunique():,} races, {o.date.min()} to {o.date.max()} ({time.time() - t0:.0f}s)", flush=True)
    toprate = o["wpr"].copy() if "wpr" in o else None
    r = chain.run_chain(o.drop(columns=["wpr"], errors="ignore"), {}, fallback_rs=ANCHOR)
    print(f"chain done ({time.time() - t0:.0f}s)", flush=True)
    out = r[["race_id", "date", "horse_id", "horse", "atw", "wpr_own", "rs_hat", "n_inform"]].rename(columns={"wpr_own": "wpr_chain"})
    off = level_correction(out["date"], out["wpr_chain"].values)
    out["wpr"] = (out.wpr_chain + off).round(2)
    out["atw"] = (out.atw + off).round(2)
    out = out.drop(columns=["wpr_chain"])
    out["rs_hat"] = out.rs_hat.round(2)
    out.to_csv(a.out, index=False, compression="gzip")
    print(f"wrote {len(out):,} rows to {a.out}")
    if a.validate and toprate is not None:
        v = r.merge(d[["race_id", "horse_id", "wpr"]].rename(columns={"wpr": "tr"}), on=["race_id", "horse_id"], how="left")
        v = v.dropna(subset=["tr", "wpr_own"])
        v["yr"] = v.date.astype(str).str[:4]
        v["e"] = v.wpr_own - v.tr
        print("year   n        bias    MAE    corr   within-race rank corr  (own vs TopRate; validation only)")
        for y, g in v.groupby("yr"):
            rc = g.assign(a=g.groupby("race_id").wpr_own.rank(), b=g.groupby("race_id").tr.rank()).groupby("race_id").apply(
                lambda x: x.a.corr(x.b) if len(x) > 3 else np.nan).mean()
            print(f"{y}  {len(g):>8,}  {g.e.mean():+6.2f}  {g.e.abs().mean():5.2f}  {g.wpr_own.corr(g.tr):.3f}  {rc:.3f}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
