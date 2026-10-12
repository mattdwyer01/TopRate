"""Our rating store: one small file per year of the chain's output, read by the projection and bet-signal code in place of the rating
columns of the results files (which still carry TopRate's numbers).

Only the files whose content changed are rewritten, and a past year never changes (the chain is causal), so a nightly run touches the
current year's file only.

  write_by_year(df)    df has race_id, horse_id, date, atw, wpr
  load_overlay()       DataFrame indexed by (race_id, horse_id) with atw and wpr
"""
import glob
import os

import pandas as pd

DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "own_ratings_data")
COLS = ["race_id", "horse_id", "atw", "wpr"]


def path(year):
    return os.path.join(DIR, f"own_ratings_{year}.csv.gz")


def write_by_year(df):
    os.makedirs(DIR, exist_ok=True)
    df = df.copy()
    df["year"] = df["date"].astype(str).str[:4]
    n = 0
    for y, g in df.groupby("year"):
        g = g.sort_values(["race_id", "horse_id"])[COLS]
        new = g.to_csv(index=False)
        p = path(y)
        if os.path.exists(p):
            old = pd.read_csv(p).to_csv(index=False)
            if old == new:
                continue
        g.to_csv(p, index=False, compression={"method": "gzip", "mtime": 0})
        n += 1
    return n


_CACHE = {}


def load_overlay(root=None):
    d = root or DIR
    files = sorted(glob.glob(os.path.join(d, "own_ratings_20*.csv.gz")))
    key = tuple((f, os.path.getmtime(f)) for f in files)
    if key not in _CACHE:
        _CACHE.clear()
        o = pd.concat([pd.read_csv(f) for f in files], ignore_index=True).drop_duplicates(["race_id", "horse_id"], keep="last")
        _CACHE[key] = o.set_index(["race_id", "horse_id"])
    return _CACHE[key]
