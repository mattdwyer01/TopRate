"""Fit the results-file ATW adjustment: how far a run's results-file `atw` sits from its plain `wpr`, from weight carried, racing age, sex and month.

The results files' `atw` restates each run on a weight-for-age scale (about -0.8 WPR per kg carried, with an age x sex x month intercept), so the
model's plain-WPR projection needs this shift before it is compared with `wpr_actual` (which is the results `atw`). Output: atw_results_scale.json
(read by atw_results_scale.py). Usage: python setup_atw_results_scale.py [--through YYYY-MM-DD] [--out PATH]  (--through = fit cut-off, for holdout checks)
"""
import argparse
import glob
import json
import os

import numpy as np
import pandas as pd

ROOT = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(ROOT, "projection", "models", "atw_results_scale.json")
SEX = {"G": "G", "M": "M", "F": "F", "C": "C", "H": "C", "R": "G"}
MIN_CELL = 15


def load():
    cols = ["horse_id", "date", "wpr", "atw", "weightCarried", "horse_age", "horse_sex"]
    d = pd.concat([pd.read_csv(f, usecols=lambda c: c in set(cols), low_memory=False) for f in sorted(glob.glob(os.path.join(ROOT, "race_results_20*.csv.gz")))], ignore_index=True)
    for c in ("wpr", "atw", "weightCarried", "horse_age"):
        d[c] = pd.to_numeric(d[c], errors="coerce")
    d["date"] = pd.to_datetime(d["date"], errors="coerce")
    d = d.dropna(subset=["wpr", "atw", "weightCarried", "horse_age", "date"]).drop_duplicates(["horse_id", "date"], keep="last")
    d["ra"] = d.atw - d.wpr
    d["sx"] = d.horse_sex.map(SEX).fillna("G")
    d["age"] = d.horse_age.clip(2, 7).astype(int)
    d["mo"] = d.date.dt.month
    return d


def fit(d):
    keys = ["age", "sx", "mo"]
    cm = d.groupby(keys).ra.transform("mean")
    wm = d.groupby(keys).weightCarried.transform("mean")
    b = float(((d.ra - cm) * (d.weightCarried - wm)).sum() / ((d.weightCarried - wm) ** 2).sum())
    d = d.assign(res=d.ra - b * d.weightCarried)
    tab = d.groupby(keys).res.agg(["mean", "count"])
    two = d.groupby(["age", "sx"]).res.mean()
    cells = {f"{a}|{s}|{m}": round(float(r["mean"]), 3) for (a, s, m), r in tab.iterrows() if r["count"] >= MIN_CELL}
    pairs = {f"{a}|{s}": round(float(v), 3) for (a, s), v in two.items()}
    return dict(slope=round(b, 4), cells=cells, pairs=pairs, glob=round(float(d.res.mean()), 3), n=int(len(d)), through=str(d.date.max().date()))


def predict(model, w, age, sx, mo):
    from atw_results_scale import offset
    return offset(model, w, age, sx, mo)


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--through")
    ap.add_argument("--out", default=OUT)
    a = ap.parse_args()
    D = load()
    if a.through:
        D = D[D.date <= a.through]
    m = fit(D)
    os.makedirs(os.path.dirname(a.out), exist_ok=True)
    json.dump(m, open(a.out, "w"))
    print(f"fitted on {m['n']} runs through {m['through']}: slope {m['slope']}, {len(m['cells'])} cells -> {a.out}")
