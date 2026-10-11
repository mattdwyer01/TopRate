"""Projection (plain WPR) -> the results files' `atw` scale, so a miss against wpr_actual compares like with like. See setup_atw_results_scale.py.

The shift depends on the weight carried in that race, the horse's racing age (rolls over 1 August), sex and month, so it is computed for every runner
of every race (past races too) from the runner's own weight and the horse's age/sex in the results files. Fail-safe: any error returns {} (no shift).
"""
import glob
import json
import os

import numpy as np
import pandas as pd

ROOT = os.path.dirname(os.path.abspath(__file__))
MODEL = os.path.join(ROOT, "projection", "models", "atw_results_scale.json")
SEX = {"G": "G", "M": "M", "F": "F", "C": "C", "H": "C", "R": "G"}


def offset(model, w, age, sx, mo):
    """Expected (atw - wpr) for one run; None if weight or age is unknown."""
    if w is None or age is None or w != w or age != age:
        return None
    a = int(min(max(age, 2), 7))
    s = SEX.get(str(sx), "G")
    base = model["cells"].get(f"{a}|{s}|{int(mo)}")
    if base is None:
        base = model["pairs"].get(f"{a}|{s}", model["glob"])
    return base + model["slope"] * float(w)


def results_scale_offsets(runners_df):
    """{run_id: expected results-atw minus plain wpr} for the rows of runners_df (needs run_id, horse_id, date, weight_carried)."""
    try:
        model = json.load(open(MODEL))
        r = runners_df[["run_id", "horse_id", "date", "weight_carried"]].copy()
        r["date"] = pd.to_datetime(r["date"], errors="coerce")
        r["horse_id"] = pd.to_numeric(r["horse_id"], errors="coerce")
        r["w"] = pd.to_numeric(r["weight_carried"], errors="coerce")
        r = r.dropna(subset=["run_id", "horse_id", "date"])
        ids = set(r.horse_id.astype("int64"))
        parts = []
        for f in sorted(glob.glob(os.path.join(ROOT, "race_results_20*.csv.gz"))):
            x = pd.read_csv(f, usecols=["horse_id", "date", "horse_age", "horse_sex", "weightCarried"], low_memory=False)
            x["horse_id"] = pd.to_numeric(x.horse_id, errors="coerce")
            parts.append(x[x.horse_id.isin(ids)])
        h = pd.concat(parts, ignore_index=True)
        h["date"] = pd.to_datetime(h["date"], errors="coerce")
        h["horse_age"] = pd.to_numeric(h["horse_age"], errors="coerce")
        h["rw"] = pd.to_numeric(h["weightCarried"], errors="coerce")
        h = h.dropna(subset=["horse_id", "date", "horse_age"]).drop_duplicates(["horse_id", "date"], keep="last")
        h["horse_id"] = h.horse_id.astype("int64")
        r["horse_id"] = r.horse_id.astype("int64")
        exact = r.merge(h, on=["horse_id", "date"], how="left")
        # no run on that date (a race still to run, or not in the results yet): the horse's last known run, age rolled to the race date
        last = h.sort_values("date").drop_duplicates("horse_id", keep="last").rename(columns={"date": "ld", "horse_age": "la", "horse_sex": "ls"})
        exact = exact.merge(last[["horse_id", "ld", "la", "ls"]], on="horse_id", how="left")
        roll = ((exact.date.dt.year - exact.ld.dt.year) + (exact.date.dt.month >= 8).astype(int) - (exact.ld.dt.month >= 8).astype(int)).clip(lower=0)
        exact["w"] = exact.w.fillna(exact.rw)   # runner rows from before weights were captured: the weight the results file recorded
        age = exact.horse_age.fillna(exact.la + roll)
        sex = exact.horse_sex.fillna(exact.ls)
        out = {}
        for rid, w, a, s, d in zip(exact.run_id, exact.w, age, sex, exact.date):
            v = offset(model, None if pd.isna(w) else float(w), None if pd.isna(a) else float(a), s, d.month)
            if v is not None:
                out[int(rid)] = round(float(v), 1)
        return out
    except Exception as e:
        print(f"  results-scale offsets skipped: {e}")
        return {}
