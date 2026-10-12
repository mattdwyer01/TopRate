"""
own_ratings/chain.py -- forward chain: observed runs (margins, weights) in date order -> own ATW and WPR per run.

Input rows (one per runner): date, race_id, horse_id, distance, weightCarried, horse_sex, horse_foaled, margin (lengths behind
the winner, winner 0), optional price. History is a dict horse_id -> list of that horse's last ATWs (most recent last), seeded
from TopRate's ratings for old runs and extended by this chain.
"""
from collections import defaultdict

import numpy as np
import pandas as pd

from . import core


def seed_history(past):
    """past: rows with date, horse_id, wpr, weightCarried, horse_sex, horse_foaled, distance. Returns {horse_id: [atw, ...]} (oldest first)."""
    p = past[past["wpr"].notna() & past["weightCarried"].notna() & past["horse_foaled"].notna()].copy()
    p = core.add_weight_terms(p, 0.8)
    p = p[p["wadj"].notna()]
    p["atw"] = p["wpr"] - p["wadj"]
    p = p.sort_values(["horse_id", "date"])
    return {h: g["atw"].tolist()[-6:] for h, g in p.groupby("horse_id")}


def run_chain(obs, hist, fallback_rs=None):
    """Returns obs with atw, wpr, rs_hat, n_inform added. hist is updated in place."""
    o = core.add_weight_terms(obs, 0.8).sort_values(["date", "race_id"]).reset_index(drop=True)
    o["m"] = o["margin"].fillna(np.nan).clip(0, core.MARGIN_CAP)
    o["k"] = core.k_per_length(o["distance"]) * core.margin_scale(o["distance"])
    atw = np.full(len(o), np.nan)
    rs_out = np.full(len(o), np.nan)
    ninf = np.zeros(len(o), int)
    last_rs = fallback_rs if fallback_rs is not None else 80.0
    for rid, idx in o.groupby("race_id", sort=False).indices.items():
        x = o.iloc[idx]
        imp = []
        for j, h in enumerate(x["horse_id"].values):
            hh = hist.get(h)
            m = x["m"].values[j]
            if hh is not None and len(hh) >= core.MIN_PRIORS and not np.isnan(m):
                imp.append(np.mean(hh[-3:]) + x["k"].values[j] * m)
        if imp:
            rs = core.trimmed_mean(imp) + core.RS_BIAS
            last_rs = 0.98 * last_rs + 0.02 * rs
        else:
            rs = last_rs                      # nobody informs: fall back to the running level
        a = rs - x["k"].values * x["m"].values
        atw[idx] = a
        rs_out[idx] = rs
        ninf[idx] = len(imp)
        for h, av in zip(x["horse_id"].values, a):
            if not np.isnan(av):
                hist.setdefault(h, []).append(float(av))
                if len(hist[h]) > 6:
                    del hist[h][0]
    o["atw"] = atw
    o["rs_hat"] = rs_out
    o["n_inform"] = ninf
    o["wpr_own"] = o["atw"] + o["wadj"]
    return o
