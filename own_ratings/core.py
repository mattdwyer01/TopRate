"""
own_ratings/core.py -- our own WPR, rebuilt from public results (Oct 2026), replacing toprate.au's ratings.

Structure (see analysis/wpr_recreate.py, checked against 281k TopRate rows):
    ATW = RS - K(distance) * margin_lengths           K = max(2750 / distance, 1.5)
    WPR = ATW + 0.8 * (weight + 2*[filly/mare] - WFA(age, month, distance))
RS (race strength, the winner's ATW) was hand-reviewed by TopRate. Here it is estimated from the field itself: every runner
that has own rating history implies RS_j = E[ATW_j] + K * margin_j, where E[ATW_j] is the mean of its last 3 ATWs. The race's RS
is a trimmed mean of those. Because the mean of the new ATWs then equals the mean of the expectations, the field's average
rating is conserved from run to run (ratings cannot inflate or deflate on their own), and only the ordering within the field
is new information. Tuned settings (margin scale by distance band, margin cap, weight coefficient) come from the forecasting
tests recorded in CLAUDE.md; they can differ from TopRate's because the aim is next-run forecasting, not matching TopRate.
"""
import os

import numpy as np
import pandas as pd

HERE = os.path.dirname(os.path.abspath(__file__))
WFA_PATH = os.path.join(HERE, "..", "analysis", "wpr_wfa_table.csv")

# forecasting-tuned parameters (11 Oct 2026 tests, VIC/SA/QLD): margin scale by distance band, cap, weight coefficient
MARGIN_SCALE = (1.0, 1.2, 1.2)        # under 1300m, 1300 to 1800m, over 1800m (times TopRate's K)
MARGIN_CAP = 10.0                      # lengths
WEIGHT_COEF = 0.3                      # TopRate uses 0.8; the weight term adds almost nothing as a rating input
RS_BIAS = 0.0                          # calibrated by backtest (see own_ratings/backtest.py)
TRIM = 0.25                            # trimmed mean drops this share from each end
MIN_PRIORS = 2                         # runners with fewer own rated runs do not inform RS


def k_per_length(dist):
    return np.maximum(2750.0 / np.asarray(dist, float), 1.5)


def margin_scale(dist):
    d = np.asarray(dist, float)
    return np.where(d < 1300, MARGIN_SCALE[0], np.where(d <= 1800, MARGIN_SCALE[1], MARGIN_SCALE[2]))


def racing_age(date, foaled):
    dt, fo = pd.to_datetime(date), pd.to_datetime(foaled, errors="coerce")
    sy = np.where(dt.dt.month >= 8, dt.dt.year, dt.dt.year - 1)
    fy = np.where(fo.dt.month >= 8, fo.dt.year, fo.dt.year - 1)
    return (sy - fy + 1) - 1


_WFA = None


def wfa_table():
    global _WFA
    if _WFA is None:
        _WFA = pd.read_csv(WFA_PATH)
    return _WFA


def add_weight_terms(x, coef=0.8):
    """x needs date, distance, weightCarried, horse_sex, horse_foaled. Adds age, mon, db, fm, wfa_tab, wadj (rating points)."""
    x = x.copy()
    x["age"] = racing_age(x["date"], x["horse_foaled"]).clip(2, 4)
    x["mon"] = pd.to_datetime(x["date"]).dt.month
    x["db"] = (x["distance"] // 100).clip(8, 24)
    x["fm"] = x["horse_sex"].isin(["F", "M"]) * 2.0
    x = x.merge(wfa_table(), on=["age", "mon", "db"], how="left")
    x["wadj"] = coef * (x["weightCarried"] + x["fm"] - x["wfa_tab"])
    return x


def trimmed_mean(v, trim=TRIM):
    v = np.sort(np.asarray(v, float))
    if len(v) < 4:
        return float(np.median(v))
    q = int(len(v) * trim)
    return float(v[q:len(v) - q].mean())
