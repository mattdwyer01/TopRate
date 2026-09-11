"""
wpr_base_anchor_roi_backtest.py - the ROI gate the wpr_base_calc_10yr_
retest.py MAE finding needs before being taken seriously (see chat, Sep
2026): ewm7 and ewm10 (untested spans, not currently shipped) beat the
currently-shipped ewm5 on BOTH average held-out MAE (6.762/6.788 vs
6.828) and era-to-era stability (std 0.165/0.162 vs 0.203) across the
genuinely 10-year-deep race_results dataset. This codebase has already
shown MAE and ROI can point in opposite directions (calibration-slope
removal, and the joint-training rejection this same session) - so the
anchor-window choice gets the same real-market-price check before any
change to _BASE_BLEND_ALPHA/_compute_base is even considered.

SCOPE: base anchor ALONE, not the full additive model. The MAE finding
this backtests was itself base-signal-only (own-history anchor design),
and the population ADJ_TERMS (track_barrier, closing_merit, trainer_
merit, jockey_merit) depend on toprate_runners.csv columns (trainer_
win_pct_365d, jockey_win_pct_90d) that only exist in the last ~4 months
of daily snapshots - including them would collapse this back down to a
recency-limited test, defeating the entire point of testing against
real decade depth. This isolates exactly the piece the MAE finding is
about.

DATA: reuses wpr_base_calc_10yr_retest.py's already-built D_CACHE
(the expensive per-horse feature build, batched over all 87,404+
horses) and combined race_results frame - no rebuild needed. Price and
outcome come from race_results ITSELF (priceStarting as the market
price, positionFinish==1 as won) rather than toprate_runners.csv, since
that CSV only covers the last ~4 months - using it would silently
re-introduce the recency-skew problem this whole investigation exists
to get away from. race_results' own 'winner' column is unusable (100%
NaN, checked directly) - positionFinish==1 is the correct derivation.

METHOD: leave-one-era-out (same 5 eras as wpr_base_calc_10yr_retest.py,
NOT an H1/H2 split, so the test stays about era-robustness specifically,
matching the framing the MAE finding itself used) - for each era, every
OTHER era is the fit set: a price-softmax beta is fit per candidate per
fold (Brier-minimization grid, same convention calibrate_price_beta.py
established), then that fold's held-out era is scored and pooled with
every other fold's held-out era. Edge is the WPR-PRICE method (model-
implied probability minus market-implied probability from priceStarting)
- not the z-score feature-blend edge the user has separately said to
ignore.

NO EM DASHES policy: hyphens only in this file.
"""
import pickle

import numpy as np
import pandas as pd

import wpr_projection as wp
from wpr_base_calc_10yr_retest import (
    load_combined, vectorized_ewm, compute_void_mask, assign_era,
    ERA_BOUNDS, D_CACHE,
)

BETA_GRID = [0.05, 0.10, 0.15, 0.20, 0.25, 0.30, 0.40]
EDGE_THRESHOLDS = [0.0, 0.02, 0.04, 0.06, 0.08, 0.10, 0.13, 0.15, 0.20]
PRICE_CAPS = [15.0, 26.0]

CANDIDATES = {
    "base_ewm5_current": "ewm5",
    "base_ewm7": "ewm7",
    "base_ewm10": "ewm10",
}


def base_with_anchor(D, anchor_col):
    """Replicates _compute_base()'s exact fallback chain, but with
    anchor_col standing in for ewm5's slot - isolates the window-choice
    question from every other part of the base calc."""
    nett, anchor = D["wpr_nett"], D[anchor_col]
    both = nett.notna() & anchor.notna()
    base = pd.Series(
        np.where(both, wp._BASE_BLEND_ALPHA * nett + (1 - wp._BASE_BLEND_ALPHA) * anchor,
                 nett.fillna(anchor)),
        index=D.index)
    return base.fillna(D["avg_last3"]).fillna(D["career_avg"])


def _brier(data, beta, pred_col):
    rows = []
    for rid, g in data.groupby("race_id"):
        if len(g) < 4:
            continue
        pv = g[pred_col].to_numpy(dtype=float)
        e = np.exp(beta * (pv - pv.max()))
        p = e / e.sum()
        rows.extend(zip(p, g["won"]))
    arr = pd.DataFrame(rows, columns=["p", "won"])
    return float(((arr["p"] - arr["won"]) ** 2).mean()) if len(arr) else float("nan")


def _fit_beta(fit_half, pred_col):
    best_beta, best_brier = None, float("inf")
    for b in BETA_GRID:
        br = _brier(fit_half, b, pred_col)
        if br < best_brier:
            best_brier, best_beta = br, b
    return best_beta


def _edge_from_pred(frame, pred_col, beta):
    e = np.exp(beta * (frame[pred_col] - frame.groupby("race_id")[pred_col].transform("max")))
    denom = frame.groupby("race_id")[pred_col].transform(
        lambda s: np.exp(beta * (s - s.max())).sum())
    p_model = e / denom
    p_mkt = (1.0 / frame["sp"]) / frame.groupby("race_id")["sp"].transform(lambda s: (1.0 / s).sum())
    return p_model - p_mkt


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


def report_edge(bets, edge_col, label):
    print(f"\n{'='*70}\n{label}\n{'='*70}")
    print(f"total held-out bets: {len(bets):,}  [population avg price ${bets['sp'].mean():.2f}]\n")
    print("=== Edge threshold alone ===")
    for thr in EDGE_THRESHOLDS:
        report(bets[bets[edge_col] >= thr], f"edge>={thr:.2f}")
    print("\n=== Edge threshold x price cap ===")
    for thr in EDGE_THRESHOLDS:
        base = bets[bets[edge_col] >= thr]
        for cap in PRICE_CAPS:
            report(base[base["sp"] <= cap], f"edge>={thr:.2f}, price<={cap:.0f}")


def load_D():
    print(f"Loading cached D from {D_CACHE} ...")
    with open(D_CACHE, "rb") as f:
        D = pickle.load(f)
    print(f"  {len(D):,} rows")
    return D


def run():
    combined = load_combined()
    D = load_D()

    print("\nDeriving won (positionFinish==1) and sp (priceStarting) from "
          "race_results itself - NOT toprate_runners.csv, which only "
          "covers the last ~4 months and would re-introduce recency skew...")
    side = combined[["horse_id", "date", "race_id", "positionFinish", "priceStarting"]].copy()
    side["date"] = pd.to_datetime(side["date"], errors="coerce")
    side["race_id"] = side["race_id"].astype(str)
    side["won"] = (pd.to_numeric(side["positionFinish"], errors="coerce") == 1).astype(int)
    side["sp"] = pd.to_numeric(side["priceStarting"], errors="coerce")
    side = side.dropna(subset=["date", "sp"]).drop_duplicates(
        subset=["horse_id", "date", "race_id"], keep="first")
    side = side[side["sp"] > 1.0]

    D = D.copy()
    D["race_id"] = D["race_id"].astype(str)
    key_cols = ["horse_id", "date", "race_id"]
    before = len(D)
    D = D.merge(side[key_cols + ["won", "sp"]], on=key_cols, how="left")
    assert len(D) == before, "won/sp merge changed row count"
    D = D.dropna(subset=["won", "sp"]).copy()
    print(f"  {len(D):,} rows with a usable price and outcome")

    print("\nComputing void mask and extra-span candidates (ewm7/ewm10) on combined...")
    void_mask = compute_void_mask(combined)
    for span in (7, 10):
        c = vectorized_ewm(combined, span, "wpr", void_mask_col=void_mask)
        c = c.rename(columns={f"ewm{span}_wpr": f"ewm{span}"})
        D = D.merge(c, on=key_cols, how="left")

    D["_era"] = assign_era(D["date"])
    era_names = [e[0] for e in ERA_BOUNDS]
    print(f"\nEra row counts (with usable price/outcome):\n"
          f"{D['_era'].value_counts().reindex(era_names)}")

    results = {}
    for label, anchor_col in CANDIDATES.items():
        D[f"pred_{label}"] = base_with_anchor(D, anchor_col)

    for label in CANDIDATES:
        pred_col = f"pred_{label}"
        pooled_parts = []
        betas = []
        for era in era_names:
            fit_half = D[D["_era"] != era]
            held_out = D[D["_era"] == era].copy()
            if len(held_out) < 200:
                continue
            beta = _fit_beta(fit_half, pred_col)
            betas.append(beta)
            held_out["edge"] = _edge_from_pred(held_out, pred_col, beta)
            pooled_parts.append(held_out)
        pooled = pd.concat(pooled_parts, ignore_index=True)
        results[label] = pooled
        print(f"\n{label}: per-era betas = {betas}")
        report_edge(pooled, "edge", f"{label} (leave-one-era-out, pooled held-out eras)")

    print("\nSame multiple-comparisons caveat as every backtest in this codebase:")
    print("treat this as a hypothesis, not a result to ship blind.")
    print("\nDone.")


if __name__ == "__main__":
    run()
