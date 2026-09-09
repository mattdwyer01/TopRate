"""wpr_model_eval_harness.py - ONE authoritative walk-forward evaluation
harness for comparing candidate WPR architectures (Phase 0 of the "restart
WPR prediction from scratch" plan, Sep 2026).

WHY THIS EXISTS
  Today's session chased a real bug (a severe future-leak in build_
  training_frame()'s wpr_nett merge, now fixed - see that function's own
  docstring) partly because validation was scattered across many one-off
  scripts, each with its own slightly different split logic, metrics, and
  conventions. Comparing a new candidate architecture against the current
  shipped one needs ONE harness both are scored through identically, or
  any difference found is not trustworthy.

  Deliberately reports ONLY rating-quality metrics (MAE, AUC, Brier, top-
  pick strike rate vs the market favourite) - NOT ROI/edge. Today's work
  already showed the ROI axis has no signal right now regardless of
  architecture (wpr_adj_term_combo_search_test.py's leak-free joint search
  found no profitable combination), and conflating "is this an accurate
  rating" with "does this beat the market" was a real source of confusion
  this session. ROI is a separate, later question - only worth asking
  again if a candidate shows a genuine accuracy win here.

METHODOLOGY
  Monthly expanding-window walk-forward (same discipline as wpr_walkforward_
  shipped_roi_test.py): each fold's SCORER is fit on strictly-prior data
  only, then scores that month's held-out data. A "scorer" is any callable
  (fit_data, held_out) -> held_out-with-a-"pred"-column - candidate
  architectures plug in here without touching the harness itself.

USAGE
  import wpr_model_eval_harness as harness
  full = harness.build_frame()   # or your own frame with the same columns
  harness.run(full, my_scorer_fn, "My candidate architecture")

  Run directly to evaluate the CURRENT shipped architecture as the
  baseline everything else is compared against:
    python wpr_model_eval_harness.py

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np
import pandas as pd
from sklearn.metrics import mean_absolute_error, roc_auc_score

import wpr_projection as wpr
from wpr_adj_term_roi_ablation_test import build_frame, fit_fold_terms, ALL_TERMS_FULL

FOLD_MONTHS = ["2026-05", "2026-06", "2026-07", "2026-08", "2026-09"]
BETA_GRID = [0.05, 0.10, 0.15, 0.20, 0.25, 0.30, 0.40]


def _brier_and_beta(fit_scored, held_scored, pred_col):
    """Fits beta (softmax sharpness) by Brier-minimising grid search on
    fit_scored, then reports held_scored's Brier score at that beta. Beta
    is fit fresh per fold per architecture so a Brier comparison between
    two candidates is fair (neither is handicapped by a stale/mismatched
    beta) - same convention wpr_beta_recalibration_clean.py established."""
    def brier_at(data, beta):
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

    best_beta, best_brier = None, float("inf")
    for b in BETA_GRID:
        br = brier_at(fit_scored, b)
        if br < best_brier:
            best_brier, best_beta = br, b
    return brier_at(held_scored, best_beta), best_beta


def _top_pick_strike(scored, pred_col):
    idx = scored.groupby("race_id")[pred_col].idxmax()
    picks = scored.loc[idx]
    return float(picks["won"].mean() * 100), len(picks)


def _market_fav_strike(scored):
    idx = scored.groupby("race_id")["sp"].idxmin()
    picks = scored.loc[idx]
    return float(picks["won"].mean() * 100), len(picks)


def compute_metrics(fit_scored, held_scored, pred_col="pred"):
    d = held_scored.dropna(subset=[pred_col, "target", "won", "sp", "race_id"])
    mae = mean_absolute_error(d["target"], d[pred_col])
    auc = roc_auc_score(d["won"], d[pred_col])
    brier, beta = _brier_and_beta(fit_scored.dropna(subset=[pred_col, "won", "race_id"]), d, pred_col)
    strike, n_races = _top_pick_strike(d, pred_col)
    mkt_strike, _ = _market_fav_strike(d)
    return {
        "n": len(d), "n_races": n_races, "mae": round(mae, 4), "auc": round(auc, 4),
        "brier": round(brier, 5), "beta": beta,
        "top_pick_strike": round(strike, 2), "market_fav_strike": round(mkt_strike, 2),
    }


def print_metrics_row(label, m):
    print(f"  {label:<28} n={m['n']:>7} races={m['n_races']:>5}  MAE={m['mae']:>7.4f}  "
          f"AUC={m['auc']:>6.4f}  Brier={m['brier']:>7.5f} (beta={m['beta']})  "
          f"top-pick={m['top_pick_strike']:>5.2f}%  mkt-fav={m['market_fav_strike']:>5.2f}%")


def run(full, scorer_fn, label, fold_months=FOLD_MONTHS):
    """scorer_fn(fit_data, held_out) -> (fit_data_scored, held_out_scored),
    both carrying a "pred" column, fit strictly on fit_data. Returns the
    pooled held-out frame (with "pred") for any further inspection."""
    print(f"\n{'='*90}\n{label}\n{'='*90}")
    pooled = []
    for month in fold_months:
        fold_start = pd.Timestamp(month + "-01")
        fold_end = fold_start + pd.offsets.MonthBegin(1)
        fit_data = full[full["date"] < fold_start]
        held_out = full[(full["date"] >= fold_start) & (full["date"] < fold_end)]
        if len(fit_data) < 2000 or len(held_out) < 50:
            print(f"Fold {month}: skipped (insufficient data)")
            continue
        fit_scored, held_scored = scorer_fn(fit_data, held_out)
        m = compute_metrics(fit_scored, held_scored, "pred")
        print_metrics_row(f"Fold {month}", m)
        pooled.append(held_scored)

    pooled_df = pd.concat(pooled, ignore_index=True)
    # pooled Brier/beta needs a pooled fit-side frame too - reuse the LAST
    # fold's fit_scored as a reasonable stand-in is wrong (different beta
    # per fold already reported above); pool by re-deriving beta on the
    # pooled held-out set itself for a single summary number, purely
    # descriptive (each fold's own beta above is the leak-free one).
    beta_pooled, _ = _brier_and_beta(pooled_df, pooled_df, "pred")
    m_pooled = compute_metrics(pooled_df, pooled_df, "pred")
    print_metrics_row("POOLED", m_pooled)
    return pooled_df


def baseline_scorer(fit_data, held_out):
    """The CURRENT shipped architecture (_base + 11 ADJ_TERMS), refit per
    fold exactly as wpr_adj_term_roi_ablation_test.fit_fold_terms already
    does (population terms fit on fit_data, applied with per-race
    demeaning to both fit_data and held_out)."""
    fit_scored, held_scored = fit_fold_terms(fit_data, held_out)
    for f in (fit_scored, held_scored):
        f["pred"] = f["wprp_proj"]
    return fit_scored, held_scored


if __name__ == "__main__":
    full = build_frame()
    run(full, baseline_scorer, "BASELINE: current shipped architecture (_base + 11 ADJ_TERMS)")
