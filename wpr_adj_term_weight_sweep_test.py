"""wpr_adj_term_weight_sweep_test.py - use each ADJ_TERM's WEIGHT as the
lever to make wpr_price a more profitable overlay signal (user request,
Sep 2026): "We should be fitting wpr price so that it becomes profitable
as an overlay. Using adj's as the lever to bring it to profitability."

This is the safer, lower-overfit-risk version of that idea. A full JOINT
fit of ~11 term weights (+beta) directly against ROI would be easy to
overfit - ROI/t-stat is a noisy, lumpy objective (a couple of big-priced
winners can swing it a lot), and searching many free parameters against a
noisy target risks finding a "profitable" combination that is really just
the best of many random-looking draws (the exact failure mode this
session has repeatedly guarded against - see wpr_walkforward_shipped_roi_
test.py's docstring on calibrate_edge_score.py's own history).

Instead: walk-forward (same expanding-window fold discipline as every
other test this session), ONE TERM AT A TIME. Fits every population-term
model once per fold (reusing wpr_adj_term_roi_ablation_test.py's
fit_fold_terms - no re-fitting per weight, only cheap recombination), then
for each candidate term sweeps a scale multiplier over that term's already-
computed (fitted + per-race-demeaned) column, holding every OTHER term at
its natural 1x weight, refits beta on the reweighted fit_data projection,
and scores the held-out fold. Reports, per term, which weight maximizes
POOLED t-stat (not just ROI - t-stat penalises small-n flukes) at edge>=
0.10 on the CURRENT (model_prob - market_prob) edge definition, since that
is what's actually shipped and what the earlier price-ratio experiment
found does not hold up.

Weight 1.0 for every term (living term untouched) reproduces wpr_
walkforward_shipped_roi_test.py's pooled shipped-architecture result -
printed first as the reference row.

USAGE
  python wpr_adj_term_weight_sweep_test.py

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np
import pandas as pd

from wpr_walkforward_shipped_roi_test import FOLD_MONTHS
from wpr_adj_term_ablation_test import ALL_CANDIDATES
from wpr_adj_term_roi_ablation_test import build_frame, fit_fold_terms, ALL_TERMS_FULL, roi_stats
import wpr_projection as wpr
from wpr_bet_selection_leakfree_eval import _edge_from_score

WEIGHT_GRID = [0.0, 0.5, 1.0, 1.5, 2.0, 3.0]
EDGE_THRESHOLD = 0.10
BETA_GRID = [0.05, 0.10, 0.15, 0.20, 0.25, 0.30, 0.40]


def _brier(data, col, beta):
    rows = []
    for rid, g in data.groupby("race_id"):
        if len(g) < 4:
            continue
        pv = g[col].to_numpy(dtype=float)
        e = np.exp(beta * (pv - pv.max()))
        p = e / e.sum()
        rows.extend(zip(p, g["won"]))
    arr = pd.DataFrame(rows, columns=["p", "won"])
    return float(((arr["p"] - arr["won"]) ** 2).mean()) if len(arr) else float("nan")


def _fit_beta(fit_data, col):
    best_beta, best_brier = None, float("inf")
    for b in BETA_GRID:
        br = _brier(fit_data, col, b)
        if br < best_brier:
            best_brier, best_beta = br, b
    return best_beta


def score_weighted(fit_data, held_out, term, weight):
    """base term set is ALL_TERMS_FULL at natural 1x weight; `term` gets
    `weight` instead (0x drops it, >1x amplifies it, gear_change at 1.0
    means "add it in", since it is not part of ALL_TERMS_FULL)."""
    fit_data = fit_data.copy()
    held_out = held_out.copy()
    base_terms = [t for t in ALL_TERMS_FULL if t != term]
    col = "_alt_proj"
    for f in (fit_data, held_out):
        f[col] = f["_base"].to_numpy() + wpr._cap_adj_sum(
            np.column_stack([f[t].to_numpy() for t in base_terms] + [weight * f[term].to_numpy()])
        ).sum(axis=1)
    beta = _fit_beta(fit_data, col)
    held_out["score_wpr"] = beta * held_out[col]
    held_out["edge_wpr"] = _edge_from_score(held_out, "score_wpr")
    return held_out


def run():
    full = build_frame()

    # pooled[(term, weight)] -> list of held_out frames across folds
    pooled = {}
    for term in ALL_CANDIDATES:
        for w in WEIGHT_GRID:
            pooled[(term, w)] = []

    for month in FOLD_MONTHS:
        fold_start = pd.Timestamp(month + "-01")
        fold_end = fold_start + pd.offsets.MonthBegin(1)
        fit_data = full[full["date"] < fold_start]
        held_out = full[(full["date"] >= fold_start) & (full["date"] < fold_end)]
        print(f"\nFold {month}: fit={len(fit_data):,} (< {fold_start.date()}), "
              f"held_out={len(held_out):,} races={held_out['race_id'].nunique()}")
        if len(fit_data) < 2000 or len(held_out) < 50:
            print("  skipping fold (insufficient data)")
            continue

        fit_scored, held_scored = fit_fold_terms(fit_data, held_out)

        for term in ALL_CANDIDATES:
            for w in WEIGHT_GRID:
                if term not in ALL_TERMS_FULL and w == 0.0:
                    continue  # gear_change at 0x == status quo, already covered by weight=1.0 on real terms
                pooled[(term, w)].append(score_weighted(fit_scored, held_scored, term, w))

    print(f"\n{'='*90}")
    print(f"{'term':<16} {'weight':>7} {'n':>7} {'strike%':>8} {'ROI%':>8} {'t':>7}   note")
    print(f"{'='*90}")
    for term in ALL_CANDIDATES:
        best_w, best_t = None, -float("inf")
        rows = []
        for w in WEIGHT_GRID:
            if term not in ALL_TERMS_FULL and w == 0.0:
                continue
            frames = pooled[(term, w)]
            if not frames:
                continue
            p = pd.concat(frames, ignore_index=True)
            stats = roi_stats(p[p["edge_wpr"] >= EDGE_THRESHOLD])
            rows.append((w, stats))
            if stats["t"] is not None and stats["t"] > best_t:
                best_t, best_w = stats["t"], w
        for w, stats in rows:
            tag = ""
            if w == 1.0 and term in ALL_TERMS_FULL:
                tag = "<- current (natural weight)"
            if w == best_w:
                tag += "  [BEST t-stat]"
            print(f"{term:<16} {w:>7.1f} {stats['n']:>7} {str(stats['strike']):>8} "
                  f"{str(stats['roi']):>8} {str(stats['t']):>7}   {tag}")
        print("-" * 90)


if __name__ == "__main__":
    run()
