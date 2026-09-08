"""wpr_adj_term_combo_search_test.py - can a COMBINATION of ADJ_TERM
weights (not just one at a time) turn wpr_price into a profitable overlay
signal? (user follow-up, Sep 2026, after wpr_adj_term_weight_sweep_test.py
found no single term's weight change rescues profitability post the
wpr_nett future-leak fix - see wpr_projection.py's build_training_frame
docstring for that bug).

WHY NOT A FULL JOINT GRID
  ~12 candidate terms x 6 weight options each is 6^12 combinations -
  computationally impossible, and even a feasible subset of it would be a
  textbook overfitting trap: searching many free parameters against a
  noisy ROI objective reliably finds a "profitable" combination that is
  really just the best of many random-looking draws (this session's own
  running theme - see wpr_walkforward_shipped_roi_test.py's docstring on
  calibrate_edge_score.py's history, and the wpr_nett leak that inflated
  every prior backtest this session before today's fix).

METHOD: greedy coordinate ascent with a genuine inner train/validation
split, so weight SELECTION never sees the fold being evaluated.
  Per outer walk-forward fold (fit=strictly before fold_start, held_out=
  that month, same as every other test this session):
    1. Split fit_data itself at its own 75th-percentile date into
       inner_fit (older 75%) and inner_val (newer 25%).
    2. Fit population-term models on inner_fit ONLY, score inner_val
       (leak-free relative to inner_val, and inner_val itself is still
       strictly before the outer held_out fold - two layers of "no
       peeking").
    3. Greedy search on inner_val: start every term at its natural 1.0x
       weight. Each round, try every (term, candidate weight) change
       against the CURRENT best combination, keep whichever single change
       improves inner_val's t-stat at price_edge>=0.20 (beta=0.3, the
       less-bad of the two live candidates per wpr_simple_price_edge_
       walkforward_test.py) the most. Stop when a round finds no
       improving move, or after MAX_ROUNDS. t-stat (not raw ROI) is the
       selection criterion specifically because it penalises small-n
       flukes - the same discipline used everywhere else this session.
    4. Refit population-term models on the FULL fit_data (standard
       practice: select hyperparameters via inner validation, refit on
       all available prior data, then evaluate once on the real held-out
       fold) and score the outer held_out fold using the SELECTED
       combination - this is the only number that counts as a genuine
       out-of-sample result.
  Pools the outer held-out results across folds and reports both the
  natural (all-1.0x) baseline and the selected combination's performance,
  side by side, across the full threshold grid - plus the per-fold
  selected combinations themselves, so a combination that is wildly
  different fold to fold (a sign of overfitting the inner validation
  noise) is visible rather than hidden behind a pooled average.

USAGE
  python wpr_adj_term_combo_search_test.py

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np
import pandas as pd

from wpr_walkforward_shipped_roi_test import FOLD_MONTHS
from wpr_adj_term_ablation_test import ALL_CANDIDATES
from wpr_adj_term_roi_ablation_test import build_frame, fit_fold_terms, ALL_TERMS_FULL, roi_stats
import wpr_projection as wpr

WEIGHT_GRID = [0.0, 0.5, 1.0, 1.5, 2.0, 3.0]
BETA = 0.3
SELECT_THRESHOLD = 0.20
REPORT_THRESHOLDS = [0.0, 0.10, 0.20, 0.30, 0.50, 0.75, 1.00]
MAX_ROUNDS = 4
MIN_N_FOR_SELECTION = 100


def blend_price_per_race(df, proj_col, beta):
    out = np.full(len(df), np.nan)
    proj = df[proj_col].to_numpy(dtype=float)
    for rid, idx in df.groupby("race_id").indices.items():
        idx = np.asarray(idx)
        pv = proj[idx]
        e = np.exp(beta * (pv - pv.max()))
        prob = e / e.sum()
        out[idx] = np.minimum(1.0 / prob, 999.0)
    return out


def score_with_weights(held_out, weights, beta=BETA):
    """weights: {term: multiplier}. Missing terms default to 1.0 (natural)
    if in ALL_TERMS_FULL, or 0.0 (excluded) if not (gear_change)."""
    held_out = held_out.copy()
    term_arrays = []
    for t in ALL_TERMS_FULL:
        w = weights.get(t, 1.0)
        term_arrays.append(w * held_out[t].to_numpy())
    if weights.get("gear_change", 0.0) != 0.0:
        term_arrays.append(weights["gear_change"] * held_out["gear_change"].to_numpy())
    held_out["_combo_proj"] = held_out["_base"].to_numpy() + wpr._cap_adj_sum(
        np.column_stack(term_arrays)).sum(axis=1)
    held_out["blend_price"] = blend_price_per_race(held_out, "_combo_proj", beta)
    held_out["price_edge_pct"] = held_out["sp"] / held_out["blend_price"] - 1.0
    return held_out


def objective(scored, threshold=SELECT_THRESHOLD):
    sub = scored[scored["price_edge_pct"] >= threshold]
    stats = roi_stats(sub)
    if stats["n"] is None or stats["n"] < MIN_N_FOR_SELECTION or stats["t"] is None:
        return -999.0
    return stats["t"]


def greedy_search(inner_val):
    weights = {t: 1.0 for t in ALL_TERMS_FULL}
    weights["gear_change"] = 0.0
    best_obj = objective(score_with_weights(inner_val, weights))
    print(f"    inner_val natural baseline t-stat: {best_obj:.2f}")
    for round_i in range(MAX_ROUNDS):
        best_move = None
        for term in ALL_CANDIDATES:
            for w in WEIGHT_GRID:
                if weights.get(term, 1.0 if term in ALL_TERMS_FULL else 0.0) == w:
                    continue
                trial = dict(weights)
                trial[term] = w
                obj = objective(score_with_weights(inner_val, trial))
                if obj > best_obj:
                    best_obj = obj
                    best_move = (term, w)
        if best_move is None:
            print(f"    round {round_i+1}: no improving move, stopping")
            break
        term, w = best_move
        weights[term] = w
        print(f"    round {round_i+1}: set {term} -> {w}x  (inner_val t-stat now {best_obj:.2f})")
    return weights, best_obj


def run():
    full = build_frame()

    natural_bets, combo_bets = [], []
    fold_combos = {}

    for month in FOLD_MONTHS:
        fold_start = pd.Timestamp(month + "-01")
        fold_end = fold_start + pd.offsets.MonthBegin(1)
        fit_data = full[full["date"] < fold_start]
        held_out = full[(full["date"] >= fold_start) & (full["date"] < fold_end)]
        print(f"\n{'#'*90}\nFold {month}: fit={len(fit_data):,} (< {fold_start.date()}), "
              f"held_out={len(held_out):,} races={held_out['race_id'].nunique()}")
        if len(fit_data) < 4000 or len(held_out) < 50:
            print("  skipping fold (insufficient data)")
            continue

        inner_cutoff = fit_data["date"].quantile(0.75)
        inner_fit = fit_data[fit_data["date"] < inner_cutoff]
        inner_val = fit_data[fit_data["date"] >= inner_cutoff]
        print(f"  inner_fit={len(inner_fit):,} (< {inner_cutoff.date()}), inner_val={len(inner_val):,}")
        if len(inner_fit) < 2000 or len(inner_val) < 500:
            print("  skipping fold (insufficient data for inner split)")
            continue

        print("  fitting terms on inner_fit, scoring inner_val for weight search...")
        _inner_fit_scored, inner_val_scored = fit_fold_terms(inner_fit, inner_val)
        weights, sel_t = greedy_search(inner_val_scored)
        fold_combos[month] = (weights, sel_t)
        print(f"  SELECTED combination for {month}: "
              f"{ {k: v for k, v in weights.items() if v != (1.0 if k in ALL_TERMS_FULL else 0.0)} }")

        print("  refitting terms on full fit_data for the real held-out evaluation...")
        _fit_scored, held_scored = fit_fold_terms(fit_data, held_out)
        natural_weights = {t: 1.0 for t in ALL_TERMS_FULL}
        natural_bets.append(score_with_weights(held_scored, natural_weights))
        combo_bets.append(score_with_weights(held_scored, weights))

    print(f"\n{'='*90}\nPER-FOLD SELECTED COMBINATIONS (inner-validation only, never saw the held-out fold)\n{'='*90}")
    for month, (weights, sel_t) in fold_combos.items():
        changed = {k: v for k, v in weights.items() if v != (1.0 if k in ALL_TERMS_FULL else 0.0)}
        print(f"  {month}: inner_val t-stat={sel_t:.2f}  changes={changed}")

    natural_pooled = pd.concat(natural_bets, ignore_index=True)
    combo_pooled = pd.concat(combo_bets, ignore_index=True)

    print(f"\n{'='*90}\nOUT-OF-SAMPLE HELD-OUT RESULT (beta={BETA})\n{'='*90}")
    print(f"{'variant':<12} {'threshold':>10} {'n':>7} {'strike%':>8} {'ROI%':>8} {'t':>7}")
    for label, pooled in [("natural", natural_pooled), ("combo", combo_pooled)]:
        for thr in REPORT_THRESHOLDS:
            sub = pooled[pooled["price_edge_pct"] >= thr]
            stats = roi_stats(sub)
            print(f"{label:<12} {thr:>10.2f} {stats['n']:>7} {str(stats['strike']):>8} "
                  f"{str(stats['roi']):>8} {str(stats['t']):>7}")
        print("-" * 90)


if __name__ == "__main__":
    run()
