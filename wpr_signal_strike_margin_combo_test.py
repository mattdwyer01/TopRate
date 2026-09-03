"""
wpr_signal_strike_margin_combo_test.py - extends wpr_best_anchor_signal_
test.py's standalone-signal comparison (which only looked at held-out
MAE) with two more direct, easier-to-interpret metrics, then searches
combinations (weighted multiples) of the standalone signals for anything
that beats the best single signal or the shipped wpr_nett/ewm3 alpha=0.40
blend.

NEW METRICS (both computed on the RAW signal, no fitting involved - "which
horse has the highest already-causal, point-in-time feature value in this
race" needs no calibration, only calibration-invariant ranking):
  - win strike rate of the top-rated horse: for each race, take the horse
    with the highest value of the signal, and report how often that horse
    actually won.
  - avg margin of the winner from the top-rated horse: toprate_runners.csv's
    margin_finish is negative for the winner (its own winning margin over
    2nd) and positive for every other runner (lengths behind the winner).
    This treats the top-rated horse's own margin_finish as 0 when it IS the
    winner (no gap) and as its raw beaten-margin otherwise - i.e. how many
    lengths behind the winner the model's top pick finished on average.

Same leak-corrected build as wpr_alpha_08_leak_corrected_validation.py
(wpr_nett re-merged from toprate_runners.csv by (horse, date, race_id), not
build_training_frame()'s contaminated run_id merge) and the same K=4-fold
discipline for MAE (fresh OLS calibration fit on training folds only, never
reused across a different signal/combination).

COMBINATION SEARCH: two parts -
  1. Every pair of the 6 standalone signals, weight grid 0.1-0.9 on the
     first-named signal (10% steps), best weight per pair reported (not
     just the shipped alpha=0.4-style midpoint).
  2. A few equal-weight multi-signal combinations (top3/top4/all6) for
     comparison against the pairwise search.

NO EM DASHES policy: hyphens only in this file.
"""
from itertools import combinations

import numpy as np
import pandas as pd

from wpr_alpha_08_leak_corrected_validation import build_full, fix_wpr_nett_leak

N_FOLDS = 4
STANDALONE_SIGNALS = ["wpr_nett", "ewm3", "avg_last3", "career_avg", "recent5_max", "best3"]
PAIR_WEIGHT_GRID = [round(w, 1) for w in np.arange(0.1, 1.0, 0.1)]
MULTI_EQUAL_COMBOS = [
    ("top3 equal (ewm3/avg_last3/wpr_nett)", ["ewm3", "avg_last3", "wpr_nett"]),
    ("top4 equal (+best3)", ["ewm3", "avg_last3", "wpr_nett", "best3"]),
    ("all6 equal", STANDALONE_SIGNALS),
]


def fit_ols(x, y):
    mask = x.notna() & y.notna()
    if mask.sum() < 30:
        return 0.0, 1.0
    slope, intercept = np.polyfit(x[mask], y[mask], 1)
    return intercept, slope


def mae_kfold(frame, raw_col):
    fold_maes = []
    for i in range(N_FOLDS):
        train = frame[frame["_fold"] != i]
        test = frame[frame["_fold"] == i]
        intercept, slope = fit_ols(train[raw_col], train["target"])
        pred = intercept + slope * test[raw_col]
        mask = test["target"].notna() & pred.notna()
        fold_maes.append(float((test["target"][mask] - pred[mask]).abs().mean()))
    return float(np.mean(fold_maes))


def strike_and_margin(frame, raw_col):
    sub = frame.dropna(subset=[raw_col, "won", "margin_finish"])
    if sub.empty:
        return float("nan"), float("nan"), 0
    top_idx = sub.groupby("race_id")[raw_col].idxmax()
    tops = sub.loc[top_idx]
    win_strike = float(tops["won"].mean())
    beaten = np.where(tops["won"] == 1, 0.0, tops["margin_finish"])
    avg_margin = float(np.mean(beaten))
    return win_strike, avg_margin, len(tops)


def weighted_raw(frame, weights):
    active = {k: v for k, v in weights.items() if v > 0}
    cols = list(active.keys())
    mask = frame[cols].notna().all(axis=1)
    raw = pd.Series(np.nan, index=frame.index, dtype=float)
    total = sum(active.values())
    combo = sum(active[c] * frame.loc[mask, c] for c in cols) / total
    raw.loc[mask] = combo
    return raw


def merge_margin(full, runners_csv="toprate_runners.csv"):
    """Brings in the actual finishing margin (margin_finish) by (horse,
    date), the same conservative convention as merge_won_by_horse_date:
    only resulted, non-scratched rows, ambiguous same-day name clashes
    dropped rather than risking a wrong match."""
    tr = pd.read_csv(runners_csv, dtype={"race_id": str}, low_memory=False,
                      usecols=["horse", "date", "race_id", "margin_finish", "resulted", "scratched"])
    tr["date"] = pd.to_datetime(tr["date"], errors="coerce")
    tr["resulted"] = pd.to_numeric(tr["resulted"], errors="coerce")
    tr["scratched"] = pd.to_numeric(tr["scratched"], errors="coerce")
    tr = tr[(tr["resulted"] == 1) & (tr["scratched"] != 1)].dropna(subset=["date"])
    tr = tr.drop_duplicates(subset=["horse", "date"], keep=False)
    full = full.merge(tr[["horse", "date", "margin_finish"]], on=["horse", "date"], how="left")
    return full


def run():
    full = build_full()
    full = fix_wpr_nett_leak(full)
    full = merge_margin(full)
    full = full.dropna(subset=["target"]).sort_values("date").reset_index(drop=True)
    print(f"Scoped rows: {len(full):,}  (margin_finish coverage: {full['margin_finish'].notna().sum():,})")

    sp = pd.to_numeric(full["fixed_win_price"], errors="coerce")
    sp_fallback = pd.to_numeric(full["starting_price_sp"], errors="coerce")
    full["sp"] = sp.fillna(sp_fallback)
    full["_inv_sp"] = np.where(full["sp"] > 1.0, 1.0 / full["sp"], np.nan)
    mkt_strike, mkt_margin, mkt_n = strike_and_margin(full, "_inv_sp")
    print(f"\nMARKET FAVOURITE BENCHMARK (highest implied probability, i.e. lowest price, per race):\n"
          f"  win strike={mkt_strike*100:.1f}%  avg margin={mkt_margin:.2f}L  n={mkt_n:,}\n"
          f"  (no MAE - the market doesn't project a WPR-scale number, only a rank)")

    fold_edges = np.array_split(np.arange(len(full)), N_FOLDS)
    full["_fold"] = -1
    for i, idx in enumerate(fold_edges):
        full.loc[idx, "_fold"] = i

    print(f"\n{'='*100}\nSTANDALONE SIGNALS (K={N_FOLDS}-fold MAE, plus win strike rate + avg beaten "
          f"margin of the top-rated horse)\n{'='*100}")
    print(f"  {'signal':<14} {'avg MAE':>9} {'win strike':>11} {'avg margin':>12} {'n(races)':>9}")
    standalone_results = {}
    for sig in STANDALONE_SIGNALS:
        mae = mae_kfold(full, sig)
        strike, margin, n = strike_and_margin(full, sig)
        standalone_results[sig] = mae
        print(f"  {sig:<14} {mae:>9.4f} {strike*100:>10.1f}% {margin:>11.2f}L {n:>9,}")

    print(f"\n{'='*100}\nPAIRWISE COMBINATIONS (best weight per pair on a 10% grid, weight shown is "
          f"the share on the first-named signal)\n{'='*100}")
    print(f"  {'pair':<30} {'best wt':>8} {'avg MAE':>9} {'win strike':>11} {'avg margin':>12} {'n(races)':>9}")
    combo_rows = []
    for a, b in combinations(STANDALONE_SIGNALS, 2):
        best_mae, best_w = float("inf"), None
        for w in PAIR_WEIGHT_GRID:
            full["_raw_tmp"] = weighted_raw(full, {a: w, b: 1 - w})
            mae = mae_kfold(full, "_raw_tmp")
            if mae < best_mae:
                best_mae, best_w = mae, w
        full["_raw_tmp"] = weighted_raw(full, {a: best_w, b: 1 - best_w})
        strike, margin, n = strike_and_margin(full, "_raw_tmp")
        label = f"{a}*{best_w:.1f} + {b}*{1-best_w:.1f}"
        combo_rows.append((label, best_mae, strike, margin, n))
        print(f"  {label:<30} {best_w:>7.1f} {best_mae:>9.4f} {strike*100:>10.1f}% {margin:>11.2f}L {n:>9,}")

    print(f"\n{'='*100}\nEQUAL-WEIGHT MULTI-SIGNAL COMBINATIONS\n{'='*100}")
    print(f"  {'combo':<40} {'avg MAE':>9} {'win strike':>11} {'avg margin':>12} {'n(races)':>9}")
    for label, sigs in MULTI_EQUAL_COMBOS:
        full["_raw_tmp"] = weighted_raw(full, {s: 1.0 for s in sigs})
        mae = mae_kfold(full, "_raw_tmp")
        strike, margin, n = strike_and_margin(full, "_raw_tmp")
        combo_rows.append((label, mae, strike, margin, n))
        print(f"  {label:<40} {mae:>9.4f} {strike*100:>10.1f}% {margin:>11.2f}L {n:>9,}")

    best_overall = min(combo_rows, key=lambda r: r[1])
    best_standalone = min(standalone_results, key=standalone_results.get)
    print(f"\nBest standalone signal: {best_standalone} (avg MAE {standalone_results[best_standalone]:.4f})")
    print(f"Best combination overall by MAE: {best_overall[0]} (avg MAE {best_overall[1]:.4f})")
    print("\nSame caveats as always: leak-free-for-wpr_nett K-fold, but one dataset/attempt. Win strike "
          "rate and avg margin need no fitting, but are still one dataset's realised outcomes, not a "
          "guarantee for a future period.")


if __name__ == "__main__":
    run()
