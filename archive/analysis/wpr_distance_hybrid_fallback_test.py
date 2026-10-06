"""
wpr_distance_hybrid_fallback_test.py - own_distance currently uses EXACT
distance match only (Aug 2026, replaced a +/-10% band that lost head-to-
head: exact 5.9049 vs band's 5.9149 held-out MAE, despite covering fewer
rows). But that test compared "band for everyone" vs "exact for
everyone" - it never tested the HYBRID: exact match when available
(unchanged, already the better choice there), falling back to a band
ONLY for the 33.2% of rows with no exact match at all (which currently
get a flat 0.0 adjustment, not "no signal available" - genuine
information is sitting unused: 92% of those rows already have a
+/-200m band match, via the existing distband_wpr/distband_n columns
build_features() already computes for a different candidate feature).

This directly answers the user's original question ("is exact distance
more reliable when the horse has ran the exact distance before, what's
the best methodology when it hasn't") - a hybrid can only help or be
neutral on the 66.8% of rows exact-match already covers (unchanged
there), so the only real question is whether the +/-200m band fallback
beats a flat 0.0 on the 33.2% it doesn't.

Does NOT yet address the harder, genuinely-out-of-range case (dist_edge
!= 0 - today's trip outside the horse's ever-proven min-max range
entirely) - that's a separate, harder problem (already diagnosed in
build_features' own dist_edge comment: held-out error climbs from 6.7
inside the proven range to 10.1 at 400m+ outside it) that a same-horse
band average can't help with by definition (there's no "nearby" run to
average). Scoped here to the achievable piece: the band fallback for
horses that HAVE run near today's trip, just not exactly at it.

METHOD: K=4 chronological folds. own_distance_hybrid is a pure per-horse
computation (already leak-free by construction - distband_wpr/distband_n
use only prior runs), so it needs no per-fold refit itself. What DOES
need the standard per-fold leak-free treatment: track_barrier/
closing_merit/trainer_merit/jockey_merit population lookups (fit on
training folds only, as always). Holds _CALIB_ADJ_SLOPE fixed at the
shipped 0.1791 for BOTH variants (isolating "does the hybrid distance
feature help" from the slope question, already separately tested and
found not to matter - wpr_joint_calib_kfold_test.py). Scores held-out
MAE, top-1 strike rate, and Summary-tab-style edge/ROI.

NO EM DASHES policy: hyphens only in this file.
"""
import pickle
from pathlib import Path

import numpy as np
import pandas as pd

import wpr_projection as wpr
from wpr_own_pace_backtest import add_base, add_track_barrier, merge_won_by_horse_date
from wpr_trainer_jockey_adj_strike_eval import (
    FORM_CSV, merge_trainer_jockey_by_horse_date, add_closing_merit,
    fit_bucket_lookup, apply_bucket, top1_strike_rate,
)
from wpr_bet_selection_post_retrain import report

CACHE_PATH = Path("/tmp/wpr_full_training_frame_cache.pkl")
N_FOLDS = 4
BETA_GRID = [0.05, 0.10, 0.15, 0.20, 0.25, 0.30, 0.40]
PRICE_CAP = 26.0
EDGE_THRESHOLDS = [0.05, 0.10, 0.20]


def build_full():
    """Same stale-"_base"-cache fix as every other test this session -
    see wpr_merit_slope_kfold_test.py's build_full() docstring."""
    form_mtime = Path(FORM_CSV).stat().st_mtime
    if CACHE_PATH.exists():
        with open(CACHE_PATH, "rb") as fh:
            cached_mtime, full = pickle.load(fh)
        if cached_mtime == form_mtime:
            print(f"Loaded cached training frame ({len(full):,} rows) - skipping the ~15-20 min rebuild.")
            full = full.drop(columns=["_base"], errors="ignore")
            return add_base(full)
        print("Cache is stale - rebuilding.")
    print("Rebuilding training frame (full history, this takes a while)...")
    full = wpr.build_training_frame(FORM_CSV, verbose=True, n_jobs=-1)
    full["date"] = pd.to_datetime(full["date"])
    full = merge_won_by_horse_date(full)
    full = merge_trainer_jockey_by_horse_date(full)
    with open(CACHE_PATH, "wb") as fh:
        pickle.dump((form_mtime, full), fh)
    return add_base(full)


def compute_hybrid(full):
    """own_distance unchanged where an exact match exists (dist_match_n
    >= 1). Where it doesn't, falls back to a shrunk (distband_wpr -
    career_avg) using distband_n as the shrinkage sample size - same
    _shrink() convention (n/(n+K), capped at _OWN_DELTA_CAP) every other
    own-history term already uses."""
    has_exact = full["dist_match_n"] >= 1
    band_delta = full["distband_wpr"] - full["career_avg"]
    band_n = full["distband_n"].fillna(0)
    shrunk = band_delta * band_n / (band_n + wpr._OWN_DELTA_SHRINK_K)
    shrunk = shrunk.clip(-wpr._OWN_DELTA_CAP, wpr._OWN_DELTA_CAP)
    band_fallback = shrunk.where(band_n >= 1, 0.0).fillna(0.0)
    return full["own_distance"].where(has_exact, band_fallback)


def fit_direction(fit_half, apply_frames, fit_cutoff):
    add_track_barrier(fit_half, apply_frames)
    add_closing_merit(apply_frames, fit_cutoff)
    edges_t, lookup_t = fit_bucket_lookup(fit_half, "trainer_win_pct_365d")
    edges_j, lookup_j = fit_bucket_lookup(fit_half, "jockey_win_pct_90d")
    for f in apply_frames:
        apply_bucket(f, "trainer_win_pct_365d", edges_t, lookup_t, "trainer_merit")
        apply_bucket(f, "jockey_win_pct_90d", edges_j, lookup_j, "jockey_merit")
        f["_base_calib"] = f["_base"].apply(wpr._calibrate_base)

        terms_shipped = f[wpr.ADJ_TERMS].copy()
        f["proj_shipped"] = f["_base_calib"] + wpr._cap_adj_sum(
            terms_shipped.to_numpy()).sum(axis=1) * wpr._CALIB_ADJ_SLOPE

        terms_hybrid = terms_shipped.copy()
        terms_hybrid["own_distance"] = compute_hybrid(f)
        f["proj_hybrid"] = f["_base_calib"] + wpr._cap_adj_sum(
            terms_hybrid.to_numpy()).sum(axis=1) * wpr._CALIB_ADJ_SLOPE


def best_beta(train, proj_col):
    best_b, best_brier = 0.15, float("inf")
    for b in BETA_GRID:
        rows = []
        for rid, g in train.groupby("race_id"):
            if len(g) < 4:
                continue
            pv = g[proj_col].to_numpy(dtype=float)
            e = np.exp(b * (pv - pv.max()))
            p = e / e.sum()
            rows.extend(zip(p, g["won"]))
        arr = pd.DataFrame(rows, columns=["p", "won"])
        brier = float(((arr["p"] - arr["won"]) ** 2).mean()) if len(arr) else float("inf")
        if brier < best_brier:
            best_brier, best_b = brier, b
    return best_b


def score(train, test, proj_col):
    b = best_beta(train, proj_col)

    def _prob(g):
        pv = g[proj_col].to_numpy(dtype=float)
        e = np.exp(b * (pv - pv.max()))
        return pd.Series(e / e.sum(), index=g.index)

    test = test.copy()
    test["model_prob"] = test.groupby("race_id", group_keys=False).apply(_prob)

    def _edge(g):
        p_mkt = (1.0 / g["sp"]) / (1.0 / g["sp"]).sum()
        return g["model_prob"] - p_mkt

    test["edge"] = test.groupby("race_id", group_keys=False).apply(_edge)
    mae = (test["target"] - test[proj_col]).abs().mean()
    strike, wins, n_top1 = top1_strike_rate(test, proj_col)
    return mae, strike, wins, n_top1, test


def run():
    full = build_full()
    non_pop_terms = [t for t in wpr.ADJ_TERMS
                     if t not in ("track_barrier", "closing_merit", "trainer_merit", "jockey_merit")]
    full = full.dropna(subset=["target", "_base", "career_avg", "distband_wpr", "distband_n"] +
                        non_pop_terms + ["barrier", "field_size", "track", "cur_distance",
                                         "trainer_win_pct_365d", "jockey_win_pct_90d", "sp"])
    full = full[full["sp"] > 1.0]
    full = full.sort_values("date").reset_index(drop=True)
    print(f"Scoped rows: {len(full):,}")
    no_exact = (full["dist_match_n"] == 0)
    print(f"Rows with no exact distance match (currently own_distance=0.0): {no_exact.sum():,} "
          f"({no_exact.mean()*100:.1f}%)")
    has_band = no_exact & (full["distband_n"] >= 1)
    print(f"Of those, rows with a usable +/-200m band fallback available: {has_band.sum():,} "
          f"({has_band.sum()/no_exact.sum()*100:.1f}% of the no-exact-match group)")

    fold_edges = np.array_split(np.arange(len(full)), N_FOLDS)
    full["_fold"] = -1
    for i, idx in enumerate(fold_edges):
        full.loc[idx, "_fold"] = i

    print(f"\n{'='*100}\nK={N_FOLDS}-fold: shipped (own_distance, exact-only) vs hybrid "
          f"(exact + band fallback)\n{'='*100}")

    ship_maes, hyb_maes = [], []
    ship_strikes, hyb_strikes = [], []
    ship_pooled, hyb_pooled = [], []
    for i in range(N_FOLDS):
        test = full[full["_fold"] == i].copy()
        train = full[full["_fold"] != i].copy()
        fit_direction(train, [train, test], train["date"].max())

        mae_s, strike_s, wins_s, ntop_s, scored_s = score(train, test, "proj_shipped")
        mae_h, strike_h, wins_h, ntop_h, scored_h = score(train, test, "proj_hybrid")
        ship_maes.append(mae_s); hyb_maes.append(mae_h)
        ship_strikes.append(strike_s); hyb_strikes.append(strike_h)
        ship_pooled.append(scored_s); hyb_pooled.append(scored_h)

        print(f"\n--- fold {i} held out (n={len(test):,}) ---")
        print(f"  MAE: shipped={mae_s:.4f}  hybrid={mae_h:.4f}  "
              f"({'better' if mae_h < mae_s else 'worse/same'})")
        print(f"  top-1 strike: shipped={wins_s}/{ntop_s}={strike_s:.2f}%  hybrid={wins_h}/{ntop_h}={strike_h:.2f}%  "
              f"({'better' if strike_h > strike_s else 'worse/same'})")

    print(f"\n{'='*100}\nSummary across all {N_FOLDS} folds\n{'='*100}")
    print(f"  avg MAE: shipped={np.mean(ship_maes):.4f}  hybrid={np.mean(hyb_maes):.4f}")
    print(f"  avg top-1 strike: shipped={np.mean(ship_strikes):.2f}%  hybrid={np.mean(hyb_strikes):.2f}%")
    print(f"  hybrid better on MAE in every fold: {all(h < s for h, s in zip(hyb_maes, ship_maes))}")
    print(f"  hybrid better on strike in every fold: {all(h > s for h, s in zip(hyb_strikes, ship_strikes))}")

    pooled_s = pd.concat(ship_pooled, ignore_index=True)
    pooled_h = pd.concat(hyb_pooled, ignore_index=True)
    print(f"\n  Summary-tab-style edge/ROI (pooled across all {N_FOLDS} held-out folds):")
    for thr in EDGE_THRESHOLDS:
        report(pooled_s[(pooled_s["edge"] >= thr) & (pooled_s["sp"] <= PRICE_CAP)], f"shipped, edge>={thr:.2f}")
        report(pooled_h[(pooled_h["edge"] >= thr) & (pooled_h["sp"] <= PRICE_CAP)], f"hybrid,  edge>={thr:.2f}")

    print("\nSame multiple-comparisons caveat as the other bet-selection scripts: treat any")
    print("row here as a hypothesis for a future walk-forward period, not a result to ship blindly.")


if __name__ == "__main__":
    run()
