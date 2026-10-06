"""
wpr_tiered_base_roi_test.py - "what about ROI now?" follow-up to shipping
the tiered multi-signal base regression (PR #173): MAE improved (6.7503
-> 6.6558) but standalone win strike rate/avg margin moved slightly the
WRONG way (24.5%->24.0%, 2.85L->2.92L). This checks the thing that
actually matters for betting - edge-vs-market ROI, the same methodology
used throughout this session (wpr_alpha_08_proper_validation.py and
successors) - for the OLD (alpha=0.40 fixed 2-signal blend, single global
calibration slope, matching what was actually shipped before PR #173) vs
NEW (tiered wpr_nett/ewm5/track_wpr/best3 regression, PR #173) base.

METHOD: K=4 chronological folds. Each fold refits, on training data only:
  - population-level ADJ_TERMS lookups (track_barrier, closing_merit,
    trainer_merit, jockey_merit) - same leak-free convention as every
    other script in this series.
  - OLD base: single global OLS calibration (target ~ raw alpha=0.40
    blend) - matches current production _calibrate_base exactly (NOT the
    piecewise calibration some earlier scripts in this series used before
    it was removed).
  - NEW base: the same 3-tier regression PR #173 shipped (minimal: wpr_
    nett+ewm5, track: +track_wpr, full: +best3), each tier's own weights
    refit on training data only (not reusing the shipped fixed constants,
    to avoid any of the held-out fold leaking into its own fit).
Both then get the SAME per-fold ADJ_TERMS treatment and the same beta
grid search (fit on training fold's own resulting wprp_proj), so the
ONLY thing that differs between OLD and NEW is the base itself.

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np
import pandas as pd
from sklearn.linear_model import LinearRegression

import wpr_projection as wpr
from wpr_own_pace_backtest import add_track_barrier
from wpr_trainer_jockey_adj_strike_eval import add_closing_merit, fit_bucket_lookup, apply_bucket
from wpr_bet_selection_post_retrain import report
from wpr_alpha_08_leak_corrected_validation import build_full, fix_wpr_nett_leak
from wpr_signal_strike_margin_combo_test import merge_margin, strike_and_margin

N_FOLDS = 4
BETA_GRID = [0.05, 0.10, 0.15, 0.20, 0.25, 0.30, 0.40]
PRICE_CAP = 26.0
EDGE_THRESHOLDS = [0.05, 0.10, 0.20]
OLD_ALPHA = 0.40


def fit_ols_1d(x, y):
    slope, intercept = np.polyfit(x, y, 1)
    return intercept, slope


def old_base(train, test):
    """Shipped-before-PR#173 base: fixed alpha=0.40 wpr_nett/ewm3 blend,
    single global calibration slope refit per fold (matches current
    _calibrate_base exactly, not the piecewise calibration some earlier
    scripts in this series used before it was removed)."""
    train_raw = OLD_ALPHA * train["wpr_nett"] + (1 - OLD_ALPHA) * train["ewm3"]
    test_raw = OLD_ALPHA * test["wpr_nett"] + (1 - OLD_ALPHA) * test["ewm3"]
    intercept, slope = fit_ols_1d(train_raw.to_numpy(), train["target"].to_numpy())
    return intercept + slope * train_raw, intercept + slope * test_raw


def new_base(train, test):
    """PR #173's tiered regression, refit fresh per fold (not the shipped
    fixed constants) so no held-out fold leaks into its own tier fit."""
    def fit_tier(cols):
        sub = train.dropna(subset=list(cols) + ["target"])
        model = LinearRegression().fit(sub[list(cols)].to_numpy(), sub["target"].to_numpy())
        return model

    m_min = fit_tier(["wpr_nett", "ewm5"])
    m_trk = fit_tier(["wpr_nett", "ewm5", "track_wpr"])
    m_full = fit_tier(["wpr_nett", "ewm5", "track_wpr", "best3"])

    def predict(frame):
        has_track = frame["track_wpr"].notna()
        has_best3 = frame["best3"].notna()
        pred = pd.Series(np.nan, index=frame.index, dtype=float)
        m_full_mask = has_track & has_best3
        if m_full_mask.any():
            pred.loc[m_full_mask] = m_full.predict(frame.loc[m_full_mask, ["wpr_nett", "ewm5", "track_wpr", "best3"]].to_numpy())
        m_trk_mask = has_track & ~has_best3
        if m_trk_mask.any():
            pred.loc[m_trk_mask] = m_trk.predict(frame.loc[m_trk_mask, ["wpr_nett", "ewm5", "track_wpr"]].to_numpy())
        m_min_mask = ~has_track
        if m_min_mask.any():
            pred.loc[m_min_mask] = m_min.predict(frame.loc[m_min_mask, ["wpr_nett", "ewm5"]].to_numpy())
        return pred

    return predict(train), predict(test)


def fit_and_score(train, test, base_fn, label):
    train = train.copy()
    test = test.copy()
    add_track_barrier(train, [train, test])
    add_closing_merit([train, test], train["date"].max())
    edges_t, lookup_t = fit_bucket_lookup(train, "trainer_win_pct_365d")
    edges_j, lookup_j = fit_bucket_lookup(train, "jockey_win_pct_90d")
    apply_bucket(train, "trainer_win_pct_365d", edges_t, lookup_t, "trainer_merit")
    apply_bucket(train, "jockey_win_pct_90d", edges_j, lookup_j, "jockey_merit")
    apply_bucket(test, "trainer_win_pct_365d", edges_t, lookup_t, "trainer_merit")
    apply_bucket(test, "jockey_win_pct_90d", edges_j, lookup_j, "jockey_merit")

    train_base, test_base = base_fn(train, test)
    train["_base_cand"] = train_base
    test["_base_cand"] = test_base

    for f in (train, test):
        f["adj_total"] = wpr._cap_adj_sum(f[wpr.ADJ_TERMS].to_numpy()).sum(axis=1) * wpr._CALIB_ADJ_SLOPE
        f["wprp_proj_cand"] = f["_base_cand"] + f["adj_total"]

    best_beta, best_brier = 0.15, float("inf")
    for b in BETA_GRID:
        rows = []
        for rid, g in train.groupby("race_id"):
            if len(g) < 4:
                continue
            pv = g["wprp_proj_cand"].to_numpy(dtype=float)
            e = np.exp(b * (pv - pv.max()))
            p = e / e.sum()
            rows.extend(zip(p, g["won"]))
        arr = pd.DataFrame(rows, columns=["p", "won"])
        brier = float(((arr["p"] - arr["won"]) ** 2).mean()) if len(arr) else float("inf")
        if brier < best_brier:
            best_brier, best_beta = brier, b

    def _prob(g):
        pv = g["wprp_proj_cand"].to_numpy(dtype=float)
        e = np.exp(best_beta * (pv - pv.max()))
        return pd.Series(e / e.sum(), index=g.index)

    test["model_prob"] = test.groupby("race_id", group_keys=False).apply(_prob)

    def _edge(g):
        p_mkt = (1.0 / g["sp"]) / (1.0 / g["sp"]).sum()
        return g["model_prob"] - p_mkt

    test["edge"] = test.groupby("race_id", group_keys=False).apply(_edge)

    mae = float((test["target"] - test["_base_cand"]).abs().mean())
    return test, mae, best_beta


def run():
    full = build_full()
    full = fix_wpr_nett_leak(full)
    full = merge_margin(full)
    non_pop_terms = [t for t in wpr.ADJ_TERMS
                     if t not in ("track_barrier", "closing_merit", "trainer_merit", "jockey_merit")]
    full = full.dropna(subset=["target", "career_avg"] + non_pop_terms +
                        ["barrier", "field_size", "track", "cur_distance"])
    sp = pd.to_numeric(full["fixed_win_price"], errors="coerce")
    sp_fallback = pd.to_numeric(full["starting_price_sp"], errors="coerce")
    full["sp"] = sp.fillna(sp_fallback)
    full = full.dropna(subset=["sp"])
    full = full[full["sp"] > 1.0]
    full = full.sort_values("date").reset_index(drop=True)
    print(f"Scoped rows: {len(full):,}")

    fold_edges = np.array_split(np.arange(len(full)), N_FOLDS)
    full["_fold"] = -1
    for i, idx in enumerate(fold_edges):
        full.loc[idx, "_fold"] = i

    for label, base_fn in [("OLD: wpr_nett*0.40 + ewm3*0.60 (single global calib, shipped before PR #173)", old_base),
                            ("NEW: tiered wpr_nett/ewm5/track_wpr/best3 (PR #173, shipped)", new_base)]:
        print(f"\n{'='*100}\n{label}\n{'='*100}")
        fold_maes = []
        all_test = []
        for i in range(N_FOLDS):
            test = full[full["_fold"] == i]
            train = full[full["_fold"] != i]
            scored, mae, beta = fit_and_score(train, test, base_fn, label)
            fold_maes.append(mae)
            all_test.append(scored)
            print(f"  fold {i}: MAE={mae:.4f}  beta={beta}")

        pooled = pd.concat(all_test, ignore_index=True)
        print(f"\n  avg MAE across folds: {np.mean(fold_maes):.4f}")
        strike, margin, n = strike_and_margin(pooled, "wprp_proj_cand")
        print(f"  top-pick win strike (pooled held-out): {strike*100:.1f}%  avg margin: {margin:.2f}L  n={n:,}")
        print(f"  edge-vs-market ROI (pooled across all {N_FOLDS} held-out folds):")
        for thr in EDGE_THRESHOLDS:
            sub = pooled[(pooled["edge"] >= thr) & (pooled["sp"] <= PRICE_CAP)]
            report(sub, f"edge>={thr:.2f}, price<=${PRICE_CAP:.0f}")

    print("\nSame caveats as always: leak-free-for-wpr_nett K-fold, but one dataset/attempt.")


if __name__ == "__main__":
    run()
