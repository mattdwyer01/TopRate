"""
wpr_dist_edge_run_style_interaction_kfold_test.py - properly tests the
run_style interaction the scoping check in wpr_dist_edge_correction_
kfold_test.py flagged as "directionally sensible but too weak on its
own": does the model's out-of-range-distance bias correct differently
depending on running style, not just distance direction alone?

SCOPING PATTERN (found earlier): stepping UP in distance, residual
climbs from -1.23 (leaders, low run_style) to -0.08 (backmarkers/
closers, high run_style) across quartiles - closers are LESS over-
predicted stepping up. Stepping DOWN, the pattern reverses: residual
goes from -0.91 (leaders) to -1.94 (closers) - closers are MORE over-
predicted stepping down, leaders relatively less. Both patterns point
the SAME way once direction is accounted for: sign(dist_edge) * run_style
should be positively related to the residual either way (up + closer, or
down + leader, both push the interaction term up and both correspond to
a less-negative residual).

METHOD: K=4 chronological folds, scored on the dist_edge != 0 subset.
Fits resid ~ a + b1*sign(dist_edge) + b2*(sign(dist_edge)*(run_style -
0.5)) on training folds, via OLS (no separate shrinkage K - the
regression's own least-squares fit already regularises via sample size,
same as the first-up trial correction test). Compares THREE variants
held-out: (a) uncorrected (b) plain dist_edge-bucket correction (same as
wpr_dist_edge_correction_kfold_test.py, for reference) (c) this
direction+run_style interaction correction - to see whether the
interaction actually earns its complexity over the plain correction, not
just over doing nothing.

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
from wpr_bet_selection_post_retrain import merge_price_pfm, report

CACHE_PATH = Path("/tmp/wpr_full_training_frame_cache.pkl")
N_FOLDS = 4
DIST_EDGE_BINS = [-np.inf, -400, -200, -1, 1, 200, 400, np.inf]
CORRECTION_K = 30.0
BETA_GRID = [0.05, 0.10, 0.15, 0.20, 0.25, 0.30, 0.40]
PRICE_CAP = 26.0
EDGE_THRESHOLDS = [0.05, 0.10, 0.20]


def build_full():
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
    full = merge_price_pfm(full)
    with open(CACHE_PATH, "wb") as fh:
        pickle.dump((form_mtime, full), fh)
    return add_base(full)


def fit_direction(fit_half, apply_frames, fit_cutoff):
    add_track_barrier(fit_half, apply_frames)
    add_closing_merit(apply_frames, fit_cutoff)
    edges_t, lookup_t = fit_bucket_lookup(fit_half, "trainer_win_pct_365d")
    edges_j, lookup_j = fit_bucket_lookup(fit_half, "jockey_win_pct_90d")
    for f in apply_frames:
        apply_bucket(f, "trainer_win_pct_365d", edges_t, lookup_t, "trainer_merit")
        apply_bucket(f, "jockey_win_pct_90d", edges_j, lookup_j, "jockey_merit")
        f["_base_calib"] = f["_base"].apply(wpr._calibrate_base)
        f["adj_total"] = wpr._cap_adj_sum(f[wpr.ADJ_TERMS].to_numpy()).sum(axis=1) * wpr._CALIB_ADJ_SLOPE
        f["proj"] = f["_base_calib"] + f["adj_total"]
        f["resid"] = f["target"] - f["proj"]


def fit_plain_correction(train):
    d = train[train["dist_edge"] != 0]
    bucket = pd.cut(d["dist_edge"], DIST_EDGE_BINS)
    lookup = {}
    for b, g in d.groupby(bucket, observed=True):
        n = len(g)
        if n < 5:
            continue
        m = g["resid"].mean()
        lookup[b] = m * n / (n + CORRECTION_K)
    return lookup


def apply_plain_correction(frame, lookup):
    bucket = pd.cut(frame["dist_edge"], DIST_EDGE_BINS)
    return bucket.map(lookup).fillna(0.0)


def fit_interaction_correction(train_edge):
    sign = np.sign(train_edge["dist_edge"])
    interaction = sign * (train_edge["run_style"] - 0.5)
    X = np.column_stack([np.ones(len(train_edge)), sign, interaction])
    y = train_edge["resid"].to_numpy()
    coef, *_ = np.linalg.lstsq(X, y, rcond=None)
    return coef


def apply_interaction_correction(frame, coef):
    sign = np.sign(frame["dist_edge"])
    interaction = sign * (frame["run_style"] - 0.5)
    return coef[0] + coef[1] * sign + coef[2] * interaction


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
    strike, wins, n_top1 = top1_strike_rate(test, proj_col)
    return strike, wins, n_top1, test


def run():
    full = build_full()
    non_pop_terms = [t for t in wpr.ADJ_TERMS
                     if t not in ("track_barrier", "closing_merit", "trainer_merit", "jockey_merit")]
    full = full.dropna(subset=["target", "_base", "career_avg", "dist_edge", "run_style"] + non_pop_terms +
                        ["barrier", "field_size", "track", "cur_distance",
                         "trainer_win_pct_365d", "jockey_win_pct_90d", "sp"])
    full = full[full["sp"] > 1.0]
    full = full.sort_values("date").reset_index(drop=True)
    print(f"Scoped rows: {len(full):,}")
    print(f"dist_edge != 0 rows: {(full['dist_edge'] != 0).sum():,}")

    fold_edges = np.array_split(np.arange(len(full)), N_FOLDS)
    full["_fold"] = -1
    for i, idx in enumerate(fold_edges):
        full.loc[idx, "_fold"] = i

    print(f"\n{'='*100}\nK={N_FOLDS}-fold: uncorrected vs plain dist_edge correction vs "
          f"dist_edge x run_style interaction\n{'='*100}")

    mae_u, mae_p, mae_i = [], [], []
    strike_u, strike_p, strike_i = [], [], []
    pooled_u, pooled_p, pooled_i = [], [], []
    for i in range(N_FOLDS):
        test = full[full["_fold"] == i].copy()
        train = full[full["_fold"] != i].copy()
        fit_direction(train, [train, test], train["date"].max())

        test_edge = test[test["dist_edge"] != 0].copy()
        train_edge = train[train["dist_edge"] != 0].copy()
        if len(test_edge) < 30:
            print(f"  fold {i}: too few dist_edge!=0 rows, skipped")
            continue

        plain_lookup = fit_plain_correction(train)
        inter_coef = fit_interaction_correction(train_edge)

        for f in (train_edge, test_edge):
            f["proj_plain"] = f["proj"] + apply_plain_correction(f, plain_lookup)
            f["proj_inter"] = f["proj"] + apply_interaction_correction(f, inter_coef)

        m_u = (test_edge["target"] - test_edge["proj"]).abs().mean()
        m_p = (test_edge["target"] - test_edge["proj_plain"]).abs().mean()
        m_i = (test_edge["target"] - test_edge["proj_inter"]).abs().mean()
        mae_u.append(m_u); mae_p.append(m_p); mae_i.append(m_i)

        s_u, w_u, n_u, sc_u = score(train_edge, test_edge, "proj")
        s_p, w_p, n_p, sc_p = score(train_edge, test_edge, "proj_plain")
        s_i, w_i, n_i, sc_i = score(train_edge, test_edge, "proj_inter")
        strike_u.append(s_u); strike_p.append(s_p); strike_i.append(s_i)
        pooled_u.append(sc_u); pooled_p.append(sc_p); pooled_i.append(sc_i)

        print(f"\n--- fold {i} (dist_edge!=0 n={len(test_edge):,}) ---")
        print(f"  interaction coef (intercept, sign(dist_edge), sign*—run_style-0.5—): "
              f"{[round(c, 3) for c in inter_coef]}")
        print(f"  MAE:    uncorrected={m_u:.4f}  plain={m_p:.4f}  interaction={m_i:.4f}")
        print(f"  strike: uncorrected={w_u}/{n_u}={s_u:.2f}%  plain={w_p}/{n_p}={s_p:.2f}%  "
              f"interaction={w_i}/{n_i}={s_i:.2f}%")

    print(f"\n{'='*100}\nSummary\n{'='*100}")
    print(f"  avg MAE:    uncorrected={np.mean(mae_u):.4f}  plain={np.mean(mae_p):.4f}  "
          f"interaction={np.mean(mae_i):.4f}")
    print(f"  avg strike: uncorrected={np.mean(strike_u):.2f}%  plain={np.mean(strike_p):.2f}%  "
          f"interaction={np.mean(strike_i):.2f}%")
    print(f"  interaction better than plain on MAE in every fold: "
          f"{all(ii < pp for ii, pp in zip(mae_i, mae_p))}")
    print(f"  interaction better than uncorrected on MAE in every fold: "
          f"{all(ii < uu for ii, uu in zip(mae_i, mae_u))}")

    pu = pd.concat(pooled_u, ignore_index=True)
    pp = pd.concat(pooled_p, ignore_index=True)
    pi = pd.concat(pooled_i, ignore_index=True)
    print(f"\n  Summary-tab-style edge/ROI (pooled, dist_edge != 0 subset only):")
    for thr in EDGE_THRESHOLDS:
        report(pu[(pu["edge"] >= thr) & (pu["sp"] <= PRICE_CAP)], f"uncorrected, edge>={thr:.2f}")
        report(pp[(pp["edge"] >= thr) & (pp["sp"] <= PRICE_CAP)], f"plain,       edge>={thr:.2f}")
        report(pi[(pi["edge"] >= thr) & (pi["sp"] <= PRICE_CAP)], f"interaction, edge>={thr:.2f}")

    print("\nSame multiple-comparisons caveat as the other bet-selection scripts: treat this")
    print("as a hypothesis for a future walk-forward period, not a result to ship blindly.")


if __name__ == "__main__":
    run()
