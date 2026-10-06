"""
wpr_first_up_trial_correction_kfold_test.py - K=4-fold leak-free
validation of wpr_interim_trial_scoping_check.py's finding: does a
trial/jumpout run before a first-up return predict how much the model's
existing (already known to be biased) first-up over-prediction should be
corrected?

WHY: the model already over-predicts first-up runners on average (a
known, existing behaviour - see build_features' first_up handling), but
the scoping check found that over-prediction shrinks sharply with better
pre-race trial form: bottom trial-finish quartile resid=-1.92, top
quartile resid=-0.05 (n=2,852). Mid-prep + freshen-up trials showed no
usable pattern and are not tested further here.

METHOD: K=4 chronological folds. Per fold: fit population terms as
always (leak-free), fit a correction (OLS: resid ~ avg_finish_pct +
won_a_trial, shrunk toward 0 by rounding down small-sample noise via a
minimum row count, not a separate K - the regression itself already
regularises via sample size) on the training folds' first-up-with-trial
rows only, apply it to the held-out fold's first-up-with-trial rows on
top of the EXISTING (unchanged) projection. Compares corrected vs
uncorrected MAE and Summary-tab-style edge/ROI on that subset.

NO EM DASHES policy: hyphens only in this file.
"""
import json
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
BETA_GRID = [0.05, 0.10, 0.15, 0.20, 0.25, 0.30, 0.40]
PRICE_CAP = 26.0
EDGE_THRESHOLDS = [0.05, 0.10, 0.20]
MIN_FIT_ROWS = 50


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


def build_trial_intervals():
    df = pd.read_csv(FORM_CSV, low_memory=False,
                      usecols=["horse_id", "date", "isBarrierTrial", "is_jumpout",
                               "positionFinish", "field_size", "marginFinish"])
    df["date"] = pd.to_datetime(df["date"], errors="coerce")
    df = df.dropna(subset=["date", "horse_id"])
    df["is_trial"] = (df["isBarrierTrial"] == True) | (df["is_jumpout"] == True)
    trials = df[df["is_trial"]].sort_values(["horse_id", "date"])
    return dict(tuple(trials.groupby("horse_id")))


def trial_features(trial_group, lo_date, hi_date):
    if trial_group is None:
        return None
    t = trial_group[(trial_group["date"] < hi_date) & (trial_group["date"] > lo_date)]
    if len(t) == 0:
        return None
    pos = pd.to_numeric(t["positionFinish"], errors="coerce")
    fs = pd.to_numeric(t["field_size"], errors="coerce")
    valid = pos.notna() & fs.notna() & (fs > 0)
    if not valid.any():
        return None
    pos, fs, t = pos[valid], fs[valid], t[valid]
    finish_pct = 1 - (pos - 1) / fs
    return {
        "avg_finish_pct": float(finish_pct.mean()),
        "won_a_trial": float((pos == 1).max()),
    }


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


def fit_correction(train_fu):
    if len(train_fu) < MIN_FIT_ROWS:
        return None
    X = np.column_stack([np.ones(len(train_fu)), train_fu["trial_avg_finish_pct"], train_fu["trial_won_a_trial"]])
    y = train_fu["resid"].to_numpy()
    coef, *_ = np.linalg.lstsq(X, y, rcond=None)
    return coef


def apply_correction(frame, coef):
    return coef[0] + coef[1] * frame["trial_avg_finish_pct"] + coef[2] * frame["trial_won_a_trial"]


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
    full = full.dropna(subset=["target", "_base", "career_avg", "first_up", "days_since"] + non_pop_terms +
                        ["barrier", "field_size", "track", "cur_distance",
                         "trainer_win_pct_365d", "jockey_win_pct_90d", "sp"])
    full = full[full["sp"] > 1.0]
    full = full.sort_values("date").reset_index(drop=True)
    print(f"Scoped rows: {len(full):,}")

    trial_by_horse = build_trial_intervals()
    full["last_real_date"] = full["date"] - pd.to_timedelta(full["days_since"], unit="D")

    fu = full[full["first_up"] == 1].copy()

    def _get_feat(row):
        tg = trial_by_horse.get(row["horse_id"])
        return trial_features(tg, row["last_real_date"], row["date"])

    print("Computing intervening-trial features for first-up rows...")
    feats = fu.apply(_get_feat, axis=1)
    has_trial = feats.notna()
    feat_df = pd.DataFrame(list(feats[has_trial]), index=fu.index[has_trial])
    feat_df = feat_df.add_prefix("trial_")
    fu_trial = fu.loc[has_trial].join(feat_df)
    print(f"first-up rows with an intervening trial: {len(fu_trial):,} / {len(fu):,}")

    fold_edges = np.array_split(np.arange(len(full)), N_FOLDS)
    full["_fold"] = -1
    for i, idx in enumerate(fold_edges):
        full.loc[idx, "_fold"] = i
    fu_trial["_fold"] = full.loc[fu_trial.index, "_fold"]

    print(f"\n{'='*100}\nK={N_FOLDS}-fold: first-up trial correction, scored on the "
          f"first-up-with-trial subset only\n{'='*100}")

    mae_u_all, mae_c_all = [], []
    strike_u_all, strike_c_all = [], []
    pooled_u, pooled_c = [], []
    for i in range(N_FOLDS):
        test = full[full["_fold"] == i].copy()
        train = full[full["_fold"] != i].copy()
        fit_direction(train, [train, test], train["date"].max())

        test_fu = fu_trial[fu_trial["_fold"] == i].copy()
        train_fu = fu_trial[fu_trial["_fold"] != i].copy()
        if len(test_fu) < 30:
            print(f"  fold {i}: too few first-up-with-trial rows ({len(test_fu)}), skipped")
            continue

        # refresh proj/resid for these rows using THIS fold's freshly fit population terms
        for f in (train_fu, test_fu):
            src = train if f is train_fu else test
            f["_base_calib"] = src.loc[f.index, "_base_calib"]
            f["adj_total"] = src.loc[f.index, "adj_total"]
            f["proj"] = src.loc[f.index, "proj"]
            f["resid"] = src.loc[f.index, "resid"]

        coef = fit_correction(train_fu)
        if coef is None:
            print(f"  fold {i}: too few training rows to fit a correction, skipped")
            continue

        test_fu["proj_corr"] = test_fu["proj"] + apply_correction(test_fu, coef)
        train_fu["proj_corr"] = train_fu["proj"] + apply_correction(train_fu, coef)

        mae_u = (test_fu["target"] - test_fu["proj"]).abs().mean()
        mae_c = (test_fu["target"] - test_fu["proj_corr"]).abs().mean()
        mae_u_all.append(mae_u)
        mae_c_all.append(mae_c)

        strike_u, wins_u, n_u, scored_u = score(train_fu, test_fu, "proj")
        strike_c, wins_c, n_c, scored_c = score(train_fu, test_fu, "proj_corr")
        strike_u_all.append(strike_u)
        strike_c_all.append(strike_c)
        pooled_u.append(scored_u)
        pooled_c.append(scored_c)

        print(f"\n--- fold {i} (first-up-with-trial n={len(test_fu):,}) ---")
        print(f"  correction coef (intercept, avg_finish_pct, won_a_trial): "
              f"{[round(c, 3) for c in coef]}")
        print(f"  MAE: uncorrected={mae_u:.4f}  corrected={mae_c:.4f}  "
              f"({'better' if mae_c < mae_u else 'worse/same'})")
        print(f"  top-1 strike: uncorrected={wins_u}/{n_u}={strike_u:.2f}%  "
              f"corrected={wins_c}/{n_c}={strike_c:.2f}%  "
              f"({'better' if strike_c > strike_u else 'worse/same'})")

    print(f"\n{'='*100}\nSummary\n{'='*100}")
    print(f"  avg MAE: uncorrected={np.mean(mae_u_all):.4f}  corrected={np.mean(mae_c_all):.4f}")
    print(f"  corrected better on MAE in every fold: {all(c < u for c, u in zip(mae_c_all, mae_u_all))}")
    print(f"  avg top-1 strike: uncorrected={np.mean(strike_u_all):.2f}%  corrected={np.mean(strike_c_all):.2f}%")

    if pooled_u:
        pooled_uc = pd.concat(pooled_u, ignore_index=True)
        pooled_cc = pd.concat(pooled_c, ignore_index=True)
        print(f"\n  Summary-tab-style edge/ROI (pooled, first-up-with-trial subset only):")
        for thr in EDGE_THRESHOLDS:
            report(pooled_uc[(pooled_uc["edge"] >= thr) & (pooled_uc["sp"] <= PRICE_CAP)],
                   f"uncorrected, edge>={thr:.2f}")
            report(pooled_cc[(pooled_cc["edge"] >= thr) & (pooled_cc["sp"] <= PRICE_CAP)],
                   f"corrected,   edge>={thr:.2f}")

    print("\nSame multiple-comparisons caveat as the other bet-selection scripts: treat this")
    print("as a hypothesis for a future walk-forward period, not a result to ship blindly.")


if __name__ == "__main__":
    run()
