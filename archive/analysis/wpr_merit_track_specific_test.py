"""
wpr_merit_track_specific_test.py - does a trainer/jockey's performance AT
THIS SPECIFIC TRACK carry real incremental signal beyond their existing
overall trailing_win_pct (365d/90d, all tracks combined)?

WHY: trainer_win_pct_365d/jockey_win_pct_90d are track-agnostic snapshots.
A trainer who wins at an above-average rate everywhere already shows up
there. What that misses: a trainer/jockey who does notably BETTER or
WORSE at one specific track than their own overall rate would suggest -
local knowledge, a stable that travels well to a particular circuit, a
jockey who rides a track's home turns better than most. This tests that
SPECIFICALLY (a track_effect residual: this trainer's own win rate AT
THIS TRACK minus their own overall win rate, shrunk by track-specific
sample size toward 0 - not toward the population mean, since the
question is "better/worse than usual for THIS trainer", not "better/
worse than average trainers").

DATA: built directly from wpr_form_history.csv.gz (513k rows, 2016-2026,
99% trainer/jockey coverage) rather than the toprate_runners.csv-only
trailing win-pct snapshots - trainer/track/jockey/date/positionFinish are
all in the raw per-run archive. Genuinely walk-forward by construction:
for every historical row, "trainer's win rate at this track so far" and
"trainer's overall win rate so far" are computed from STRICTLY PRIOR runs
only (groupby + expanding + shift(1)) - no per-fold refit needed for the
feature itself (unlike the population-level bucket lookups elsewhere in
this series), since every row already only sees its own true past.

SPARSITY: median only 4 prior runs per (trainer, track) pair (mean 14.4,
skewed by the more prolific pairs) - track-specific shrinkage (K_TRACK)
needs to be much smaller than the 300 used for trainer_merit/jockey_merit's
own population-wide K, or a real track effect would be shrunk away before
it's ever visible. Tested across a K_TRACK grid rather than picked once.

METHOD: K=4 chronological folds. Per fold, fit a scalar gamma (OLS, no
intercept) mapping (track_effect_trainer + track_effect_jockey) onto
target - proj_shipped (the residual the SHIPPED model still leaves on
the table) on the training folds, then score held-out top-1 strike rate
and Summary-tab-style edge/ROI for proj_shipped + gamma*track_effect vs
proj_shipped alone - same adoption bar as every other trainer/jockey
merit test in this series.

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
K_TRACK_GRID = [3, 5, 10, 20]
BETA_GRID = [0.05, 0.10, 0.15, 0.20, 0.25, 0.30, 0.40]
PRICE_CAP = 26.0
EDGE_THRESHOLDS = [0.05, 0.10, 0.20]
MIN_TRACK_RUNS = 2  # need at least this many PRIOR runs at the track to compute anything


def build_full():
    """Same stale-"_base"-cache fix as the other merit-slope scripts this
    session - see wpr_merit_slope_kfold_test.py's build_full() docstring."""
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


def build_track_effect_table():
    """Reads wpr_form_history.csv.gz fresh (the full raw per-run archive,
    not the per-horse training frame - trainer/track performance spans
    many different horses) and computes, per row, this trainer's/jockey's
    own win rate AT THIS TRACK and OVERALL, both using strictly prior rows
    only (expanding mean, shifted by 1 within each group, sorted by date).
    Returns a DataFrame keyed by (horse, date) - same join convention as
    merge_won_by_horse_date/merge_trainer_jockey_by_horse_date, for the
    same reason (run_id is not a reliable per-historical-row key)."""
    print("Reading raw form history for track-specific trainer/jockey rates...")
    cols = ["horse", "date", "track", "trainer", "jockey", "positionFinish"]
    raw = pd.read_csv(FORM_CSV, usecols=cols, low_memory=False)
    raw["date"] = pd.to_datetime(raw["date"], errors="coerce")
    raw = raw.dropna(subset=["date", "trainer", "jockey", "track", "positionFinish"])
    raw["won"] = (raw["positionFinish"] == 1).astype(float)
    raw = raw.sort_values("date").reset_index(drop=True)

    def _prior_rate(df, group_cols, out_col):
        g = df.groupby(group_cols)["won"]
        cum_sum = g.cumsum() - df["won"]
        cum_n = g.cumcount()
        df[out_col + "_n"] = cum_n
        df[out_col] = np.where(cum_n > 0, cum_sum / cum_n.replace(0, np.nan), np.nan)

    _prior_rate(raw, ["trainer"], "trainer_overall_rate")
    _prior_rate(raw, ["trainer", "track"], "trainer_track_rate")
    _prior_rate(raw, ["jockey"], "jockey_overall_rate")
    _prior_rate(raw, ["jockey", "track"], "jockey_track_rate")

    print(f"  {len(raw):,} rows with trainer/jockey/track/result; "
          f"median prior runs at (trainer, track): {raw['trainer_track_rate_n'].median():.0f}")
    return raw[["horse", "date", "trainer_overall_rate", "trainer_track_rate", "trainer_track_rate_n",
                "jockey_overall_rate", "jockey_track_rate", "jockey_track_rate_n"]]


def merge_track_effect(D, track_tbl):
    """(horse, date) join - same convention/caveat as merge_won_by_horse_date
    (drops ambiguous same-name-same-day collisions rather than risk a wrong
    match)."""
    t = track_tbl.drop_duplicates(subset=["horse", "date"], keep=False)
    return D.merge(t, on=["horse", "date"], how="inner")


def track_effect_at_k(frame, k_track):
    """Shrinks (track_rate - overall_rate) toward 0 by n_track/(n_track+k) -
    "no track-specific evidence yet" is 0, not the population mean, since
    this is measuring deviation from THIS trainer's/jockey's OWN baseline."""
    def _eff(rate_col, overall_col, n_col):
        delta = frame[rate_col] - frame[overall_col]
        n = frame[n_col].fillna(0)
        shrunk = delta * n / (n + k_track)
        return shrunk.where(n >= MIN_TRACK_RUNS, 0.0).fillna(0.0)

    trainer_eff = _eff("trainer_track_rate", "trainer_overall_rate", "trainer_track_rate_n")
    jockey_eff = _eff("jockey_track_rate", "jockey_overall_rate", "jockey_track_rate_n")
    return trainer_eff + jockey_eff


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
        f["proj_shipped"] = f["_base_calib"] + f["adj_total"]


def fit_gamma(train, k_track):
    x = track_effect_at_k(train, k_track).to_numpy()
    y = (train["target"] - train["proj_shipped"]).to_numpy()
    denom = np.dot(x, x)
    return float(np.dot(x, y) / denom) if denom > 0 else 0.0


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


def score(train, test, proj_col_train, proj_col_test):
    b = best_beta(train, proj_col_train)

    def _prob(g):
        pv = g[proj_col_test].to_numpy(dtype=float)
        e = np.exp(b * (pv - pv.max()))
        return pd.Series(e / e.sum(), index=g.index)

    test = test.copy()
    test["model_prob"] = test.groupby("race_id", group_keys=False).apply(_prob)

    def _edge(g):
        p_mkt = (1.0 / g["sp"]) / (1.0 / g["sp"]).sum()
        return g["model_prob"] - p_mkt

    test["edge"] = test.groupby("race_id", group_keys=False).apply(_edge)
    strike, wins, n_top1 = top1_strike_rate(test, proj_col_test)
    return strike, wins, n_top1, test


def run():
    full = build_full()
    track_tbl = build_track_effect_table()
    full = merge_track_effect(full, track_tbl)

    non_pop_terms = [t for t in wpr.ADJ_TERMS
                     if t not in ("track_barrier", "closing_merit", "trainer_merit", "jockey_merit")]
    full = full.dropna(subset=["target", "_base", "career_avg"] + non_pop_terms +
                        ["barrier", "field_size", "track", "cur_distance",
                         "trainer_win_pct_365d", "jockey_win_pct_90d", "sp"])
    full = full[full["sp"] > 1.0]
    full = full.sort_values("date").reset_index(drop=True)
    print(f"\nScoped rows (after track-effect merge + standard filters): {len(full):,}")
    n_with_track_data = (full["trainer_track_rate_n"].fillna(0) >= MIN_TRACK_RUNS).sum()
    print(f"Rows with >= {MIN_TRACK_RUNS} prior trainer runs at that track: {n_with_track_data:,} "
          f"({n_with_track_data / len(full) * 100:.1f}%)")

    fold_edges = np.array_split(np.arange(len(full)), N_FOLDS)
    full["_fold"] = -1
    for i, idx in enumerate(fold_edges):
        full.loc[idx, "_fold"] = i

    summary = []
    for k_track in K_TRACK_GRID:
        print(f"\n{'='*100}\nK_TRACK = {k_track}\n{'='*100}")
        strikes_ship, strikes_cand = [], []
        pooled_ship, pooled_cand = [], []
        gammas = []
        for i in range(N_FOLDS):
            test = full[full["_fold"] == i].copy()
            train = full[full["_fold"] != i].copy()
            fit_direction(train, [train, test], train["date"].max())

            gamma = fit_gamma(train, k_track)
            gammas.append(gamma)
            train["proj_cand"] = train["proj_shipped"] + gamma * track_effect_at_k(train, k_track)
            test["proj_cand"] = test["proj_shipped"] + gamma * track_effect_at_k(test, k_track)

            strike_ship, wins_ship, n_ship, scored_ship = score(train, test, "proj_shipped", "proj_shipped")
            strike_cand, wins_cand, n_cand, scored_cand = score(train, test, "proj_cand", "proj_cand")
            strikes_ship.append(strike_ship)
            strikes_cand.append(strike_cand)
            pooled_ship.append(scored_ship)
            pooled_cand.append(scored_cand)
            print(f"  fold {i}: gamma={gamma:+.4f}  strike shipped={wins_ship}/{n_ship}={strike_ship:.2f}%  "
                  f"+track_effect={wins_cand}/{n_cand}={strike_cand:.2f}%  "
                  f"({'better' if strike_cand > strike_ship else 'worse/same'})")

        avg_ship = np.mean(strikes_ship)
        avg_cand = np.mean(strikes_cand)
        print(f"\n  avg gamma: {np.mean(gammas):+.4f}")
        print(f"  avg strike: shipped={avg_ship:.2f}%  +track_effect={avg_cand:.2f}%")
        pooled_s = pd.concat(pooled_ship, ignore_index=True)
        pooled_c = pd.concat(pooled_cand, ignore_index=True)
        roi_ship, roi_cand = {}, {}
        for thr in EDGE_THRESHOLDS:
            sub_s = pooled_s[(pooled_s["edge"] >= thr) & (pooled_s["sp"] <= PRICE_CAP)]
            sub_c = pooled_c[(pooled_c["edge"] >= thr) & (pooled_c["sp"] <= PRICE_CAP)]
            report(sub_s, f"shipped, edge>={thr:.2f}")
            report(sub_c, f"+track_effect, edge>={thr:.2f}")
            roi_ship[thr] = (np.where(sub_s["won"] == 1, sub_s["sp"] - 1, -1.0).sum() / len(sub_s) * 100
                             if len(sub_s) else float("nan"))
            roi_cand[thr] = (np.where(sub_c["won"] == 1, sub_c["sp"] - 1, -1.0).sum() / len(sub_c) * 100
                             if len(sub_c) else float("nan"))
        summary.append((k_track, avg_ship, avg_cand, roi_ship, roi_cand))

    print(f"\n{'='*100}\nSUMMARY: K_TRACK vs strike rate / ROI (shipped vs +track_effect)\n{'='*100}")
    for k_track, avg_ship, avg_cand, roi_ship, roi_cand in summary:
        print(f"  K_TRACK={k_track:3d}  strike: shipped={avg_ship:.2f}% -> +track_effect={avg_cand:.2f}%")
        for thr in EDGE_THRESHOLDS:
            print(f"      edge>={thr:.2f}: shipped ROI={roi_ship[thr]:+.1f}%  "
                  f"+track_effect ROI={roi_cand[thr]:+.1f}%")

    print("\nSame multiple-comparisons caveat as the other bet-selection scripts: treat any")
    print("row here as a hypothesis for a future walk-forward period, not a result to ship blindly.")


if __name__ == "__main__":
    run()
