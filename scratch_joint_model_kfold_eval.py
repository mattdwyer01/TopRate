"""
scratch_joint_model_kfold_eval.py
-----------------------------------
K=4-fold, leak-free walk-forward comparison of the joint model vs the
current additive architecture - the same comparison scratch_joint_model_
eval.py did on a single train/test split (MAE 6.2910 -> 5.8453, -0.4457,
Sep 2026 - see chat), now checked across multiple genuinely out-of-sample
time periods, matching this codebase's own established K=4-fold walk-
forward validation bar before a result is trusted, rather than resting on
one split that could have been lucky.

WALK-FORWARD, NOT RANDOM K-FOLD: this is time-ordered racing data - training
on future races to predict past ones would leak. Each fold's population
ADJ_TERM models (track_barrier, trainer_merit, jockey_merit, closing_merit)
and the joint model itself are refit on ONLY that fold's own trn (data
strictly before the fold's test window, expanding window) - never on data
from a later fold.

SCOPE LIMITATION (deliberate): pace_shape/settle_signal/pace_signal/
interaction are EXCLUDED entirely (fixed 0.0 for both architectures, every
fold). wpr_projection._fit_pace_shape_model's own leak-safe window is
hardcoded to (D's global max date - 365 days), not fold-aware - doing this
properly per fold would need a real custom since= per fold (via the already-
exposed _build_pace_shape_race_scores/_build_pace_shape_settle_lookup) that
isn't worth the added complexity here, since pace_signal's own single-split
importance (72) was already the smallest of the joint model's top features.
Excluding it makes this comparison MORE conservative for the joint model
(giving up a real, if minor, validated signal) - if the joint model still
wins clearly without it, that is a stronger result, not a weaker one.

Does NOT modify wpr_projection.py, does NOT touch wpr_models/*.joblib or
config.json. Read-only comparison, safe to run repeatedly.

NO EM DASHES policy: hyphens only in this file.
"""
import pickle
from pathlib import Path

import numpy as np
import pandas as pd
import lightgbm as lgb
from sklearn.metrics import mean_absolute_error

import wpr_projection as wp

# Checkpoint the expensive prep (build_training_frame + trainer/jockey merge
# + filters + _base/median-fill) to disk so a relaunch after an interrupted
# run (this sandbox has been silently killing background processes mid-run,
# Sep 10 2026 - not an OOM, not a script bug, see chat) can skip straight to
# the fold loop instead of redoing ~10 minutes of feature-building every
# time. /tmp, not the repo - this is throwaway, never meant to be committed.
_CACHE = Path("/tmp/joint_model_kfold_D_cache.pkl")

if _CACHE.exists():
    print(f"Loading cached prepped D from {_CACHE} (skipping rebuild)...")
    with open(_CACHE, "rb") as f:
        D, _name_map = pickle.load(f)
    print(f"{len(D):,} training rows (from cache)")
else:
    print("Building training frame (n_jobs=-1, parallel across free cores) ...")
    D = wp.build_training_frame("wpr_form_history.csv.gz", n_jobs=-1).dropna(
        subset=["target", "date"]).sort_values("date")
    print(f"{len(D):,} training rows")

    print("merging trainer/jockey trailing win-rate by (horse, date)...")
    _name_map, _tj_lookup = wp._load_trainer_jockey_by_horse_date("wpr_form_history.csv.gz")
    _tj_dates = D["date"].dt.strftime("%Y-%m-%d")
    _tj_names = D["horse_id"].map(_name_map)
    _tj_vals = [_tj_lookup.get((n, d), (np.nan, np.nan)) for n, d in zip(_tj_names, _tj_dates)]
    D["trainer_win_pct_365d"] = [t for t, j in _tj_vals]
    D["jockey_win_pct_90d"] = [j for t, j in _tj_vals]

    try:
        from wpr_void import void_from_comment_only
        cv = D["comments_video"] if "comments_video" in D.columns else None
        cs = D["comments_steward"] if "comments_steward" in D.columns else None
        if cv is not None or cs is not None:
            cv = cv if cv is not None else [None] * len(D)
            cs = cs if cs is not None else [None] * len(D)
            void_mask = [void_from_comment_only(a, b)[0] for a, b in zip(cv, cs)]
            n_void = int(sum(void_mask))
            if n_void:
                D = D[[not v for v in void_mask]].copy()
                print(f"void filter: excluded {n_void:,} rows, {len(D):,} remain")
    except ImportError:
        print("void filter: wpr_void not found, skipping")

    if "going" in D.columns:
        _g = D["going"].astype(str).str.strip().str.lower()
        blank_going = D["going"].isna() | _g.isin(["", "nan", "none", "<na>"])
        n_blank = int(blank_going.sum())
        if n_blank:
            D = D[~blank_going].copy()
            print(f"surface filter: excluded {n_blank:,} rows, {len(D):,} remain")

    D["_base"] = wp._BASE_BLEND_ALPHA * D["wpr_nett"] + (1 - wp._BASE_BLEND_ALPHA) * D["ewm5"]
    D["_base"] = D["_base"].fillna(D["wpr_nett"]).fillna(D["ewm5"]) \
        .fillna(D["avg_last3"]).fillna(D["career_avg"])
    D = D.dropna(subset=["_base"]).copy()

    med = D[wp.FEATURES].median()
    D[wp.FEATURES] = D[wp.FEATURES].fillna(med)

    # pace_shape excluded entirely (see module docstring).
    D["pace_shape"] = 0.0
    D["settle_signal"] = 0.0
    D["pace_signal"] = 0.0
    D["interaction"] = 0.0

    print(f"Caching prepped D to {_CACHE} ...")
    with open(_CACHE, "wb") as f:
        pickle.dump((D, _name_map), f)

BASE_JOINT_FEATURES = list(wp.FEATURES) + [
    "barrier", "track_code", "trainer_win_pct_365d", "jockey_win_pct_90d",
    "gear_code", "closing_raw_resid", "closing_n_pairs",
    "settle_signal", "pace_signal", "interaction",
]


def _additive_predict(frame):
    return frame["_base"].to_numpy() + wp._cap_adj_sum(
        frame[wp.ADJ_TERMS].to_numpy()).sum(axis=1)


def run_fold(fold_num, D, trn_mask, te_mask):
    trn = D[trn_mask].copy()
    te = D[te_mask].copy()
    print(f"\n{'='*70}")
    print(f"FOLD {fold_num}: trn={len(trn):,} ({trn['date'].min().date()} to {trn['date'].max().date()})  "
          f"te={len(te):,} ({te['date'].min().date()} to {te['date'].max().date()})")
    print("=" * 70)

    track_categories = sorted(trn["track"].dropna().unique())
    track_code_map = {t: i for i, t in enumerate(track_categories)}
    for _frame in (trn, te):
        _frame.loc[:, "track_code"] = _frame["track"].map(track_code_map).fillna(-1).astype(int)
    track_barrier_model = wp._fit_simple_adj_model(trn, wp._TRACK_BARRIER_FEATURES, "track_barrier")
    te["track_barrier"] = [
        wp._track_barrier_term(trk, dist, bar, fs, track_code_map, track_barrier_model)
        for trk, dist, bar, fs in zip(te["track"], te["cur_distance"], te["barrier"], te["field_size"])
    ]

    trainer_merit_trn = wp._fit_coverage_aware_trn(trn, ["trainer_win_pct_365d"])
    trainer_merit_model = wp._fit_simple_adj_model(trainer_merit_trn, wp._TRAINER_MERIT_FEATURES, "trainer_merit")
    jockey_merit_trn = wp._fit_coverage_aware_trn(trn, ["jockey_win_pct_90d"])
    jockey_merit_model = wp._fit_simple_adj_model(jockey_merit_trn, wp._JOCKEY_MERIT_FEATURES, "jockey_merit")
    te["trainer_merit"] = [
        wp._merit_term(v, fs, trainer_merit_model, wp._TRAINER_MERIT_FEATURES)
        for v, fs in zip(te["trainer_win_pct_365d"], te["field_size"])
    ]
    te["jockey_merit"] = [
        wp._merit_term(v, fs, jockey_merit_model, wp._JOCKEY_MERIT_FEATURES)
        for v, fs in zip(te["jockey_win_pct_90d"], te["field_size"])
    ]

    for _frame in (trn, te):
        _bucket = _frame["gear_changes"].apply(wp._gear_change_bucket)
        _frame.loc[:, "gear_code"] = _bucket.map(wp._GEAR_BUCKET_CODE).fillna(0).astype(int)
    wp._fit_simple_adj_model(trn, wp._GEAR_CHANGE_FEATURES, "gear_change")  # fit only, unused (not an ADJ_TERM)

    trn_cutoff_date = trn["date"].max()
    pace_baseline_lookup = wp._fit_pace_baseline("wpr_form_history.csv.gz", trn_cutoff_date)

    def _closing_raw_resid_one(pairs):
        vals = []
        for sect, bucket in pairs:
            exp = pace_baseline_lookup.get(bucket)
            if exp is not None and sect is not None and sect == sect:
                vals.append(float(sect) - float(exp))
        return (float(np.mean(vals)), float(len(vals))) if vals else (np.nan, 0.0)

    for _frame in (trn, te):
        _computed = [_closing_raw_resid_one(p) for p in _frame["closing_pairs"]]
        _frame.loc[:, "closing_raw_resid"] = [c[0] for c in _computed]
        _frame.loc[:, "closing_n_pairs"] = [c[1] for c in _computed]
    closing_merit_model = wp._fit_simple_adj_model(trn, wp._CLOSING_MERIT_FEATURES, "closing_merit")
    te["closing_merit"] = [
        wp._closing_merit_term(pairs, pace_baseline_lookup, fs, closing_merit_model)
        for pairs, fs in zip(te["closing_pairs"], te["field_size"])
    ]

    for _term in ("track_barrier", "closing_merit", "trainer_merit", "jockey_merit"):
        te[_term] = te[_term] - te.groupby("race_id")[_term].transform("mean")

    te[wp.ADJ_TERMS] = te[wp.ADJ_TERMS].fillna(0.0)

    mae_current = mean_absolute_error(te["target"], _additive_predict(te))

    jf = [f for f in BASE_JOINT_FEATURES if f in trn.columns]
    for c in jf:
        if trn[c].isna().any() or te[c].isna().any():
            _fill = trn[c].median()
            trn[c] = trn[c].fillna(_fill)
            te[c] = te[c].fillna(_fill)

    joint_model = lgb.LGBMRegressor(objective="quantile", alpha=0.5, n_estimators=350,
                                    max_depth=3, learning_rate=0.04, num_leaves=8,
                                    random_state=42, verbosity=-1)
    joint_model.fit(trn[jf], trn["target"])
    mae_joint = mean_absolute_error(te["target"], joint_model.predict(te[jf]))

    print(f"  CURRENT additive: MAE = {mae_current:.4f}")
    print(f"  JOINT model:      MAE = {mae_joint:.4f}")
    print(f"  Delta: {mae_joint - mae_current:+.4f} "
          f"({'JOINT WINS' if mae_joint < mae_current else 'ADDITIVE WINS'})")
    return mae_current, mae_joint


# Walk-forward, 4 folds - a substantial expanding-window trn before the
# first test fold (matching train_wpr_projection()'s own convention of a
# large trn before any evaluation split), each subsequent fold's trn
# expanding to include the prior fold's test period too.
q = D["date"].quantile([0.40, 0.55, 0.70, 0.85, 1.0]).tolist()
folds = [
    (D["date"] < q[0], (D["date"] >= q[0]) & (D["date"] < q[1])),
    (D["date"] < q[1], (D["date"] >= q[1]) & (D["date"] < q[2])),
    (D["date"] < q[2], (D["date"] >= q[2]) & (D["date"] < q[3])),
    (D["date"] < q[3], (D["date"] >= q[3])),
]

results = []
for i, (trn_mask, te_mask) in enumerate(folds, 1):
    results.append(run_fold(i, D, trn_mask, te_mask))

print(f"\n{'='*70}")
print(f"SUMMARY across {len(results)} walk-forward folds")
print("=" * 70)
for i, (mae_c, mae_j) in enumerate(results, 1):
    print(f"  Fold {i}: additive={mae_c:.4f}  joint={mae_j:.4f}  delta={mae_j-mae_c:+.4f}")
avg_c = float(np.mean([r[0] for r in results]))
avg_j = float(np.mean([r[1] for r in results]))
print(f"\n  Mean additive MAE: {avg_c:.4f}")
print(f"  Mean joint MAE:    {avg_j:.4f}")
print(f"  Mean delta:        {avg_j-avg_c:+.4f}")
n_joint_wins = sum(1 for c, j in results if j < c)
print(f"  Joint model won {n_joint_wins}/{len(results)} folds")
print("\nDone.")
