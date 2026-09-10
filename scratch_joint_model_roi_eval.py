"""
scratch_joint_model_roi_eval.py
----------------------------------
The gate the K=4-fold MAE result (mean delta -0.4533, joint won 4/4 folds,
Sep 2026 - see chat) still needs before being taken seriously: does the
joint model's edge against real market prices actually beat the current
additive architecture's, or does this codebase's own repeated finding -
MAE and ROI pointing in OPPOSITE directions (the calibration-slope removal
is the clearest prior example) - hold here too?

METHODOLOGY: mirrors wpr_bet_selection_leakfree_eval.py's own established
"genuinely leak-free" bidirectional approach exactly (see that file's own
docstring for the full rationale) - split by date 50/50 into H1/H2, fit
EVERY population artifact (track_barrier, trainer_merit, jockey_merit,
closing_merit, AND for this script's purposes the joint model itself) on
one half only, score the OTHER half, do this in both directions, pool the
two held-out halves. Every row's prediction (additive or joint) came from a
fit that never saw that row or any row from the same half.

Unlike that reference script (which predates the Sep 2026 trained-model
conversion and still uses the old bucket-lookup ADJ_TERM style), this one
uses the SAME per-row trained-model term functions (_track_barrier_term,
_merit_term, _closing_merit_term) the live model and the K-fold MAE eval
actually use - so the additive baseline here matches what is actually
shipped, not a stale prior version.

price-softmax beta is fit separately for EACH prediction column (additive,
joint) via the same Brier-minimization grid search calibrate_price_beta.py
established, in-sample on the fit half (an accepted convention for this
low-risk scalar constant, per wpr_bet_selection_leakfree_eval.py's own
docstring) - a fair comparison needs each architecture's own best-fit price
translation, not one borrowed from the other.

SCOPE LIMITATION (deliberate, matching the K-fold MAE eval): pace_shape/
settle_signal/pace_signal/interaction excluded entirely (fixed 0.0, both
architectures, both halves) - same reasoning as scratch_joint_model_kfold_
eval.py's own docstring.

Checkpoints the prepped, merged D to /tmp early (this sandbox has been
killing long-running background scripts mid-build repeatedly this session -
not OOM, not a bug, see chat) so an interrupted run's relaunch skips the
expensive rebuild.

Does NOT modify wpr_projection.py, does NOT touch wpr_models/*.joblib or
config.json. Read-only, safe to run repeatedly.

NO EM DASHES policy: hyphens only in this file.
"""
import pickle
from pathlib import Path

import numpy as np
import pandas as pd
import lightgbm as lgb

import wpr_projection as wp
from wpr_own_pace_backtest import merge_won_by_horse_date
from wpr_bet_selection_post_retrain import merge_price_pfm

FORM_CSV = "wpr_form_history.csv.gz"
BETA_GRID = [0.05, 0.10, 0.15, 0.20, 0.25, 0.30, 0.40]
EDGE_THRESHOLDS = [0.0, 0.02, 0.04, 0.06, 0.08, 0.10, 0.13, 0.15, 0.20]
PRICE_CAPS = [15.0, 26.0]

_CACHE = Path("/tmp/joint_model_roi_D_cache.pkl")

if _CACHE.exists():
    print(f"Loading cached prepped D from {_CACHE} (skipping rebuild)...")
    with open(_CACHE, "rb") as f:
        D = pickle.load(f)
    print(f"{len(D):,} rows (from cache)")
else:
    print("Building training frame (n_jobs=-1, parallel) ...")
    D = wp.build_training_frame(FORM_CSV, n_jobs=-1).dropna(
        subset=["target", "date"]).sort_values("date")
    print(f"{len(D):,} training rows")

    print("Merging won/race_id from toprate_runners.csv (leak-safe horse+date join)...")
    D = merge_won_by_horse_date(D, form_csv=FORM_CSV)
    print(f"  {len(D):,} rows after won/race_id merge")

    print("Merging trainer/jockey trailing win-rate...")
    _name_map, _tj_lookup = wp._load_trainer_jockey_by_horse_date(FORM_CSV)
    _tj_dates = D["date"].dt.strftime("%Y-%m-%d")
    _tj_names = D["horse_id"].map(_name_map)
    _tj_vals = [_tj_lookup.get((n, d), (np.nan, np.nan)) for n, d in zip(_tj_names, _tj_dates)]
    D["trainer_win_pct_365d"] = [t for t, j in _tj_vals]
    D["jockey_win_pct_90d"] = [j for t, j in _tj_vals]

    print("Merging price/pfm_score from toprate_runners.csv...")
    D = merge_price_pfm(D)
    sp = pd.to_numeric(D["fixed_win_price"], errors="coerce")
    sp_fallback = pd.to_numeric(D["starting_price_sp"], errors="coerce")
    D["used_sp_fallback"] = sp.isna() & sp_fallback.notna()
    D["sp"] = sp.fillna(sp_fallback)
    D = D.dropna(subset=["sp"])
    D = D[D["sp"] > 1.0]
    print(f"  {len(D):,} rows with a usable price")

    if "going" in D.columns:
        _g = D["going"].astype(str).str.strip().str.lower()
        blank_going = D["going"].isna() | _g.isin(["", "nan", "none", "<na>"])
        n_blank = int(blank_going.sum())
        if n_blank:
            D = D[~blank_going].copy()
            print(f"  surface filter: excluded {n_blank:,} rows, {len(D):,} remain")

    D["_base"] = wp._BASE_BLEND_ALPHA * D["wpr_nett"] + (1 - wp._BASE_BLEND_ALPHA) * D["ewm5"]
    D["_base"] = D["_base"].fillna(D["wpr_nett"]).fillna(D["ewm5"]) \
        .fillna(D["avg_last3"]).fillna(D["career_avg"])
    D = D.dropna(subset=["_base"]).copy()

    med = D[wp.FEATURES].median()
    D[wp.FEATURES] = D[wp.FEATURES].fillna(med)

    D["pace_shape"] = 0.0
    D["settle_signal"] = 0.0
    D["pace_signal"] = 0.0
    D["interaction"] = 0.0

    print(f"Caching prepped D to {_CACHE} ...")
    with open(_CACHE, "wb") as f:
        pickle.dump(D, f)

BASE_JOINT_FEATURES = list(wp.FEATURES) + [
    "barrier", "track_code", "trainer_win_pct_365d", "jockey_win_pct_90d",
    "gear_code", "closing_raw_resid", "closing_n_pairs",
    "settle_signal", "pace_signal", "interaction",
]


def _additive_predict(frame):
    return frame["_base"].to_numpy() + wp._cap_adj_sum(
        frame[wp.ADJ_TERMS].to_numpy()).sum(axis=1)


def _closing_raw_resid_one(pairs, pace_baseline_lookup):
    vals = []
    for sect, bucket in pairs:
        exp = pace_baseline_lookup.get(bucket)
        if exp is not None and sect is not None and sect == sect:
            vals.append(float(sect) - float(exp))
    return (float(np.mean(vals)), float(len(vals))) if vals else (np.nan, 0.0)


def fit_and_score(fit_half, held_out):
    """Fits every population ADJ_TERM model and the joint model on
    fit_half ONLY; returns held_out with additive_pred/joint_pred columns
    computed purely from fit_half's fits - held_out never contributes to
    anything used to score it."""
    fit_half = fit_half.copy()
    held_out = held_out.copy()

    track_categories = sorted(fit_half["track"].dropna().unique())
    track_code_map = {t: i for i, t in enumerate(track_categories)}
    trainer_merit_trn = wp._fit_coverage_aware_trn(fit_half, ["trainer_win_pct_365d"])
    trainer_merit_model = wp._fit_simple_adj_model(trainer_merit_trn, wp._TRAINER_MERIT_FEATURES, "trainer_merit")
    jockey_merit_trn = wp._fit_coverage_aware_trn(fit_half, ["jockey_win_pct_90d"])
    jockey_merit_model = wp._fit_simple_adj_model(jockey_merit_trn, wp._JOCKEY_MERIT_FEATURES, "jockey_merit")
    for _f in (fit_half, held_out):
        _f.loc[:, "track_code"] = _f["track"].map(track_code_map).fillna(-1).astype(int)
    track_barrier_model = wp._fit_simple_adj_model(fit_half, wp._TRACK_BARRIER_FEATURES, "track_barrier")
    pace_baseline_lookup = wp._fit_pace_baseline(FORM_CSV, fit_half["date"].max())
    for _f in (fit_half, held_out):
        _computed = [_closing_raw_resid_one(p, pace_baseline_lookup) for p in _f["closing_pairs"]]
        _f.loc[:, "closing_raw_resid"] = [c[0] for c in _computed]
        _f.loc[:, "closing_n_pairs"] = [c[1] for c in _computed]
    closing_merit_model = wp._fit_simple_adj_model(fit_half, wp._CLOSING_MERIT_FEATURES, "closing_merit")

    for _f in (fit_half, held_out):
        _f.loc[:, "track_barrier"] = [
            wp._track_barrier_term(trk, dist, bar, fs, track_code_map, track_barrier_model)
            for trk, dist, bar, fs in zip(_f["track"], _f["cur_distance"], _f["barrier"], _f["field_size"])
        ]
        _f.loc[:, "trainer_merit"] = [
            wp._merit_term(v, fs, trainer_merit_model, wp._TRAINER_MERIT_FEATURES)
            for v, fs in zip(_f["trainer_win_pct_365d"], _f["field_size"])
        ]
        _f.loc[:, "jockey_merit"] = [
            wp._merit_term(v, fs, jockey_merit_model, wp._JOCKEY_MERIT_FEATURES)
            for v, fs in zip(_f["jockey_win_pct_90d"], _f["field_size"])
        ]
        _f.loc[:, "closing_merit"] = [
            wp._closing_merit_term(pairs, pace_baseline_lookup, fs, closing_merit_model)
            for pairs, fs in zip(_f["closing_pairs"], _f["field_size"])
        ]
        for _term in ("track_barrier", "closing_merit", "trainer_merit", "jockey_merit"):
            _f[_term] = _f[_term] - _f.groupby("race_id")[_term].transform("mean")
        _f[wp.ADJ_TERMS] = _f[wp.ADJ_TERMS].fillna(0.0)
        gear_bucket = _f["gear_changes"].apply(wp._gear_change_bucket)
        _f.loc[:, "gear_code"] = gear_bucket.map(wp._GEAR_BUCKET_CODE).fillna(0).astype(int)

    jf = [f for f in BASE_JOINT_FEATURES if f in fit_half.columns]
    for c in jf:
        if fit_half[c].isna().any() or held_out[c].isna().any():
            _fill = fit_half[c].median()
            fit_half[c] = fit_half[c].fillna(_fill)
            held_out[c] = held_out[c].fillna(_fill)

    joint_model = lgb.LGBMRegressor(objective="quantile", alpha=0.5, n_estimators=350,
                                    max_depth=3, learning_rate=0.04, num_leaves=8,
                                    random_state=42, verbosity=-1)
    joint_model.fit(fit_half[jf], fit_half["target"])

    fit_half["additive_pred"] = _additive_predict(fit_half)
    fit_half["joint_pred"] = joint_model.predict(fit_half[jf])
    held_out["additive_pred"] = _additive_predict(held_out)
    held_out["joint_pred"] = joint_model.predict(held_out[jf])

    for pred_col in ("additive_pred", "joint_pred"):
        beta = _fit_beta(fit_half, pred_col)
        held_out[f"edge_{pred_col}"] = _edge_from_pred(held_out, pred_col, beta)
        held_out[f"beta_{pred_col}"] = beta
    return held_out


def _brier(data, beta, pred_col):
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


def _fit_beta(fit_half, pred_col):
    best_beta, best_brier = None, float("inf")
    for b in BETA_GRID:
        br = _brier(fit_half, b, pred_col)
        if br < best_brier:
            best_brier, best_beta = br, b
    return best_beta


def _edge_from_pred(frame, pred_col, beta):
    e = np.exp(beta * (frame[pred_col] - frame.groupby("race_id")[pred_col].transform("max")))
    denom = frame.groupby("race_id")[pred_col].transform(
        lambda s: np.exp(beta * (s - s.max())).sum())
    p_model = e / denom
    p_mkt = (1.0 / frame["sp"]) / frame.groupby("race_id")["sp"].transform(lambda s: (1.0 / s).sum())
    return p_model - p_mkt


def report(sub, label):
    if len(sub) < 20:
        print(f"    {label}: n={len(sub)} (too small, skipped)")
        return
    profit = np.where(sub["won"] == 1, sub["sp"] - 1, -1.0)
    se = profit.std(ddof=1) / np.sqrt(len(profit))
    t = profit.mean() / se if se > 0 else float("nan")
    flag = "  ** SIGNIFICANT **" if abs(t) >= 1.96 else ""
    print(f"    {label}: n={len(sub):5d}  strike={sub['won'].mean()*100:5.2f}%  "
          f"ROI={profit.sum()/len(sub)*100:+6.2f}%  t={t:+.2f}{flag}")


def report_edge(bets, edge_col, label):
    print(f"\n{'='*70}\n{label}\n{'='*70}")
    print(f"total held-out bets: {len(bets):,}  [population avg price ${bets['sp'].mean():.2f}]\n")
    print("=== Edge threshold alone ===")
    for thr in EDGE_THRESHOLDS:
        report(bets[bets[edge_col] >= thr], f"edge>={thr:.2f}")
    print("\n=== Edge threshold x price cap ===")
    for thr in EDGE_THRESHOLDS:
        base = bets[bets[edge_col] >= thr]
        for cap in PRICE_CAPS:
            report(base[base["sp"] <= cap], f"edge>={thr:.2f}, price<={cap:.0f}")


mid = D["date"].quantile(0.5)
h1, h2 = D[D["date"] < mid].copy(), D[D["date"] >= mid].copy()
print(f"\nH1: {len(h1):,} rows (< {mid.date()}), H2: {len(h2):,} rows (>= {mid.date()})")

print("\nFitting on H1, scoring held-out H2...")
h2_scored = fit_and_score(h1, h2)
print(f"  H1-fit beta: additive={h2_scored['beta_additive_pred'].iloc[0]}  "
      f"joint={h2_scored['beta_joint_pred'].iloc[0]}")

print("\nFitting on H2, scoring held-out H1...")
h1_scored = fit_and_score(h2, h1)
print(f"  H2-fit beta: additive={h1_scored['beta_additive_pred'].iloc[0]}  "
      f"joint={h1_scored['beta_joint_pred'].iloc[0]}")

pooled = pd.concat([h1_scored, h2_scored], ignore_index=True)
print(f"\nPooled leak-free held-out set: {len(pooled):,} rows")

report_edge(pooled, "edge_additive_pred", "CURRENT ADDITIVE architecture - LEAK-FREE")
report_edge(pooled, "edge_joint_pred", "JOINT model - LEAK-FREE")

print(f"\n{'='*70}\nFAVOURITE-LONGSHOT BIAS CHECK (edge>=0.10 bets, by price bucket)\n{'='*70}")
PRICE_BUCKETS = [1.0, 3.0, 5.0, 8.0, 15.0, 26.0, 1e9]
PRICE_BUCKET_LABELS = ["<3", "3-5", "5-8", "8-15", "15-26", ">26"]
pooled["bucket"] = pd.cut(pooled["sp"], bins=PRICE_BUCKETS, labels=PRICE_BUCKET_LABELS, right=False)
print("\n--- Baseline: back every runner in each price bucket, no model ---")
for b in PRICE_BUCKET_LABELS:
    report(pooled[pooled["bucket"] == b], f"bucket ${b} (unconditional)")
for edge_col, name in [("edge_additive_pred", "ADDITIVE"), ("edge_joint_pred", "JOINT")]:
    print(f"\n--- {name}: edge>=0.10-selected bets, by price bucket ---")
    sub = pooled[pooled[edge_col] >= 0.10]
    for b in PRICE_BUCKET_LABELS:
        report(sub[sub["bucket"] == b], f"{name} edge>=0.10, bucket ${b}")

print("\nSame multiple-comparisons caveat every backtest in this codebase carries:")
print("treat this as a hypothesis for a future walk-forward period, not a result to ship blind.")
print("\nDone.")
