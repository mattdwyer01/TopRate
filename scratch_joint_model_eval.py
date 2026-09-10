"""
scratch_joint_model_eval.py
----------------------------
One-off, throwaway comparison: does training ONE joint model (base signals +
every ADJ_TERM's raw underlying features, all together) beat the current
live architecture (a fixed 0.30/0.70 wpr_nett/ewm5 base blend, plus 11
separately-fitted/looked-up ADJ_TERMS summed on top, unshrunk) on held-out
MAE, on the SAME train/cf/test split and SAME target this repo's own
train_wpr_projection() already uses?

This mirrors train_wpr_projection()'s own data prep almost exactly (same
D/trn/cf/te split by date quantiles 0.70/0.85, same per-term feature
construction, same _additive_predict baseline) so the comparison is
apples-to-apples against the number train_wpr_projection() itself prints
as "held-out projection MAE". The only new thing added is JOINT_FEATURES
(FEATURES plus every ADJ_TERM's own raw ingredient columns) and one single
LightGBM quantile(alpha=0.5) model fit on trn[JOINT_FEATURES] -> target
directly, instead of the current base + sum(11 independently-fit terms).

Does NOT modify wpr_projection.py, does NOT touch wpr_models/*.joblib or
config.json. Read-only comparison, safe to run repeatedly.

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np
import pandas as pd
import lightgbm as lgb
from sklearn.metrics import mean_absolute_error

import wpr_projection as wp

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

# Same void/surface filters train_wpr_projection() applies, for parity.
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
D["_y"] = D["target"] - D["_base"]

med = D[wp.FEATURES].median()
D[wp.FEATURES] = D[wp.FEATURES].fillna(med)

q1, q2 = D["date"].quantile([0.70, 0.85])
trn = D[D["date"] < q1].copy()
cf = D[(D["date"] >= q1) & (D["date"] < q2)].copy()
te = D[D["date"] >= q2].copy()
print(f"trn={len(trn):,} cf={len(cf):,} te={len(te):,}")

print("fitting track_barrier model (population, trn only)...")
track_categories = sorted(D["track"].dropna().unique())
track_code_map = {t: i for i, t in enumerate(track_categories)}
for _frame in (trn, cf, te):
    _frame.loc[:, "track_code"] = _frame["track"].map(track_code_map).fillna(-1).astype(int)
track_barrier_model = wp._fit_simple_adj_model(trn, wp._TRACK_BARRIER_FEATURES, "track_barrier")
for _frame in (cf, te):
    _frame["track_barrier"] = [
        wp._track_barrier_term(trk, dist, bar, fs, track_code_map, track_barrier_model)
        for trk, dist, bar, fs in zip(_frame["track"], _frame["cur_distance"],
                                      _frame["barrier"], _frame["field_size"])
    ]

print("fitting trainer_merit / jockey_merit models...")
trainer_merit_trn = wp._fit_coverage_aware_trn(D, ["trainer_win_pct_365d"])
trainer_merit_model = wp._fit_simple_adj_model(trainer_merit_trn, wp._TRAINER_MERIT_FEATURES, "trainer_merit")
jockey_merit_trn = wp._fit_coverage_aware_trn(D, ["jockey_win_pct_90d"])
jockey_merit_model = wp._fit_simple_adj_model(jockey_merit_trn, wp._JOCKEY_MERIT_FEATURES, "jockey_merit")
for _frame in (cf, te):
    _frame["trainer_merit"] = [
        wp._merit_term(v, fs, trainer_merit_model, wp._TRAINER_MERIT_FEATURES)
        for v, fs in zip(_frame["trainer_win_pct_365d"], _frame["field_size"])
    ]
    _frame["jockey_merit"] = [
        wp._merit_term(v, fs, jockey_merit_model, wp._JOCKEY_MERIT_FEATURES)
        for v, fs in zip(_frame["jockey_win_pct_90d"], _frame["field_size"])
    ]

print("fitting gear_change model...")
for _frame in (trn, cf, te):
    _bucket = _frame["gear_changes"].apply(wp._gear_change_bucket)
    _frame.loc[:, "gear_code"] = _bucket.map(wp._GEAR_BUCKET_CODE).fillna(0).astype(int)
gear_change_model = wp._fit_simple_adj_model(trn, wp._GEAR_CHANGE_FEATURES, "gear_change")
for _frame in (cf, te):
    _frame["gear_change"] = [
        wp._gear_change_term(b, fs, fu, su, nr, gear_change_model)
        for b, fs, fu, su, nr in zip(
            _frame["gear_changes"].apply(wp._gear_change_bucket), _frame["field_size"],
            _frame["first_up"], _frame["second_up"], _frame["n_runs"])
    ]

print("fitting closing_merit pace-context baseline...")
pace_baseline_lookup = wp._fit_pace_baseline("wpr_form_history.csv.gz", q1)

def _closing_raw_resid_one(pairs):
    vals = []
    for sect, bucket in pairs:
        exp = pace_baseline_lookup.get(bucket)
        if exp is not None and sect is not None and sect == sect:
            vals.append(float(sect) - float(exp))
    return (float(np.mean(vals)), float(len(vals))) if vals else (np.nan, 0.0)

for _frame in (trn, cf, te):
    _computed = [_closing_raw_resid_one(p) for p in _frame["closing_pairs"]]
    _frame.loc[:, "closing_raw_resid"] = [c[0] for c in _computed]
    _frame.loc[:, "closing_n_pairs"] = [c[1] for c in _computed]
closing_merit_model = wp._fit_simple_adj_model(trn, wp._CLOSING_MERIT_FEATURES, "closing_merit")
for _frame in (cf, te):
    _frame["closing_merit"] = [
        wp._closing_merit_term(pairs, pace_baseline_lookup, fs, closing_merit_model)
        for pairs, fs in zip(_frame["closing_pairs"], _frame["field_size"])
    ]

for _frame in (cf, te):
    for _term in ("track_barrier", "closing_merit", "trainer_merit", "jockey_merit"):
        _frame[_term] = _frame[_term] - _frame.groupby("race_id")[_term].transform("mean")

print("fitting pace_shape model...")
pace_shape_model = wp._fit_pace_shape_model(D, _name_map)
if pace_shape_model is not None:
    for _frame in (cf, te):
        _fps = D.loc[_frame.index, ["pace_score", "predicted_rel_settle"]]
        _frame["pace_shape"] = [
            wp._pace_shape_term(ps, prs, fs, pace_shape_model)
            for ps, prs, fs in zip(_fps["pace_score"], _fps["predicted_rel_settle"],
                                   _frame["field_size"])
        ]
        _frame["settle_signal"] = (_fps["predicted_rel_settle"] - 0.5) * 2
        _frame["pace_signal"] = (_fps["pace_score"] - 0.5) * 2
        _frame["interaction"] = _frame["settle_signal"] * _frame["pace_signal"]
else:
    for _frame in (cf, te):
        _frame["pace_shape"] = 0.0
        _frame["settle_signal"] = 0.0
        _frame["pace_signal"] = 0.0
        _frame["interaction"] = 0.0
# trn needs settle/pace signal columns too (as JOINT_FEATURES inputs) -
# D already has pace_score/predicted_rel_settle from the fit call above.
trn["settle_signal"] = (D.loc[trn.index, "predicted_rel_settle"] - 0.5) * 2
trn["pace_signal"] = (D.loc[trn.index, "pace_score"] - 0.5) * 2
trn["interaction"] = trn["settle_signal"] * trn["pace_signal"]

# --- Current live architecture's held-out MAE (the number to beat) ---
def _additive_predict(frame):
    return frame["_base"].to_numpy() + wp._cap_adj_sum(
        frame[wp.ADJ_TERMS].to_numpy()).sum(axis=1)

te_pred_current = _additive_predict(te)
mae_current = mean_absolute_error(te["target"], te_pred_current)
print(f"\n=== CURRENT additive architecture: held-out MAE = {mae_current:.4f} ===")

# --- Joint model: one LightGBM quantile(0.5) model on base + every
# ADJ_TERM's raw underlying feature, predicting target directly. ---
JOINT_FEATURES = list(wp.FEATURES) + [
    "barrier", "track_code",
    "trainer_win_pct_365d", "jockey_win_pct_90d",
    "gear_code",
    "closing_raw_resid", "closing_n_pairs",
    "settle_signal", "pace_signal", "interaction",
]
JOINT_FEATURES = [f for f in JOINT_FEATURES if f in trn.columns]
missing = [f for f in (list(wp.FEATURES) + [
    "barrier", "track_code", "trainer_win_pct_365d", "jockey_win_pct_90d",
    "gear_code", "closing_raw_resid", "closing_n_pairs",
    "settle_signal", "pace_signal", "interaction"]) if f not in trn.columns]
if missing:
    print(f"NOTE: dropped missing columns from JOINT_FEATURES: {missing}")
print(f"\nJOINT_FEATURES ({len(JOINT_FEATURES)}): {JOINT_FEATURES}")

for c in JOINT_FEATURES:
    if trn[c].isna().any() or cf[c].isna().any() or te[c].isna().any():
        _fill = trn[c].median()
        trn[c] = trn[c].fillna(_fill)
        cf[c] = cf[c].fillna(_fill)
        te[c] = te[c].fillna(_fill)

joint_model = lgb.LGBMRegressor(objective="quantile", alpha=0.5, n_estimators=350,
                                max_depth=3, learning_rate=0.04, num_leaves=8,
                                random_state=42, verbosity=-1)
joint_model.fit(trn[JOINT_FEATURES], trn["target"])
te_pred_joint = joint_model.predict(te[JOINT_FEATURES])
mae_joint = mean_absolute_error(te["target"], te_pred_joint)
print(f"\n=== JOINT model (base+adj features, one model): held-out MAE = {mae_joint:.4f} ===")

print(f"\nDelta: {mae_joint - mae_current:+.4f} MAE "
      f"({'JOINT WINS' if mae_joint < mae_current else 'CURRENT ADDITIVE WINS'})")

print("\nTop 20 joint model feature importances:")
for feat, imp in sorted(zip(JOINT_FEATURES, joint_model.feature_importances_),
                        key=lambda x: -x[1])[:20]:
    print(f"  {feat:24s} {imp}")

# Also try a couple of depth/leaf settings quickly, in case max_depth=3 is
# too shallow to represent a genuinely joint base+adjustment interaction
# (the additive architecture's whole premise is a flexible per-term fit
# summed together - a single shallow tree model might need more capacity
# to match that, or might already win with less).
print("\n--- Capacity sweep (same JOINT_FEATURES, varying depth/leaves) ---")
for max_depth, num_leaves, n_estimators in [(4, 16, 400), (5, 31, 400), (3, 8, 600)]:
    m = lgb.LGBMRegressor(objective="quantile", alpha=0.5, n_estimators=n_estimators,
                          max_depth=max_depth, learning_rate=0.04, num_leaves=num_leaves,
                          random_state=42, verbosity=-1)
    m.fit(trn[JOINT_FEATURES], trn["target"])
    mae_v = mean_absolute_error(te["target"], m.predict(te[JOINT_FEATURES]))
    print(f"  depth={max_depth} leaves={num_leaves} n_est={n_estimators}: MAE={mae_v:.4f}")

print("\nDone.")
