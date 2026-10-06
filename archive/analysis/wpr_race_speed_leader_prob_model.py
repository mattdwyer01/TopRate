"""
wpr_race_speed_leader_prob_model.py - the structurally different idea
left after four straight nulls tonight (thresholds, field completeness,
plain tactical features, hyperparameter tuning - see chat, Sep 2026).

THE IDEA
  n_leaders/n_onpace (existing features) count how many runners have a
  raw historical mean relative-settle <= a FIXED threshold (0.20/0.40) -
  completely blind to barrier, distance, or anything about today's
  actual race. Diagnostic_check.py already showed n_leaders contributes
  EXACTLY 0% importance to the shipped model. Instead of a fixed
  threshold on a raw average, fit an actual per-HORSE classifier:
  P(this horse settles as a leader TODAY | its own trailing settle/
  sectional history, barrier, distance) - then aggregate those FITTED
  probabilities (mean/max/std/count-above-threshold across the field)
  into new race-level features for the existing race-shape model.

LEAKAGE DISCIPLINE (the real risk with any two-stage model like this)
  The leader-classifier is fit ONLY on the outer-TRAIN runners (same
  70/30 chronological cut every other script tonight used). Its
  predictions for OUTER-TRAIN rows themselves are generated via 5-fold
  cross-fitting (out-of-fold) - a classifier trivially "predicts" the
  labels it was directly fit on, which would leak into the race-level
  model's own training features and look far more informative there
  than at serving time. OUTER-TEST rows get a single set of predictions
  from the classifier fit on the FULL outer-train (never touching
  outer-test), exactly mirroring how the real race-shape model itself is
  fit once and then served on later dates it never trained on.

METHOD
  1. Build one row per (horse, historical run) across the SAME 2-year-
     bounded population every script tonight used, with features drawn
     from _prior_means() (barrier, distance, own trailing rel/sectionals -
     already leakage-free by construction) and the label = did this
     horse ACTUALLY settle in the front 20% of the field this run.
  2. Fit/cross-fit a LightGBM classifier as above.
  3. Aggregate predicted P(lead) per race (mean/max/std/n above 0.3) and
     feed those as NEW candidate features into the EXACT SAME race-shape
     model/evaluation harness wpr_race_speed_feature_search_v3.py and
     wpr_race_speed_diagnostic_check.py already used - same outer-test
     set, so the result is directly comparable to every number reported
     tonight.

NO EM DASHES policy: hyphens only.
"""
import numpy as np
import pandas as pd
import lightgbm as lgb
from sklearn.model_selection import KFold

import race_speed_estimate as rse

LEADER_REL_THRESHOLD = 0.20
P_LEAD_FLAG_THRESHOLD = 0.30


def load_bounded_form():
    print("Loading form history...")
    fh_full = rse._load_and_prep_form()
    since = fh_full["date"].max() - pd.Timedelta(days=730)
    fh = fh_full[fh_full["date"] >= since].copy()
    print(f"  bounded to last 2 years ({since.date()} onward): {len(fh):,} rows")
    return fh


def build_race_meta(fh):
    fh2 = fh.dropna(subset=["track", "raceNumber", "raceShapeEarly"]).copy()
    fh2["race_key"] = (fh2["track"].astype(str) + "|" + fh2["date"].astype(str)
                        + "|" + fh2["raceNumber"].astype(str))
    race_meta = (fh2.groupby("race_key")
                   .agg(date=("date", "first"), rse=("raceShapeEarly", "first"),
                        n=("horse_lc", "count"))
                   .reset_index())
    race_meta = race_meta[race_meta["n"] >= 4].sort_values("date").reset_index(drop=True)
    print(f"  {len(race_meta):,} races with 4+ runners and a known raceShapeEarly")
    return fh2, race_meta


def build_runner_rows(fh2, race_meta):
    """One row per (horse, historical run) for every race in race_meta:
    leader-classifier features (from _prior_means, leakage-free) + the
    ACTUAL outcome label for that run (from the run's own real
    positionSettled/field_size, not a prior average - this IS what the
    classifier is trying to predict)."""
    fh_by_race = fh2.groupby("race_key")
    pmeans_cache = {}
    rows = []
    n = len(race_meta)
    for i, (day, day_races) in enumerate(race_meta.groupby(race_meta["date"].dt.normalize())):
        if day not in pmeans_cache:
            pmeans_cache[day] = rse._prior_means(fh2, day)
        pmeans = pmeans_cache[day]
        for _, rr in day_races.iterrows():
            runners = fh_by_race.get_group(rr["race_key"])
            for _, r in runners.iterrows():
                hl = str(r.get("horse", "")).strip().lower()
                ps = pd.to_numeric(r.get("positionSettled"), errors="coerce")
                fsz = pd.to_numeric(r.get("field_size"), errors="coerce")
                if pd.isna(ps) or pd.isna(fsz) or fsz <= 0:
                    continue
                actual_rel = ps / fsz
                b = r.get("barrier")
                barrier = float(b) if b is not None and str(b) != "nan" else np.nan
                dist = pd.to_numeric(r.get("distance"), errors="coerce")
                own_rel = pmeans["positionSettled"].get(hl, np.nan)
                own_fs = pmeans["field_size"].get(hl, np.nan)
                own_prior_rel = (own_rel / own_fs) if (own_rel == own_rel and own_fs == own_fs and own_fs > 0) else np.nan
                rows.append({
                    "race_key": rr["race_key"], "date": rr["date"],
                    "barrier": barrier, "distance": dist,
                    "own_prior_rel": own_prior_rel,
                    "own_prior_ld": pmeans["sect_ld_early"].get(hl, np.nan),
                    "own_prior_ie": pmeans["sect_i_early"].get(hl, np.nan),
                    "own_prior_t8": pmeans["sect_i_to800"].get(hl, np.nan),
                    "label_is_leader": int(actual_rel <= LEADER_REL_THRESHOLD),
                })
    print(f"  {len(rows):,} runner-rows built")
    return pd.DataFrame(rows)


def fit_and_score_leader_model(runner_rows, outer_cut):
    """Returns runner_rows with a new 'p_lead' column - out-of-fold
    predictions for outer-train rows (5-fold, leakage-free), direct
    predictions (from a model fit on ALL of outer-train) for outer-test
    rows."""
    feat_cols = ["barrier", "distance", "own_prior_rel", "own_prior_ld", "own_prior_ie", "own_prior_t8"]
    train_mask = runner_rows["date"] < outer_cut
    test_mask = ~train_mask

    Xtr = runner_rows.loc[train_mask, feat_cols]
    ytr = runner_rows.loc[train_mask, "label_is_leader"].to_numpy()
    med = Xtr.median()
    Xtr_f = Xtr.fillna(med)

    print(f"  leader-classifier train rows: {len(Xtr):,} ({ytr.mean()*100:.1f}% positive)")

    p_lead = pd.Series(index=runner_rows.index, dtype=float)

    kf = KFold(n_splits=5, shuffle=True, random_state=42)
    for fold_i, (fit_idx, oof_idx) in enumerate(kf.split(Xtr_f)):
        clf = lgb.LGBMClassifier(n_estimators=150, max_depth=3, num_leaves=8,
                                 learning_rate=0.05, random_state=42, verbosity=-1)
        clf.fit(Xtr_f.iloc[fit_idx], ytr[fit_idx])
        oof_pred = clf.predict_proba(Xtr_f.iloc[oof_idx])[:, 1]
        p_lead.iloc[Xtr_f.index.get_indexer(Xtr_f.iloc[oof_idx].index)] = oof_pred
    print(f"  5-fold out-of-fold predictions built for outer-train rows")

    final_clf = lgb.LGBMClassifier(n_estimators=150, max_depth=3, num_leaves=8,
                                   learning_rate=0.05, random_state=42, verbosity=-1)
    final_clf.fit(Xtr_f, ytr)
    Xte = runner_rows.loc[test_mask, feat_cols].fillna(med)
    p_lead.loc[test_mask] = final_clf.predict_proba(Xte)[:, 1]
    print(f"  outer-test predictions built from classifier fit on full outer-train")

    from sklearn.metrics import roc_auc_score
    train_auc = roc_auc_score(ytr, p_lead.loc[train_mask])
    yte = runner_rows.loc[test_mask, "label_is_leader"].to_numpy()
    test_auc = roc_auc_score(yte, p_lead.loc[test_mask])
    print(f"  leader-classifier AUC: train(oof)={train_auc:.3f}  test={test_auc:.3f}"
          f"  (0.5 = no better than chance)")

    runner_rows = runner_rows.copy()
    runner_rows["p_lead"] = p_lead
    return runner_rows


def aggregate_race_features(runner_rows):
    def agg(g):
        p = g["p_lead"].dropna()
        return pd.Series({
            "mean_p_lead": p.mean() if len(p) else np.nan,
            "max_p_lead": p.max() if len(p) else np.nan,
            "std_p_lead": p.std() if len(p) >= 2 else np.nan,
            "n_p_lead_ge_03": (p >= P_LEAD_FLAG_THRESHOLD).sum(),
        })
    return runner_rows.groupby("race_key").apply(agg)


def run(limit=None):
    fh = load_bounded_form()
    fh2, race_meta = build_race_meta(fh)
    if limit:
        race_meta = race_meta.tail(limit).reset_index(drop=True)
        print(f"  --limit applied: using most recent {len(race_meta):,} races (smoke test)")

    print("\nBuilding per-runner rows for the leader classifier...")
    runner_rows = build_runner_rows(fh2, race_meta)

    outer_cut = race_meta["date"].quantile(0.70)
    print(f"\nOuter split at {outer_cut.date()} (identical to every other script tonight)")

    print("\nFitting leader-probability classifier (5-fold cross-fit on outer-train)...")
    runner_rows = fit_and_score_leader_model(runner_rows, outer_cut)

    print("\nAggregating predicted leader probabilities to race level...")
    race_feats = aggregate_race_features(runner_rows)
    print(f"  {len(race_feats):,} races with aggregated leader-probability features")

    # ---- Now feed into the EXISTING race-shape model, same harness as v3 ----
    print("\nBuilding baseline race-shape features (same as diagnostic_check.py)...")
    fh_by_race = fh2.groupby("race_key")
    pmeans_cache = {}

    def build_rows(race_df, label):
        rows, ys = [], []
        for day, day_races in race_df.groupby(race_df["date"].dt.normalize()):
            if day not in pmeans_cache:
                pmeans_cache[day] = rse._prior_means(fh, day)
            pmeans = pmeans_cache[day]
            for _, rr in day_races.iterrows():
                runners = fh_by_race.get_group(rr["race_key"])
                feat = rse._race_features(runners, pmeans)
                feat["race_key"] = rr["race_key"]
                rows.append(feat)
                ys.append(rr["rse"])
        print(f"  {label}: {len(rows):,} rows built")
        return pd.DataFrame(rows), np.array(ys, dtype=float)

    train_races = race_meta[race_meta["date"] < outer_cut]
    test_races = race_meta[race_meta["date"] >= outer_cut]
    Xtr, ytr = build_rows(train_races, "outer-train")
    Xte, yte = build_rows(test_races, "outer-test")

    Xtr = Xtr.merge(race_feats, left_on="race_key", right_index=True, how="left").drop(columns=["race_key"])
    Xte = Xte.merge(race_feats, left_on="race_key", right_index=True, how="left").drop(columns=["race_key"])

    baseline_features = [c for c in Xtr.columns if c not in
                          ("mean_p_lead", "max_p_lead", "std_p_lead", "n_p_lead_ge_03")]

    def fit_and_score(feature_list, label):
        med = Xtr[feature_list].median()
        Xtr_f = Xtr[feature_list].fillna(med)
        Xte_f = Xte[feature_list].fillna(med)
        model = lgb.LGBMRegressor(n_estimators=200, max_depth=3, learning_rate=0.05,
                                  num_leaves=8, random_state=42, verbosity=-1)
        model.fit(Xtr_f, ytr)
        pred = model.predict(Xte_f)
        corr = float(np.corrcoef(pred, yte)[0, 1])
        print(f"  {label}: held-out correlation = {corr:+.4f}")
        return corr

    print("\n" + "=" * 78)
    print("RESULT: does the fitted leader-probability signal beat the dead-weight n_leaders?")
    print("=" * 78)
    c_base = fit_and_score(baseline_features, "BASELINE (24 features, incl. dead-weight n_leaders)")
    c_mean = fit_and_score(baseline_features + ["mean_p_lead"], "+ mean_p_lead")
    c_max = fit_and_score(baseline_features + ["max_p_lead"], "+ max_p_lead")
    c_all = fit_and_score(baseline_features + ["mean_p_lead", "max_p_lead", "std_p_lead", "n_p_lead_ge_03"],
                           "+ all four leader-probability features")

    print(f"\nBaseline (diagnostic_check.py's own number on this exact test set): +0.2959")
    print(f"This run's baseline (should match closely):  {c_base:+.4f}")
    print(f"+ mean_p_lead:                                {c_mean:+.4f}  (delta {c_mean-c_base:+.4f})")
    print(f"+ max_p_lead:                                 {c_max:+.4f}  (delta {c_max-c_base:+.4f})")
    print(f"+ all four:                                   {c_all:+.4f}  (delta {c_all-c_base:+.4f})")


if __name__ == "__main__":
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--limit", type=int, default=None, help="use only the N most recent races (smoke test)")
    args = ap.parse_args()
    run(limit=args.limit)
