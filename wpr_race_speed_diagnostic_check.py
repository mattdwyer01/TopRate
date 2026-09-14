"""
wpr_race_speed_diagnostic_check.py - two quick diagnostics on
race_speed_estimate.py's model, run BEFORE committing to a bigger
"per-horse leader-probability" rebuild (see chat, Sep 2026):

  1. TRAIN vs HELD-OUT correlation gap: is the model's low +0.28-0.29
     held-out correlation a genuine information ceiling (train
     correlation similarly low - more capacity would not help), or is
     it underfit/overfit (a real train/test gap - more capacity or
     regularization tuning could still move the needle)?
  2. FEATURE IMPORTANCE on the ACTUAL shipped race_speed_model.joblib
     (not a refit) - which of the 24 features the live model actually
     leans on, to tell whether effort is better spent sharpening the
     top features (e.g. a smarter, context-aware leader signal) or
     genuinely somewhere else.

Reuses the same 2-year memory-safety bound and race-building approach
as wpr_race_speed_feature_search_v3.py (baseline features only, no
candidates) for consistency with tonight's other results.

NO EM DASHES policy: hyphens only.
"""
import numpy as np
import pandas as pd
import lightgbm as lgb

import race_speed_estimate as rse


def run():
    print("=" * 72)
    print("DIAGNOSTIC 1: feature importance on the ACTUAL shipped model")
    print("=" * 72)
    rse._load_model()
    importances = rse._MODEL.feature_importances_
    features = rse._CFG["features"]
    order = np.argsort(importances)[::-1]
    total = importances.sum()
    print(f"shipped heldout_corr: {rse._CFG['heldout_corr']:+.4f}  (n_train={rse._CFG['n_train']:,})")
    print(f"\n{'feature':25s} {'importance':>12s} {'% of total':>10s}")
    for i in order:
        pct = importances[i] / total * 100 if total else 0
        print(f"{features[i]:25s} {importances[i]:12.0f} {pct:9.1f}%")

    print("\n" + "=" * 72)
    print("DIAGNOSTIC 2: train vs held-out correlation gap (fresh fit, baseline features)")
    print("=" * 72)
    print("Loading form history...")
    fh_full = rse._load_and_prep_form()
    since = fh_full["date"].max() - pd.Timedelta(days=730)
    fh = fh_full[fh_full["date"] >= since].copy()
    print(f"  bounded to last 2 years ({since.date()} onward): {len(fh):,} rows")

    fh2 = fh.dropna(subset=["track", "raceNumber", "raceShapeEarly"]).copy()
    fh2["race_key"] = (fh2["track"].astype(str) + "|" + fh2["date"].astype(str)
                        + "|" + fh2["raceNumber"].astype(str))
    race_meta = (fh2.groupby("race_key")
                   .agg(date=("date", "first"), rse=("raceShapeEarly", "first"),
                        n=("horse_lc", "count"))
                   .reset_index())
    race_meta = race_meta[race_meta["n"] >= 4]
    print(f"  {len(race_meta):,} races with 4+ runners and a known raceShapeEarly")

    cut = race_meta["date"].quantile(0.70)
    train_races = race_meta[race_meta["date"] < cut]
    test_races = race_meta[race_meta["date"] >= cut]
    print(f"  split at {cut.date()}: {len(train_races):,} train, {len(test_races):,} test")

    fh_by_race = fh2.groupby("race_key")
    pmeans_cache = {}

    def prior_means_cached(cutoff_date):
        if cutoff_date not in pmeans_cache:
            pmeans_cache[cutoff_date] = rse._prior_means(fh, cutoff_date)
        return pmeans_cache[cutoff_date]

    def build_rows(race_df, label):
        rows, ys = [], []
        for day, day_races in race_df.groupby(race_df["date"].dt.normalize()):
            pmeans = prior_means_cached(day)
            for _, rr in day_races.iterrows():
                runners = fh_by_race.get_group(rr["race_key"])
                rows.append(rse._race_features(runners, pmeans))
                ys.append(rr["rse"])
        print(f"  {label}: {len(rows):,} rows built")
        return pd.DataFrame(rows), np.array(ys, dtype=float)

    print("Building training rows...")
    Xtr, ytr = build_rows(train_races, "train")
    print("Building held-out rows...")
    Xte, yte = build_rows(test_races, "test")

    med = Xtr.median()
    Xtr_f, Xte_f = Xtr.fillna(med), Xte.fillna(med)

    model = lgb.LGBMRegressor(n_estimators=200, max_depth=3, learning_rate=0.05,
                              num_leaves=8, random_state=42, verbosity=-1)
    model.fit(Xtr_f, ytr)

    pred_tr = model.predict(Xtr_f)
    pred_te = model.predict(Xte_f)
    corr_tr = float(np.corrcoef(pred_tr, ytr)[0, 1])
    corr_te = float(np.corrcoef(pred_te, yte)[0, 1])

    print(f"\nTRAIN correlation:     {corr_tr:+.4f}  (R^2 ~ {corr_tr**2*100:.1f}%)")
    print(f"HELD-OUT correlation:  {corr_te:+.4f}  (R^2 ~ {corr_te**2*100:.1f}%)")
    print(f"GAP (train - heldout): {corr_tr-corr_te:+.4f}")
    print()
    if corr_tr - corr_te < 0.05:
        print("Small gap: train correlation is ALSO low - this is a genuine information")
        print("ceiling given the current feature set, not underfitting/overfitting. More")
        print("model capacity (deeper trees, more estimators) is unlikely to help; new")
        print("information (better features) is the only lever left.")
    else:
        print("Real gap: the model fits training data noticeably better than held-out.")
        print("There may be room for a bigger/better-regularized model on the SAME")
        print("features - worth a quick hyperparameter pass before a bigger feature build.")


if __name__ == "__main__":
    run()
