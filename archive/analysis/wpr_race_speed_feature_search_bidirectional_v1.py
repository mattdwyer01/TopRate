"""
wpr_race_speed_feature_search_bidirectional_v1.py - second-direction check
on wpr_race_speed_feature_search_v1.py's result (same_day_pace_so_far
took held-out correlation from +0.2934 to +0.3445, single direction only -
train on the oldest 70% of races, test on the newest 30%, matching
race_speed_estimate.py's own train() convention).

This codebase's own higher bar (used for every WPR ADJ_TERMS decision, and
for the void-marker expansion validated earlier today) requires BOTH
directions of a swapped chronological split to agree before trusting a
result. race_speed_estimate.py's own train() has never applied that bar to
itself (it only reports one direction) - this checks whether the new
same_day_pace_so_far/track_hist_tempo features would survive it anyway.

EFFICIENCY NOTE: unlike the void-marker bidirectional check (which needed a
full separate model BUILD per direction, because track_barrier/closing_merit
are population lookups fit differently depending which half is "trn"), the
race-speed candidate features here are already fully causal per-row
(same_day_pace_so_far and track_hist_tempo are each computed from strictly
EARLIER rows than the row itself, regardless of which train/test split a
downstream model uses) - so this script builds every race's feature row
ONCE, then evaluates two different chronological partitions of that same
already-built table. No second expensive build needed.

Same 2-year window bound as v1 (see its own comment for why - the raw
archive goes back to 2017, and the pmeans_cache{} pattern this reuses
OOM-killed v1 twice before that bound was added).

NO EM DASHES policy: hyphens only.
"""
import numpy as np
import pandas as pd
import lightgbm as lgb

import race_speed_estimate as rse
from wpr_race_speed_feature_search_v1 import build_same_day_and_track_hist

FORM_CSV = "wpr_form_history.csv.gz"


def run():
    print("Loading form history...")
    fh = rse._load_and_prep_form()
    fh = fh.dropna(subset=["track", "raceNumber", "raceShapeEarly"])

    since = fh["date"].max() - pd.Timedelta(days=730)
    n_before = len(fh)
    fh = fh[fh["date"] >= since].copy()
    print(f"  bounded to last 2 years ({since.date()} onward): "
          f"{n_before:,} -> {len(fh):,} rows, "
          f"{fh['date'].dt.normalize().nunique():,} distinct days")

    fh["race_key"] = (fh["track"].astype(str) + "|" + fh["date"].astype(str)
                      + "|" + fh["raceNumber"].astype(str))

    race_meta = (fh.groupby("race_key")
                   .agg(date=("date", "first"), rse=("raceShapeEarly", "first"),
                        n=("horse_lc", "count"))
                   .reset_index())
    race_meta = race_meta[race_meta["n"] >= 4].sort_values("date").reset_index(drop=True)
    print(f"  {len(race_meta):,} races with 4+ runners and a known raceShapeEarly")

    print("Building same_day_pace_so_far / track_hist_tempo lookups...")
    same_day, track_hist = build_same_day_and_track_hist(fh)

    fh_by_race = fh.groupby("race_key")
    pmeans_cache = {}

    def prior_means_cached(cutoff_date):
        if cutoff_date not in pmeans_cache:
            pmeans_cache[cutoff_date] = rse._prior_means(fh, cutoff_date)
        return pmeans_cache[cutoff_date]

    print("Building feature rows for EVERY race once (reused across both directions)...")
    rows, ys, dates = [], [], []
    for day, day_races in race_meta.groupby(race_meta["date"].dt.normalize()):
        pmeans = prior_means_cached(day)
        for _, rr in day_races.iterrows():
            runners = fh_by_race.get_group(rr["race_key"])
            feat = rse._race_features(runners, pmeans)
            feat["same_day_pace_so_far"] = same_day.get(rr["race_key"], np.nan)
            feat["track_hist_tempo"] = track_hist.get(rr["race_key"], np.nan)
            rows.append(feat)
            ys.append(rr["rse"])
            dates.append(rr["date"])
    X = pd.DataFrame(rows)
    y = np.array(ys, dtype=float)
    dates = pd.Series(dates)
    print(f"  {len(X):,} race rows built")

    baseline_features = [c for c in X.columns if c not in ("same_day_pace_so_far", "track_hist_tempo")]
    feature_sets = {
        "BASELINE (24 features)": baseline_features,
        "+ same_day_pace_so_far": baseline_features + ["same_day_pace_so_far"],
        "+ track_hist_tempo": baseline_features + ["track_hist_tempo"],
        "+ both": baseline_features + ["same_day_pace_so_far", "track_hist_tempo"],
    }

    def fit_and_score(feats, trn_idx, te_idx, label):
        Xtr, ytr = X.loc[trn_idx, feats], y[trn_idx]
        Xte, yte = X.loc[te_idx, feats], y[te_idx]
        med = Xtr.median()
        Xtr_f, Xte_f = Xtr.fillna(med), Xte.fillna(med)
        model = lgb.LGBMRegressor(n_estimators=200, max_depth=3, learning_rate=0.05,
                                  num_leaves=8, random_state=42, verbosity=-1)
        model.fit(Xtr_f, ytr)
        pred = model.predict(Xte_f)
        corr = float(np.corrcoef(pred, yte)[0, 1])
        print(f"  [{label}] n_trn={len(trn_idx):,} n_te={len(te_idx):,} corr={corr:+.4f}")
        return corr

    cut_a = dates.quantile(0.70)
    idx_a_trn = dates[dates < cut_a].index
    idx_a_te = dates[dates >= cut_a].index
    print(f"\nDirection A (forward, matches v1/production): split at {cut_a.date()}, "
          f"train={len(idx_a_trn):,} test={len(idx_a_te):,}")

    cut_b = dates.quantile(0.30)
    idx_b_trn = dates[dates > cut_b].index
    idx_b_te = dates[dates <= cut_b].index
    print(f"Direction B (reversed): split at {cut_b.date()}, "
          f"train={len(idx_b_trn):,} test={len(idx_b_te):,}")

    results = {}
    for label, feats in feature_sets.items():
        print(f"\n=== {label} ===")
        ca = fit_and_score(feats, idx_a_trn, idx_a_te, "direction A (forward)")
        cb = fit_and_score(feats, idx_b_trn, idx_b_te, "direction B (reversed)")
        results[label] = (ca, cb)

    print("\n=== SUMMARY ===")
    base_a, base_b = results["BASELINE (24 features)"]
    for label, (ca, cb) in results.items():
        if label.startswith("BASELINE"):
            continue
        da, db = ca - base_a, cb - base_b
        both_better = da > 0 and db > 0
        print(f"  {label}: A {base_a:+.4f} -> {ca:+.4f} ({da:+.4f}), "
              f"B {base_b:+.4f} -> {cb:+.4f} ({db:+.4f})  "
              f"{'BOTH IMPROVED' if both_better else 'not both improved'}")

    print("\nDone.")


if __name__ == "__main__":
    run()
