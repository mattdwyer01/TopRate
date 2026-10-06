"""
wpr_race_speed_feature_search_v2.py - a NEW candidate for race_speed_estimate.py,
after v1's same_day_pace_so_far (validated bidirectionally, +0.29 -> +0.34/+0.21)
turned out to be dead on arrival for live use: toprate.au does not surface
results intra-day, only once a whole meeting is complete, so "earlier races
at today's meeting" is never actually available before a later race on the
same card. That feature is NOT being pursued further for production.

THIS candidate has no such problem: a jockey's historical tendency to ride
forward (lead/press the pace) vs sit back is knowable from the jockey's own
past rides, fully resolved well before today, completely independent of
same-day timing. Two features, mirroring the model's own existing
horse-level n_leaders/n_onpace/mean_rel/min_rel design but at the JOCKEY
level instead of the horse's own history - genuinely new information (a
first-time-forward horse booked to a notorious pace-presser is a real
signal the horse's OWN history cannot carry):

  mean_jockey_forward: mean, across today's field, of each runner's OWN
    jockey's trailing (strictly prior-date) mean relative settle position
    (positionSettled/field_size across ALL that jockey's past rides, any
    horse) - 0 = always leads, 1 = always brings up the rear.
  n_forward_jockeys: count of runners in today's field whose jockey's
    trailing mean relative settle is <= 0.30 (a genuinely front-running
    rider by history), mirroring n_leaders/n_onpace's own thresholding.

Same memory-safety bound as v1 (fh's raw archive goes back to 2017,
2,839+ distinct days - the per-day pmeans_cache pattern this reuses grows
large over that; bounding to 2 years keeps this well within this session's
sandbox memory limit, confirmed at ~13.3GB via the bash tool's own cgroup -
NOTE this OOM is a sandbox constraint, not confirmed evidence that
production itself (which last retrained successfully 2 days ago,
presumably on a different, less constrained machine) is currently broken -
worth hardening either way, not claimed as an active bug).

Reuses race_speed_estimate.py's own train()/held-out split convention,
tested BOTH directions (see wpr_race_speed_feature_search_bidirectional_v1.py
for why - this codebase's own bar for trusting a candidate change).

NO EM DASHES policy: hyphens only.
"""
import numpy as np
import pandas as pd
import lightgbm as lgb

import race_speed_estimate as rse

FORM_CSV = "wpr_form_history.csv.gz"


def build_jockey_prior_lookup(fh, cutoff_date):
    """Trailing (strictly < cutoff_date) mean relative settle position per
    jockey, across ALL of that jockey's past rides (any horse). Mirrors
    race_speed_estimate._prior_means's own per-horse pattern, at the
    jockey level instead."""
    prior = fh[fh["date"] < cutoff_date]
    if "jockey" not in prior.columns:
        return {}
    ps = pd.to_numeric(prior["positionSettled"], errors="coerce")
    fs = pd.to_numeric(prior["field_size"], errors="coerce")
    valid = (ps > 0) & (fs > 0) & prior["jockey"].notna()
    if not valid.any():
        return {}
    rel = (ps[valid] / fs[valid]).clip(0, 1)
    jockey = prior.loc[valid, "jockey"].astype(str).str.strip().str.lower()
    return rel.groupby(jockey).mean().to_dict()


def add_jockey_features(feat, race_runners, jockey_lookup):
    vals = []
    for _, r in race_runners.iterrows():
        j = str(r.get("jockey", "")).strip().lower()
        vals.append(jockey_lookup.get(j, np.nan))
    a = np.array(vals, dtype=float)
    feat["mean_jockey_forward"] = float(np.nanmean(a)) if np.isfinite(a).any() else np.nan
    feat["n_forward_jockeys"] = float(np.nansum(a <= 0.30))
    return feat


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
    print(f"  jockey coverage: {fh['jockey'].notna().mean()*100:.1f}%")

    fh["race_key"] = (fh["track"].astype(str) + "|" + fh["date"].astype(str)
                      + "|" + fh["raceNumber"].astype(str))

    race_meta = (fh.groupby("race_key")
                   .agg(date=("date", "first"), rse=("raceShapeEarly", "first"),
                        n=("horse_lc", "count"))
                   .reset_index())
    race_meta = race_meta[race_meta["n"] >= 4].sort_values("date").reset_index(drop=True)
    print(f"  {len(race_meta):,} races with 4+ runners and a known raceShapeEarly")

    fh_by_race = fh.groupby("race_key")
    pmeans_cache = {}
    jockey_cache = {}

    def prior_means_cached(cutoff_date):
        if cutoff_date not in pmeans_cache:
            pmeans_cache[cutoff_date] = rse._prior_means(fh, cutoff_date)
        return pmeans_cache[cutoff_date]

    def jockey_lookup_cached(cutoff_date):
        if cutoff_date not in jockey_cache:
            jockey_cache[cutoff_date] = build_jockey_prior_lookup(fh, cutoff_date)
        return jockey_cache[cutoff_date]

    print("Building feature rows for every race once...")
    rows, ys, dates = [], [], []
    for day, day_races in race_meta.groupby(race_meta["date"].dt.normalize()):
        pmeans = prior_means_cached(day)
        jlookup = jockey_lookup_cached(day)
        for _, rr in day_races.iterrows():
            runners = fh_by_race.get_group(rr["race_key"])
            feat = rse._race_features(runners, pmeans)
            feat = add_jockey_features(feat, runners, jlookup)
            rows.append(feat)
            ys.append(rr["rse"])
            dates.append(rr["date"])
    X = pd.DataFrame(rows)
    y = np.array(ys, dtype=float)
    dates = pd.Series(dates)
    print(f"  {len(X):,} race rows built")
    print(f"  mean_jockey_forward coverage: {X['mean_jockey_forward'].notna().mean()*100:.1f}%")

    baseline_features = [c for c in X.columns if c not in ("mean_jockey_forward", "n_forward_jockeys")]
    feature_sets = {
        "BASELINE (24 features)": baseline_features,
        "+ mean_jockey_forward": baseline_features + ["mean_jockey_forward"],
        "+ n_forward_jockeys": baseline_features + ["n_forward_jockeys"],
        "+ both jockey features": baseline_features + ["mean_jockey_forward", "n_forward_jockeys"],
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
    print(f"\nDirection A (forward): split at {cut_a.date()}, "
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
