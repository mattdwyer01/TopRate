"""
wpr_race_speed_feature_search_v3.py - three NEW candidates for
race_speed_estimate.py, none tried before (checked first, see below).

PRIOR ART CHECKED BEFORE BUILDING THIS (Sep 2026, see chat) - do not
re-propose these:
  - going / track-grading, barrier-relative: tested and rejected
    (race_speed_estimate.py's train() docstring, "Aug 2026 backtest").
  - same_day_pace_so_far: statistically validated bidirectionally but
    dead on arrival for live use (toprate.au never surfaces same-day
    results intra-meeting) - see wpr_race_speed_feature_search_v1.py /
    v2.py's docstrings.
  - track_hist_tempo (per-track trailing mean raceShapeEarly): built in
    v1.py, not present in the shipped race_speed_config.json's feature
    list, so not adopted (result not re-derived here - out of scope for
    this pass, which is about untested ground).
  - mean_jockey_forward / n_forward_jockeys (jockey's own trailing
    settle tendency): built in v2.py, also absent from the shipped
    feature list.
  Confirmed via race_speed_config.json's own "features" list (23
  entries, none of the above) rather than assumed.

THREE NEW CANDIDATES THIS SESSION
  1. race_class: this race's class/grade (MAI, OPEN, BM72, CLS1, etc,
     99.5% populated in wpr_form_history.csv.gz) - a genuinely different
     kind of signal (how competitively/professionally a race is likely
     to be run) that nothing in the existing 24 features captures.
     Passed to LightGBM as a native categorical column (pandas
     'category' dtype), not manually encoded - avoids guessing an
     ordinal ranking across ~40 distinct class strings.
  2. n_first_starters: count of runners in the field (the SAME sparse
     runners _race_features() already sees) with ZERO prior rows in
     wpr_form_history.csv.gz strictly before today's date - a same-grain
     proxy for "genuinely new to racing," since no separate authoritative
     first-starter flag is available on this historical file (leakage-
     free by construction: only counts what would have been knowable at
     the time). An inexperienced field runs less predictably.
  3. leader_barrier_std: NOT the same as the already-rejected plain
     "barrier-relative" feature - an INTERACTION between barrier and the
     field's own predicted running style. Among runners whose OWN prior
     mean relative settle (the same rel used for n_leaders/n_onpace)
     already marks them a likely leader (rel <= 0.20), the standard
     deviation of THEIR barriers. Low = confirmed leaders drawn close
     together (classically a genuine speed battle, since they must fight
     for the rail early); high/NaN = leaders spread out or too few of
     them to say. Racing logic the plain mean-barrier-of-the-whole-field
     feature cannot express.

METHOD: reuses race_speed_estimate.py's own train()/held-out split
convention exactly (race-level, 70th percentile date cutoff, LightGBM,
same hyperparameters), same as v1/v2 - added ONE AT A TIME against the
current 24-feature baseline, not combined, so each candidate's own
marginal contribution is visible.

NO EM DASHES policy: hyphens only.
"""
import numpy as np
import pandas as pd
import lightgbm as lgb

import race_speed_estimate as rse


def build_first_seen_lookup(fh):
    """horse_lc -> earliest date seen anywhere in fh. A runner counts as
    a first starter in a given race if that race's date is <= this
    (i.e. fh has no row for this horse strictly before today - the
    leakage-free definition _prior_means already uses elsewhere)."""
    return fh.groupby("horse_lc")["date"].min().to_dict()


def add_v3_features(feat, race_runners, pmeans, first_seen, race_date):
    # --- race_class: race-level, constant across the group's runners ---
    rc = race_runners["race_class"].dropna()
    feat["race_class"] = rc.iloc[0] if len(rc) else None

    # --- n_first_starters ---
    n_first = 0
    for h in race_runners["horse"]:
        hl = str(h).strip().lower()
        fs_date = first_seen.get(hl)
        if fs_date is None or fs_date >= race_date:
            n_first += 1
    feat["n_first_starters"] = float(n_first)

    # --- leader_barrier_std ---
    leader_barriers = []
    for _, r in race_runners.iterrows():
        hl = str(r.get("horse", "")).strip().lower()
        ps = pmeans["positionSettled"].get(hl, np.nan)
        fsz = pmeans["field_size"].get(hl, np.nan)
        rel = (ps / fsz) if (ps == ps and fsz == fsz and fsz > 0) else np.nan
        if rel == rel and rel <= 0.20:
            b = r.get("barrier")
            if b is not None and str(b) != "nan":
                leader_barriers.append(float(b))
    feat["leader_barrier_std"] = float(np.std(leader_barriers)) if len(leader_barriers) >= 2 else np.nan
    feat["n_confirmed_leaders"] = float(len(leader_barriers))
    return feat


def run(limit=None):
    print("Loading form history...")
    fh_full = rse._load_and_prep_form()
    print(f"  {len(fh_full):,} rows (one per horse+date), {fh_full['horse_lc'].nunique():,} horses")

    # first_seen needs each horse's TRUE earliest-ever appearance, so it
    # is built from the FULL unbounded history (one single groupby, cheap)
    # BEFORE bounding fh down below - otherwise a horse whose real career
    # started years earlier would wrongly look like a first starter the
    # moment it appears inside the bounded window.
    first_seen = build_first_seen_lookup(fh_full)

    # Same memory-safety bound v1.py/v2.py already established in this
    # exact sandbox: fh's raw archive goes back to 2017 (2,839+ distinct
    # days), and the per-day pmeans_cache built below (one expensive
    # _prior_means() lookup structure per unique day) grows large enough
    # over that full range to risk OOM (confirmed directly in a prior
    # session, ~13.3GB cgroup limit). Bounding to the last 2 years keeps
    # this comfortably within it while still giving a large sample.
    since = fh_full["date"].max() - pd.Timedelta(days=730)
    fh = fh_full[fh_full["date"] >= since].copy()
    print(f"  bounded to last 2 years ({since.date()} onward) for pmeans/race-building: {len(fh):,} rows")

    fh2 = fh.dropna(subset=["track", "raceNumber", "raceShapeEarly"])
    fh2 = fh2.copy()
    fh2["race_key"] = (fh2["track"].astype(str) + "|" + fh2["date"].astype(str)
                        + "|" + fh2["raceNumber"].astype(str))

    race_meta = (fh2.groupby("race_key")
                   .agg(date=("date", "first"), rse=("raceShapeEarly", "first"),
                        n=("horse_lc", "count"))
                   .reset_index())
    race_meta = race_meta[race_meta["n"] >= 4]
    print(f"  {len(race_meta):,} races with 4+ runners and a known raceShapeEarly")
    if limit:
        race_meta = race_meta.sort_values("date").tail(limit)
        print(f"  --limit applied: using most recent {len(race_meta):,} races (smoke test)")

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
        n = len(race_df)
        for i, (day, day_races) in enumerate(race_df.groupby(race_df["date"].dt.normalize())):
            pmeans = prior_means_cached(day)
            for _, rr in day_races.iterrows():
                runners = fh_by_race.get_group(rr["race_key"])
                feat = rse._race_features(runners, pmeans)
                feat = add_v3_features(feat, runners, pmeans, first_seen, rr["date"])
                rows.append(feat)
                ys.append(rr["rse"])
        print(f"  {label}: {len(rows):,} rows built")
        return pd.DataFrame(rows), np.array(ys, dtype=float)

    print("Building training rows...")
    Xtr, ytr = build_rows(train_races, "train")
    print("Building held-out rows...")
    Xte, yte = build_rows(test_races, "test")

    # race_class as a shared categorical dtype across train+test so
    # LightGBM sees consistent category codes on both sides.
    combined_rc = pd.concat([Xtr["race_class"], Xte["race_class"]]).astype("category")
    Xtr["race_class"] = combined_rc.iloc[:len(Xtr)].values
    Xte["race_class"] = combined_rc.iloc[len(Xtr):].values

    baseline_features = [c for c in Xtr.columns if c not in
                          ("race_class", "n_first_starters", "leader_barrier_std", "n_confirmed_leaders")]
    print(f"\nBaseline: {len(baseline_features)} features")

    def fit_and_score(feature_list, label):
        Xtr_f = Xtr[feature_list].copy()
        Xte_f = Xte[feature_list].copy()
        numeric_cols = [c for c in feature_list if c != "race_class"]
        med = Xtr_f[numeric_cols].median()
        Xtr_f[numeric_cols] = Xtr_f[numeric_cols].fillna(med)
        Xte_f[numeric_cols] = Xte_f[numeric_cols].fillna(med)
        cat_features = ["race_class"] if "race_class" in feature_list else "auto"
        model = lgb.LGBMRegressor(n_estimators=200, max_depth=3, learning_rate=0.05,
                                  num_leaves=8, random_state=42, verbosity=-1)
        model.fit(Xtr_f, ytr, categorical_feature=cat_features)
        pred = model.predict(Xte_f)
        corr = float(np.corrcoef(pred, yte)[0, 1])
        print(f"  {label}: held-out correlation = {corr:+.4f}  ({len(feature_list)} features)")
        return corr

    print("\n=== Held-out correlation comparison (one candidate at a time) ===")
    c_base = fit_and_score(baseline_features, "BASELINE")
    c_class = fit_and_score(baseline_features + ["race_class"], "+ race_class")
    c_first = fit_and_score(baseline_features + ["n_first_starters"], "+ n_first_starters")
    c_leader = fit_and_score(baseline_features + ["leader_barrier_std", "n_confirmed_leaders"],
                              "+ leader_barrier_std + n_confirmed_leaders")
    c_all = fit_and_score(baseline_features + ["race_class", "n_first_starters",
                                                "leader_barrier_std", "n_confirmed_leaders"],
                           "+ all three combined")

    print(f"\nBaseline:                             {c_base:+.4f}")
    print(f"+ race_class:                         {c_class:+.4f}  (delta {c_class-c_base:+.4f})")
    print(f"+ n_first_starters:                   {c_first:+.4f}  (delta {c_first-c_base:+.4f})")
    print(f"+ leader_barrier_std/n_confirmed:      {c_leader:+.4f}  (delta {c_leader-c_base:+.4f})")
    print(f"+ all three combined:                 {c_all:+.4f}  (delta {c_all-c_base:+.4f})")
    print("\nDone.")


if __name__ == "__main__":
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--limit", type=int, default=None, help="use only the N most recent races (smoke test)")
    args = ap.parse_args()
    run(limit=args.limit)
