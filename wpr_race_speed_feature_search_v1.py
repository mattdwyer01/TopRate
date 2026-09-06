"""
wpr_race_speed_feature_search_v1.py - tries to improve race_speed_estimate.py's
pre-race tempo model, per direct user request: "can you first update the
model to try and improve the correlation with these factors" (race shape and
track bias), before building a manual-input capture path.

BASELINE: race_speed_estimate.py's current model gets +0.27-0.29 held-out
correlation with actual raceShapeEarly, using 24 features that are all
per-race AGGREGATES OF THE FIELD'S OWN PRIOR-RUN HISTORY (past settle
positions, past sectionals, past margins, barrier, distance). Already
TESTED AND REJECTED (per that file's own train() docstring): adding
barrier-relative and going/track-grading features on top - neither gave a
real held-out gain.

TWO NEW CANDIDATES, neither tried before, both motivated directly by
today's diagnostic findings (wpr_track_bias_pace_review_v1/v2 and
wpr_track_bias_running_tally_v1):

  1. same_day_pace_so_far: the mean ACTUAL raceShapeEarly of EARLIER races
     at the SAME (track, date) meeting, using only races that have already
     been run (>=1 prior race that day). Genuinely new information source -
     the existing model only ever looks at the field's OWN prior history,
     never at what has already happened elsewhere at TODAY's meeting. This
     is the pace-tempo equivalent of the running_tally script's barrier
     signal (which DID survive as a real, leak-safe effect) - worth testing
     directly on the pace model itself, not just as a downstream WPR
     adjustment.
  2. track_hist_tempo: a fully causal, per-TRACK trailing mean
     raceShapeEarly (computed from ALL prior days' races at that venue,
     strictly before today's date) - does this specific track typically run
     hot or run slow, independent of today's field. No batch train/test
     split needed for this one (it's naturally leak-safe per-row, computed
     from strictly-prior dates only), unlike track_barrier's population
     shrinkage fit in wpr_projection.py.

METHOD: reuses race_speed_estimate.py's own train()/held-out split
(race-level, 70th percentile date cutoff, LightGBM, same hyperparameters)
exactly, just with the 24 baseline features vs baseline+candidate(s) -
same held-out CORRELATION metric that file already reports and trusts.

NO EM DASHES policy: hyphens only.
"""
import numpy as np
import pandas as pd
import lightgbm as lgb

import race_speed_estimate as rse

FORM_CSV = "wpr_form_history.csv.gz"


def build_same_day_and_track_hist(fh):
    """Per race_key: same_day_pace_so_far (mean actual raceShapeEarly of
    earlier races at the same (track,date) meeting) and track_hist_tempo
    (trailing mean raceShapeEarly at this track from all strictly-prior
    dates). Both computed once, up front, from the full race-level table -
    entirely pre-race-safe (uses only earlier races/dates than the race
    itself)."""
    race_meta = (fh.groupby("race_key")
                   .agg(date=("date", "first"), track=("track", "first"),
                        raceNumber=("raceNumber", "first"),
                        rse=("raceShapeEarly", "first"))
                   .reset_index())
    race_meta = race_meta.sort_values(["track", "date", "raceNumber"])

    same_day = {}
    for (track, date), g in race_meta.groupby(["track", race_meta["date"].dt.normalize()]):
        g = g.sort_values("raceNumber")
        vals = []
        for _, row in g.iterrows():
            same_day[row["race_key"]] = float(np.mean(vals)) if len(vals) >= 1 else np.nan
            vals.append(row["rse"])

    track_hist = {}
    for track, g in race_meta.groupby("track"):
        g = g.sort_values("date")
        vals, dates = [], []
        for _, row in g.iterrows():
            track_hist[row["race_key"]] = float(np.mean(vals)) if len(vals) >= 3 else np.nan
            vals.append(row["rse"])

    return same_day, track_hist


def run():
    print("Loading form history...")
    fh = rse._load_and_prep_form()
    fh = fh.dropna(subset=["track", "raceNumber", "raceShapeEarly"])

    # BUG FOUND (this run): the raw archive goes back to 2017 (2,839
    # distinct calendar days). race_speed_estimate.py's own train()
    # inherited pattern - pmeans_cache{} keyed by day, each entry a fresh
    # set of ~13 dicts keyed by every horse_lc seen up to that day - grows
    # unbounded over that many distinct days and OOM-killed this script
    # twice (once at 6.75GB fighting for CPU with a concurrent job, once
    # alone at 13.95GB - so this is a real inefficiency in the inherited
    # design, not a contention artifact). Same latent risk likely exists
    # in race_speed_estimate.py's own train() if ever re-run on today's
    # full (now much longer than when it was last fit) archive - worth a
    # separate look, not fixed here. Pragmatic bound for THIS test, same
    # convention as wpr_own_pace_backtest.py's own --since default: keep
    # 2 years of history (still >>> the 70/30 split needs, nowhere near
    # 2017-2026's full 2,839 days) so pmeans_cache stays a few hundred
    # entries, not thousands.
    since = fh["date"].max() - pd.Timedelta(days=730)
    n_before = len(fh)
    fh = fh[fh["date"] >= since].copy()
    print(f"  bounded to last 2 years ({since.date()} onward): "
          f"{n_before:,} -> {len(fh):,} rows, "
          f"{fh['date'].dt.normalize().nunique():,} distinct days")

    fh["race_key"] = (fh["track"].astype(str) + "|" + fh["date"].astype(str)
                      + "|" + fh["raceNumber"].astype(str))
    print(f"  {len(fh):,} rows")

    race_meta = (fh.groupby("race_key")
                   .agg(date=("date", "first"), rse=("raceShapeEarly", "first"),
                        n=("horse_lc", "count"))
                   .reset_index())
    race_meta = race_meta[race_meta["n"] >= 4]
    print(f"  {len(race_meta):,} races with 4+ runners and a known raceShapeEarly")

    print("Building same_day_pace_so_far / track_hist_tempo lookups...")
    same_day, track_hist = build_same_day_and_track_hist(fh)
    print(f"  same_day coverage (>=1 prior race that day): "
          f"{sum(1 for v in same_day.values() if not pd.isna(v)):,} / {len(same_day):,}")
    print(f"  track_hist coverage (>=3 prior races at that track): "
          f"{sum(1 for v in track_hist.values() if not pd.isna(v)):,} / {len(track_hist):,}")

    cut = race_meta["date"].quantile(0.70)
    train_races = race_meta[race_meta["date"] < cut]
    test_races = race_meta[race_meta["date"] >= cut]
    print(f"  split at {cut.date()}: {len(train_races):,} train, {len(test_races):,} test")

    fh_by_race = fh.groupby("race_key")
    pmeans_cache = {}

    def prior_means_cached(cutoff_date):
        if cutoff_date not in pmeans_cache:
            pmeans_cache[cutoff_date] = rse._prior_means(fh, cutoff_date)
        return pmeans_cache[cutoff_date]

    def build_rows(race_df):
        rows, ys = [], []
        for day, day_races in race_df.groupby(race_df["date"].dt.normalize()):
            pmeans = prior_means_cached(day)
            for _, rr in day_races.iterrows():
                runners = fh_by_race.get_group(rr["race_key"])
                feat = rse._race_features(runners, pmeans)
                feat["same_day_pace_so_far"] = same_day.get(rr["race_key"], np.nan)
                feat["track_hist_tempo"] = track_hist.get(rr["race_key"], np.nan)
                rows.append(feat)
                ys.append(rr["rse"])
        return pd.DataFrame(rows), np.array(ys, dtype=float)

    print("Building training rows...")
    Xtr, ytr = build_rows(train_races)
    print("Building held-out rows...")
    Xte, yte = build_rows(test_races)

    # Baseline feature list = whatever _race_features() itself emits (more
    # robust than reading it back off a possibly-stale config.json, and
    # this script never calls _load_model() so rse._CFG is never populated).
    baseline_features = [c for c in Xtr.columns if c not in ("same_day_pace_so_far", "track_hist_tempo")]

    def fit_and_score(feature_list, label):
        med = Xtr[feature_list].median()
        Xtr_f = Xtr[feature_list].fillna(med)
        Xte_f = Xte[feature_list].fillna(med)
        model = lgb.LGBMRegressor(n_estimators=200, max_depth=3, learning_rate=0.05,
                                  num_leaves=8, random_state=42, verbosity=-1)
        model.fit(Xtr_f, ytr)
        pred = model.predict(Xte_f)
        corr = float(np.corrcoef(pred, yte)[0, 1])
        print(f"  {label}: held-out correlation = {corr:+.4f}  ({len(feature_list)} features)")
        return corr

    print("\n=== Held-out correlation comparison ===")
    c_base = fit_and_score(baseline_features, "BASELINE (24 features, current model)")
    c_sameday = fit_and_score(baseline_features + ["same_day_pace_so_far"], "+ same_day_pace_so_far")
    c_trackhist = fit_and_score(baseline_features + ["track_hist_tempo"], "+ track_hist_tempo")
    c_both = fit_and_score(baseline_features + ["same_day_pace_so_far", "track_hist_tempo"], "+ both")

    print(f"\nBaseline: {c_base:+.4f}")
    print(f"Best candidate: {max(c_sameday, c_trackhist, c_both):+.4f}")
    print("Done.")


if __name__ == "__main__":
    run()
