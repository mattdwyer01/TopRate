"""
wpr_race_speed_retrain_full_field.py
--------------------------------------
Tests whether race_speed_estimate.py's model itself (not just its
output thresholds - see wpr_race_speed_actual_calibration.py, a
negative result) can be improved by training on COMPLETE race fields
instead of the sparse ones train() has always used.

THE HYPOTHESIS
  train()'s features (mean_rel, n_leaders, std_rel, etc.) are field-
  level aggregates - but the runners fed into _race_features() during
  training come from wpr_form_history.csv.gz's own race_key grouping,
  which only contains a horse if that horse was independently scraped
  elsewhere (backfill_race_results.py's own docstring measured this
  directly: median 2-3 captured runners per race, out of real fields of
  ~10-12). A "how many leaders are in this field" feature computed over
  2-3 of 12 runners is a noisy, unrepresentative sample of the real
  field. race_results_*.csv.gz (backfill_race_results.py's bulk
  meetings/{id}/history fetch) has every runner in every finalized
  meeting - if data completeness is what is capping the model's
  held-out correlation (+0.26, see race_speed_estimate.py's own module
  docstring), training on complete fields should measurably raise it.

CONTROLLED COMPARISON (same races, same target, only field completeness
differs)
  For a common population of races (from race_results_*.csv.gz, so the
  target raceShapeEarly and race population are identical either way):
    OLD (sparse)  - each of race_results_*.csv.gz's real runners is kept
                    only if that (horse, date) pair also appears
                    somewhere in wpr_form_history.csv.gz (i.e. that
                    runner was independently captured elsewhere) - empty
                    if none of the field was ever captured, a realistic
                    worst case. NOT matched via a reconstructed
                    track|date|raceNumber race key: raceNumber turned
                    out to be essentially always null in race_results_
                    *.csv.gz (confirmed directly), so (horse, date) -
                    the same granularity _prior_means() already uses -
                    is the reliable join instead.
    NEW (full)    - runners come from race_results_*.csv.gz's own
                    complete field for that race.
  Per-horse PRIOR-history lookups (_prior_means) are IDENTICAL in both
  conditions - always built from wpr_form_history.csv.gz, since that is
  the only source with positionSettled/sectionals at all (race_results_
  *.csv.gz has positionSettled 100% absent - a real gap, see wpr_settle_
  shape_prediction_check.py's own docstring). Only which runners get
  averaged over for feature-building differs.

  Two LightGBM models (identical hyperparameters to train()'s own) are
  fit on the SAME chronological 70/30 split, one per condition, then
  evaluated on the untouched holdout - a clean answer to "does field
  completeness alone move the needle."

SCOPE
  Restricted to races since --since (default 2024-01-01) for
  tractability - full multi-year history would take much longer to
  build features for (two conditions per race) than the live-scoring
  pass this session's other tools already timed. Use --limit for a
  quick smoke test before a full run.

SAFETY
  Read-only / dry-run always - this is a research comparison, it never
  writes race_speed_model.joblib or race_speed_config.json. If the
  result is a genuine win, that is a SEPARATE, deliberate follow-up
  (retrain + ship), not something this script does automatically.

NO EM DASHES policy: hyphens only in this file.
"""
import argparse
import time
from pathlib import Path

import numpy as np
import pandas as pd

import race_speed_estimate as rse

HERE = Path(__file__).parent


def load_race_results(since):
    since_ts = pd.Timestamp(since)
    years = range(since_ts.year, pd.Timestamp.today().year + 1)
    frames = []
    for y in years:
        p = HERE / f"race_results_{y}.csv.gz"
        if not p.exists():
            continue
        frames.append(pd.read_csv(
            p, low_memory=False, dtype={"race_id": str},
            usecols=["race_id", "track", "date", "raceNumber", "barrier",
                     "distance", "horse", "raceShapeEarly"],
        ))
    df = pd.concat(frames, ignore_index=True)
    df["date"] = pd.to_datetime(df["date"], errors="coerce")
    df["barrier"] = pd.to_numeric(df["barrier"], errors="coerce")
    df["distance"] = pd.to_numeric(df["distance"], errors="coerce")
    df["raceShapeEarly"] = pd.to_numeric(df["raceShapeEarly"], errors="coerce")
    df = df[df["date"] >= since_ts]
    return df.dropna(subset=["race_id", "date", "raceShapeEarly"])


def build_race_meta(rr):
    meta = (rr.groupby("race_id")
              .agg(date=("date", "first"), rse=("raceShapeEarly", "first"),
                   n=("horse", "count"), distance=("distance", "first"))
              .reset_index())
    return meta[meta["n"] >= 4]


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--since", default="2024-01-01",
                    help="only races on/after this date (YYYY-MM-DD), default 2024-01-01")
    ap.add_argument("--limit", type=int, default=None,
                    help="cap the race population for a quick smoke test")
    args = ap.parse_args()

    print(f"Loading race_results_*.csv.gz since {args.since}...")
    rr = load_race_results(args.since)
    print(f"  {len(rr):,} runner-race rows")

    meta = build_race_meta(rr)
    print(f"  {len(meta):,} races with 4+ runners and a known raceShapeEarly")
    meta = meta.sort_values("date").reset_index(drop=True)
    if args.limit:
        meta = meta.iloc[:args.limit]
        print(f"  --limit applied: using first {len(meta):,} races (smoke test)")

    print("\nLoading wpr_form_history.csv.gz (for prior-means AND the OLD sparse-field condition)...")
    fh = rse._load_form()
    # NOT a track|date|raceNumber key match (the original plan) -
    # raceNumber turned out to be essentially always null in
    # race_results_*.csv.gz (confirmed directly: 0/5 sampled rows had a
    # value - this bulk endpoint uses a different field for it, per
    # backfill_race_results.py's own header comment, which lists
    # raceNumber as NOT among the fields confirmed present). Matching on
    # (horse_lc, date) instead sidesteps that gap entirely, is exactly
    # the same granularity _prior_means()/_load_form() already use
    # elsewhere in this codebase, and answers the real question directly:
    # "was THIS runner's run on THIS date captured anywhere in
    # wpr_form_history.csv.gz at all" - which is precisely what
    # constitutes the OLD condition's sparse coverage.
    fh_horse_dates = set(zip(fh["horse_lc"], fh["date"]))

    rr = rr.copy()
    rr["horse_lc"] = rr["horse"].astype(str).str.strip().str.lower()
    rr_by_race_id = rr.groupby("race_id")

    n_races = len(meta)
    print(f"\nBuilding features for {n_races:,} races (both OLD-sparse and NEW-full-field conditions)...")
    t0 = time.time()
    pmeans_by_date = {}
    old_rows, new_rows, ys, dates = [], [], [], []
    n_old_empty = 0
    for gi, row in meta.iterrows():
        if gi > 0 and gi % 2000 == 0:
            elapsed = time.time() - t0
            eta = elapsed / gi * (n_races - gi)
            print(f"  ... {gi:,}/{n_races:,} ({elapsed:.0f}s elapsed, ~{eta:.0f}s remaining)")
        day = row["date"].normalize()
        if day not in pmeans_by_date:
            pmeans_by_date[day] = rse._prior_means(fh, day)
        pmeans = pmeans_by_date[day]

        full_field = rr_by_race_id.get_group(row["race_id"])
        new_rows.append(rse._race_features(full_field[["horse", "barrier", "distance"]], pmeans))

        race_date = row["date"]
        captured_mask = full_field["horse_lc"].apply(lambda hl: (hl, race_date) in fh_horse_dates)
        old_field = full_field.loc[captured_mask, ["horse", "barrier", "distance"]]
        if len(old_field):
            old_feat = rse._race_features(old_field, pmeans)
        else:
            # _race_features indexes race_runners["distance"].iloc[0] to
            # get today's race distance, so it needs at least one row -
            # but a genuinely empty field shouldn't count as 1 runner.
            # Use a single phantom row (horse=None, so per-horse lookups
            # correctly come back NaN) just so the distance read
            # succeeds, then overwrite field_size with the REAL count -
            # distance and field_size are known from the race card
            # itself regardless of scrape coverage, unlike every other
            # feature here which genuinely depends on it.
            phantom = pd.DataFrame([{"horse": None, "barrier": np.nan, "distance": row["distance"]}])
            old_feat = rse._race_features(phantom, pmeans)
            old_feat["field_size"] = float(row["n"])
            n_old_empty += 1
        old_rows.append(old_feat)

        ys.append(row["rse"])
        dates.append(row["date"])
    print(f"Done in {time.time()-t0:.0f}s. {n_old_empty:,}/{n_races:,} races had ZERO sparse-field "
          f"coverage in wpr_form_history.csv.gz (a realistic worst case for the OLD condition).")

    Xnew = pd.DataFrame(new_rows)
    Xold = pd.DataFrame(old_rows)
    y = np.array(ys, dtype=float)
    dates = pd.Series(dates)

    cut = int(n_races * 0.70)
    order = dates.sort_values().index  # already chronological (meta was sorted), but be explicit
    train_idx, test_idx = order[:cut], order[cut:]
    print(f"\nFit: {len(train_idx):,} races ({dates.iloc[train_idx].min().date()} to {dates.iloc[train_idx].max().date()})")
    print(f"Holdout: {len(test_idx):,} races ({dates.iloc[test_idx].min().date()} to {dates.iloc[test_idx].max().date()})")

    import lightgbm as lgb
    from sklearn.metrics import mean_absolute_error

    def fit_and_eval(X, name):
        med = X.iloc[train_idx].median()
        Xtr = X.iloc[train_idx].fillna(med)
        Xte = X.iloc[test_idx].fillna(med)
        model = lgb.LGBMRegressor(n_estimators=200, max_depth=3, learning_rate=0.05,
                                  num_leaves=8, random_state=42, verbosity=-1)
        model.fit(Xtr, y[train_idx])
        pred = model.predict(Xte)
        corr = float(np.corrcoef(pred, y[test_idx])[0, 1])
        mae = float(mean_absolute_error(y[test_idx], pred))
        print(f"\n--- {name} ---")
        print(f"held-out correlation: {corr:+.4f}  (R^2 ~ {corr**2*100:.1f}%)")
        print(f"held-out MAE: {mae:.3f}")
        return corr, mae, model

    print("\n" + "=" * 72)
    print("TRAINING BOTH CONDITIONS ON THE SAME RACES / SAME TARGET / SAME SPLIT")
    print("=" * 72)
    old_corr, old_mae, _ = fit_and_eval(Xold, "OLD (sparse field, wpr_form_history.csv.gz - today's actual approach)")
    new_corr, new_mae, _ = fit_and_eval(Xnew, "NEW (complete field, race_results_*.csv.gz)")

    print("\n" + "=" * 72)
    print(f"RESULT: OLD corr={old_corr:+.4f}  NEW corr={new_corr:+.4f}  "
          f"delta={new_corr-old_corr:+.4f}")
    print(f"        (currently shipped model's documented held-out corr: +0.27, "
          f"different population/split - not directly comparable to either number "
          f"above, only OLD-vs-NEW here is apples-to-apples)")
    print("=" * 72)
    if new_corr > old_corr + 0.02:
        print("\nComplete fields measurably help. Worth a real retrain + proper "
              "chronological validation before shipping (this script never writes "
              "race_speed_model.joblib/race_speed_config.json itself).")
    else:
        print("\nComplete fields do NOT measurably help on this sample - field "
              "sparsity was not the binding constraint. See chat for next steps.")


if __name__ == "__main__":
    main()
