"""
wpr_race_speed_actual_calibration.py
-------------------------------------
Refits race_speed_estimate.py's Hot/Fast/Even/Slow thresholds against
REAL, independent actual raceShapeEarly outcomes (race_results_*.csv.gz,
backfill_race_results.py's bulk meetings/{id}/history fetch) - something
no prior calibration pass on this model has ever done.

WHY THE EXISTING CALIBRATION (wpr_race_speed_true_calibration.py) ISN'T
ENOUGH
  That script (and train()'s own y_quantiles fit inside race_speed_
  estimate.py) both pick thresholds as QUANTILES OF THE MODEL'S OWN
  PREDICTIONS, then check that the resulting label split looks similar
  between a fit set and a held-out set. That only proves the thresholds
  are internally self-consistent (stable across a re-split of the same
  population) - it never checks whether a race labelled "Hot" by that
  scheme actually ran hot. Confirmed via wpr_settle_shape_prediction_
  check.py against real toprate.au data (Sep 2026, see chat): the live
  rs_label was predicting Fast/Hot on 69% of races when only 46% of
  races actually ran fast, and almost never predicting Slow (9.6% of
  races) despite Slow being the single most common REAL outcome (51%).
  Both existing calibration bugs (a sign inversion, then a population-
  mismatch bug - see race_speed_estimate.py's _tempo_label docstring and
  this file's own predecessor's docstring) were found and "fixed"
  without ever being checked against real outcomes, because race_
  results_*.csv.gz (a comprehensive, independent per-race actual-shape
  source) did not exist as a validation tool until this session.

METHOD
  1. Score every resulted race in toprate_runners.csv through the exact
     LIVE estimate_race_speed() call path (same as wpr_race_speed_true_
     calibration.py's score_all(), reused unchanged here) - this is
     "predicted_rse", the model's continuous pre-bucket output.
  2. Join against race_results_*.csv.gz's real raceShapeEarly per
     race_id (one actual value per race), bucketed into Fast/Even/Slow
     with the SAME +-0.15 threshold lib/pace.ts's estimatePace() and
     wpr_settle_shape_prediction_check.py both already use, so this
     calibration targets the exact real-world label distribution the
     live dashboard is judged against, not an arbitrary target split.
  3. Chronological 70/30 fit/holdout split (matches this project's own
     convention elsewhere, e.g. race_speed_estimate.train()'s own 0.70
     cut and wpr_race_speed_true_calibration.py's FIT_FRACTION).
  4. On the FIT set only, grid-search two cut points on predicted_rse
     to maximise BALANCED accuracy (mean per-class recall across
     Slow/Even/Fast) against the REAL actual bucket - balanced, not raw
     accuracy, because Even is rare (~2-3% of races) and raw accuracy
     would be dominated by the Fast/Slow split alone.
  5. A third "hot" cutoff subdivides the Fast side for the 4-way display
     label only - there is no separate ground-truth "Hot" category to
     calibrate against (lib/pace.ts already folds Hot into Fast for
     matching purposes), so this is a cosmetic split: the median
     predicted_rse among FIT rows whose ACTUAL bucket is Fast.
  6. Evaluate the new thresholds on the untouched HOLDOUT set, and
     report the OLD (currently shipped) thresholds' performance on the
     exact same holdout set for a clean, apples-to-apples before/after.

SAFETY
  Dry-run by default - prints the full before/after report and exits.
  Pass --commit to actually write race_speed_config.json's y_quantiles
  and backfill rs_score/rs_label onto toprate_runners.csv (same two
  writes wpr_race_speed_true_calibration.py's run() already makes, so a
  later real retrain overwrites this the same way it always has).

NO EM DASHES policy: hyphens only in this file.
"""
import argparse
import json
import time
from pathlib import Path

import numpy as np
import pandas as pd

import race_speed_estimate as rse
from toprate_daily import load_runners, save_runners

HERE = Path(__file__).parent
CONFIG_PATH = HERE / "race_speed_config.json"
FIT_FRACTION = 0.70


def score_all(runners_df, fh):
    """Unchanged from wpr_race_speed_true_calibration.py - scores every
    resulted race through the live estimate_race_speed() call path."""
    resulted_mask = pd.to_numeric(runners_df.get("resulted"), errors="coerce") == 1
    runners_df["date"] = pd.to_datetime(runners_df["date"], errors="coerce")
    target = runners_df[resulted_mask & runners_df["date"].notna()]
    race_groups = list(target.groupby("race_id"))
    n_races = len(race_groups)
    print(f"Scoring {n_races:,} real races via the LIVE estimate_race_speed() call path...")

    t0 = time.time()
    pmeans_by_date = {}
    rows = []
    for gi, (race_id, race) in enumerate(race_groups):
        if gi > 0 and gi % 1000 == 0:
            elapsed = time.time() - t0
            eta = elapsed / gi * (n_races - gi)
            print(f"  ... {gi:,}/{n_races:,} ({elapsed:.0f}s elapsed, ~{eta:.0f}s remaining)")
        race_date = race["date"].iloc[0]
        day = race_date.normalize()
        if day not in pmeans_by_date:
            pmeans_by_date[day] = rse._prior_means(fh, day)
        try:
            res = rse.estimate_race_speed(race, race_date, fh, pmeans=pmeans_by_date[day])
        except Exception:
            continue
        rows.append((race_id, race_date, res["predicted_rse"]))
    print(f"Scored {len(rows):,} races in {time.time()-t0:.0f}s.")
    return pd.DataFrame(rows, columns=["race_id", "date", "predicted_rse"])


def load_actual_shape(years):
    frames = []
    for y in years:
        p = HERE / f"race_results_{y}.csv.gz"
        if not p.exists():
            continue
        # race_id as str explicitly - load_runners() (toprate_daily.py)
        # also loads race_id as str, and pandas otherwise infers this
        # file's race_id as int64, which fails the merge in main() with
        # "You are trying to merge on str and int64 columns".
        frames.append(pd.read_csv(p, low_memory=False, dtype={"race_id": str},
                                   usecols=["race_id", "raceShapeEarly"]))
    if not frames:
        return pd.DataFrame(columns=["race_id", "raceShapeEarly"])
    df = pd.concat(frames, ignore_index=True)
    return df.dropna(subset=["race_id", "raceShapeEarly"]).drop_duplicates(subset=["race_id"])


def actual_bucket(raceShapeEarly):
    if raceShapeEarly > 0.15:
        return "Fast"
    if raceShapeEarly < -0.15:
        return "Slow"
    return "Even"


def balanced_accuracy(t_low, t_high, predicted, actual):
    pred_labels = np.where(predicted <= t_low, "Slow",
                    np.where(predicted <= t_high, "Even", "Fast"))
    recalls = []
    for cls in ("Slow", "Even", "Fast"):
        mask = actual == cls
        if mask.sum() == 0:
            continue
        recalls.append((pred_labels[mask] == cls).mean())
    return float(np.mean(recalls)) if recalls else 0.0


def fit_thresholds(predicted, actual):
    """Grid-search t_low < t_high over the FIT set's own predicted_rse
    range to maximise balanced accuracy against the real actual bucket."""
    candidates = np.quantile(predicted, np.linspace(0.02, 0.98, 97))
    candidates = np.unique(candidates)
    best = (-1.0, None, None)
    for i, t_low in enumerate(candidates):
        for t_high in candidates[i + 1:]:
            score = balanced_accuracy(t_low, t_high, predicted, actual)
            if score > best[0]:
                best = (score, t_low, t_high)
    return best  # (balanced_accuracy, t_low, t_high)


def report(name, predicted, actual, t_low, t_high):
    pred_labels = np.where(predicted <= t_low, "Slow",
                    np.where(predicted <= t_high, "Even", "Fast"))
    df = pd.DataFrame({"pred": pred_labels, "actual": actual})
    n = len(df)
    match = (df["pred"] == df["actual"]).mean()
    majority = df["actual"].value_counts(normalize=True).max()
    bal_acc = balanced_accuracy(t_low, t_high, predicted, actual)
    print(f"\n--- {name} (n={n:,}) ---")
    print(f"exact match rate      : {match*100:.1f}%")
    print(f"majority-class baseline: {majority*100:.1f}%")
    print(f"balanced accuracy      : {bal_acc*100:.1f}%  (33.3% = no better than random across 3 classes)")
    print("confusion matrix (rows=predicted, cols=actual):")
    print(pd.crosstab(df["pred"], df["actual"]).reindex(
        index=["Slow", "Even", "Fast"], columns=["Slow", "Even", "Fast"], fill_value=0))


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--commit", action="store_true",
                    help="write the new thresholds to race_speed_config.json and backfill "
                         "rs_score/rs_label onto toprate_runners.csv. Default is dry-run.")
    ap.add_argument("--cache", default=None,
                    help="path to cache/reuse the (expensive, ~7min) live-scoring pass output "
                         "as a pickle - use the same path across reruns while iterating on the "
                         "fit/report logic so only the join+calibration part reruns.")
    args = ap.parse_args()

    print("Loading model + form history...")
    rse._load_model()
    fh = rse._load_form()

    print("Loading runners_df...")
    runners_df = load_runners()

    if args.cache and Path(args.cache).exists():
        print(f"Loading cached scoring pass from {args.cache} (delete it to force a rescore)...")
        scored = pd.read_pickle(args.cache)
    else:
        scored = score_all(runners_df, fh)
        if args.cache:
            scored.to_pickle(args.cache)
            print(f"Cached scoring pass to {args.cache}")
    scored["year"] = pd.to_datetime(scored["date"]).dt.year

    print("\nLoading actual raceShapeEarly from race_results_*.csv.gz...")
    actual = load_actual_shape(sorted(scored["year"].unique()))
    print(f"  {len(actual):,} races with a real actual raceShapeEarly")

    merged = scored.merge(actual, on="race_id", how="inner").sort_values("date").reset_index(drop=True)
    merged["actual_bucket"] = merged["raceShapeEarly"].apply(actual_bucket)
    print(f"\nRaces with BOTH a live-path prediction and a real actual result: {len(merged):,}")
    if len(merged) < 100:
        print("Too few matched races to calibrate reliably - stopping.")
        return
    print(f"date range: {merged['date'].min().date()} to {merged['date'].max().date()}")
    print("real actual bucket distribution (the target this calibration is judged against):")
    print(merged["actual_bucket"].value_counts())
    print((merged["actual_bucket"].value_counts(normalize=True) * 100).round(1))

    cut = int(len(merged) * FIT_FRACTION)
    fit = merged.iloc[:cut]
    holdout = merged.iloc[cut:]
    print(f"\nFit set: {len(fit):,} races ({fit['date'].min().date()} to {fit['date'].max().date()})")
    print(f"Holdout set: {len(holdout):,} races ({holdout['date'].min().date()} to {holdout['date'].max().date()})")

    # ---- Baseline: how do the CURRENTLY SHIPPED thresholds do on this
    # exact holdout set? (re-derive their 3-way call from the old config,
    # Hot folded into Fast, matching lib/pace.ts's own fold rule) ------
    old_cfg = json.load(open(CONFIG_PATH))
    oq = old_cfg["y_quantiles"]
    # Old 4-way scheme: <=hot->Slow, <=fast->Even, <=even->Fast, else->Hot.
    # Folded to 3-way here (Hot joins Fast, matching lib/pace.ts's own
    # fold rule) means the Even/Fast boundary is oq["fast"], NOT
    # oq["even"] (oq["even"] is the old Fast/Hot boundary, irrelevant
    # once Hot and Fast are the same bucket).
    report("BEFORE (currently shipped thresholds) on HOLDOUT",
           holdout["predicted_rse"].to_numpy(), holdout["actual_bucket"].to_numpy(),
           oq["hot"], oq["fast"])

    # ---- Fit new thresholds on FIT only, evaluate on HOLDOUT ----------
    print("\nGrid-searching new thresholds on the FIT set (maximising balanced accuracy)...")
    bal_acc_fit, t_low, t_high = fit_thresholds(
        fit["predicted_rse"].to_numpy(), fit["actual_bucket"].to_numpy())
    print(f"best FIT-set balanced accuracy: {bal_acc_fit*100:.1f}%  (t_low={t_low:.4f}, t_high={t_high:.4f})")

    report("FIT set (in-sample, for reference only)",
           fit["predicted_rse"].to_numpy(), fit["actual_bucket"].to_numpy(), t_low, t_high)
    report("AFTER (new thresholds) on HOLDOUT (the real test)",
           holdout["predicted_rse"].to_numpy(), holdout["actual_bucket"].to_numpy(), t_low, t_high)

    # Hot cutoff: cosmetic 4-way subdivision of the Fast side only (no
    # separate ground truth - see module docstring).
    fast_fit_scores = fit.loc[fit["actual_bucket"] == "Fast", "predicted_rse"]
    hot_cutoff = float(fast_fit_scores.median()) if len(fast_fit_scores) else t_high

    # _score_from_rse's own "hi" reference (q["slow"]) is a SEPARATE
    # concern from the label boundaries above - it only scales the
    # display score to 0-1 and was never a label cutpoint itself (see
    # that function's docstring). Preserve the original design intent
    # (a genuinely high point near the top of the distribution) rather
    # than reusing hot_cutoff, which sits much lower (the median of only
    # the actual-Fast rows) and would compress/skew the displayed score.
    score_hi = float(np.quantile(fit["predicted_rse"], 0.90))

    print("\n" + "=" * 72)
    print(f"New label boundaries: slow/even={t_low:.4f}  even/fast={t_high:.4f}  fast/hot(cosmetic)={hot_cutoff:.4f}")
    print(f"Score-display hi reference (unrelated to label boundaries): {score_hi:.4f}")
    print("=" * 72)

    if not args.commit:
        print("\nDry run (no --commit) - nothing written. Re-run with --commit to apply.")
        return

    cfg = json.load(open(CONFIG_PATH))
    # Key names match _tempo_label's existing ascending check order
    # exactly (hot=Slow/Even boundary, fast=Even/Fast, even=Fast/Hot) -
    # confusing names, but they are race_speed_estimate.py's own
    # pre-existing schema, not something to rename here.
    cfg["y_quantiles"] = {
        "hot": float(t_low), "fast": float(t_high),
        "even": float(hot_cutoff), "slow": float(score_hi),
    }
    with open(CONFIG_PATH, "w") as f:
        json.dump(cfg, f, indent=1)
    print(f"\nWrote updated y_quantiles to {CONFIG_PATH}.")

    print("Backfilling rs_score/rs_label for all resulted races with the new thresholds...")
    # NOT rse._tempo_label()/_score_from_rse() here - those read the
    # module-global _CFG that _load_model() cached in memory BEFORE the
    # new config was written above, so they would silently apply the OLD
    # thresholds. Inline the same logic directly against the values just
    # computed instead, so there is no risk of a stale-cache mismatch
    # between what was written to disk and what gets backfilled.
    def new_label(p):
        if p <= t_low:
            return "Slow"
        if p <= t_high:
            return "Even"
        if p <= hot_cutoff:
            return "Fast"
        return "Hot"

    def new_score(p):
        if score_hi == t_low:
            return 0.5
        return float(min(1.0, max(0.0, (p - t_low) / (score_hi - t_low))))

    scored_map = {rid: p for rid, p in zip(scored["race_id"], scored["predicted_rse"])}
    resulted_mask = pd.to_numeric(runners_df.get("resulted"), errors="coerce") == 1
    for col in ["rs_score", "rs_label"]:
        if col not in runners_df.columns:
            runners_df[col] = None
    for race_id, p in scored_map.items():
        idx = runners_df.index[(runners_df["race_id"] == race_id) & resulted_mask]
        runners_df.loc[idx, "rs_score"] = round(new_score(p), 3)
        runners_df.loc[idx, "rs_label"] = new_label(p)

    save_runners(runners_df)
    print("Saved toprate_runners.csv")


if __name__ == "__main__":
    main()
