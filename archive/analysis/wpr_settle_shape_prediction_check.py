"""
wpr_settle_shape_prediction_check.py
-------------------------------------
Compares TopRate's own PRE-race predictions - rs_label/rs_score (race
shape, pace_shape.joblib) and _settling (per-runner predicted settle
band) - as recorded in toprate_runners.csv at prediction time, against
the ACTUAL post-race values toprate.au itself reports for the same
races, via race_results_YYYY.csv.gz (backfill_race_results.py's bulk
meetings/{id}/history fetch).

WHY race_results_*.csv.gz AND NOT wpr_form_history.csv.gz
  wpr_form_history.csv.gz's own actual-shape backfill only fires when a
  horse races AGAIN (see toprate_daily._enrich_form_history_rich, which
  only re-fetches rich per-runner pages for TODAY's runners) - checked
  directly against the real file (Sep 2026, see chat): well under 5% of
  the last 30 days' rows have an actual raceShapeEarly/positionSettled
  at all. race_results_*.csv.gz comes from a different fetch
  (backfill_race_results.py's bulk meetings/{id}/history endpoint) that
  captures EVERY runner in EVERY finalized meeting, not just ones some
  other horse's re-fetch happened to sweep up.

A REAL DATA GAP, NOT A BUG IN THIS SCRIPT
  race_results_*.csv.gz's raceShapeEarly is well populated (confirmed
  Sep 2026: ~69% of rows in a real 30-day window), so the RACE SHAPE
  comparison below is real and actionable. positionSettled is NOT -
  confirmed 100% null across the entire 2026 file (160,598 rows, 0
  non-null) despite being a documented CORE_COLS field. This matches a
  pre-existing code comment in toprate_json_capture.py flagging
  positionSettled as "genuinely absent" from a related endpoint's
  payload during an earlier live inspection. The settle-position
  comparison below therefore reports "no data" rather than a fabricated
  number - closing that gap would need new capture work (finding
  whichever toprate.au field/endpoint, if any, actually carries it),
  which is a bigger job than this script; flag it back to the user
  rather than guessing.

NO EM DASHES policy: hyphens only.
"""
import argparse
from pathlib import Path

import numpy as np
import pandas as pd

HERE = Path(__file__).parent
RUNNERS_CSV = HERE / "toprate_runners.csv"


def _normalize_settle(label):
    """leader / on-pace / midfield / back - toprate_runners.csv's own
    _settling values ("backmarker" for the last bucket) folded onto the
    same 4-way band lib/pace.ts's settleBand() and wpr_projection.py's
    _settle_band() both use, so predicted and actual sides compare on
    identical labels."""
    if pd.isna(label):
        return None
    l = str(label).strip().lower()
    if l in ("back", "backmarker"):
        return "back"
    return l


def _actual_settle_band(rel):
    if pd.isna(rel):
        return None
    if rel <= 0.2:
        return "leader"
    if rel <= 0.45:
        return "on-pace"
    if rel <= 0.7:
        return "midfield"
    return "back"


def _actual_shape_bucket(race_shape_early):
    """Same thresholds as lib/pace.ts's estimatePace()."""
    if pd.isna(race_shape_early):
        return None
    if race_shape_early > 0.15:
        return "Fast"
    if race_shape_early < -0.15:
        return "Slow"
    return "Even"


def _predicted_shape_bucket(rs_label):
    """rs_label is Hot/Fast/Even/Slow - Hot folds into Fast for matching,
    same as lib/pace.ts's estimatePace() already does for the live
    dashboard (a real shape measurement only ever comes back
    Fast/Even/Slow, never "Hot" - that word is pace_shape.joblib's own
    label for an especially strong Fast prediction)."""
    if pd.isna(rs_label):
        return None
    if rs_label == "Slow":
        return "Slow"
    if rs_label == "Even":
        return "Even"
    return "Fast"


def load_actual_results(since, until):
    years = sorted({d.year for d in pd.date_range(since, until, freq="D")})
    frames = []
    for y in years:
        p = HERE / f"race_results_{y}.csv.gz"
        if not p.exists():
            continue
        frames.append(pd.read_csv(
            p, low_memory=False,
            usecols=["race_id", "horse_id", "date", "positionSettled",
                     "raceShapeEarly", "field_size"],
        ))
    if not frames:
        return pd.DataFrame(columns=["race_id", "horse_id", "date",
                                      "positionSettled", "raceShapeEarly",
                                      "field_size"])
    df = pd.concat(frames, ignore_index=True)
    df["date"] = pd.to_datetime(df["date"], errors="coerce")
    return df[(df["date"] >= since) & (df["date"] <= until)]


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--since", required=True, help="YYYY-MM-DD, start of the review window")
    ap.add_argument("--until", default=None, help="YYYY-MM-DD, end of window (default: today)")
    args = ap.parse_args()

    since = pd.Timestamp(args.since)
    until = pd.Timestamp(args.until) if args.until else pd.Timestamp.today().normalize()
    print(f"Reviewing predictions vs actuals: {since.date()} to {until.date()}")

    pred = pd.read_csv(RUNNERS_CSV, low_memory=False)
    pred["date"] = pd.to_datetime(pred["date"], errors="coerce")
    pred = pred[(pred["date"] >= since) & (pred["date"] <= until)]
    pred = pred.dropna(subset=["race_id", "horse_id"])
    print(f"Predicted rows in window (toprate_runners.csv): {len(pred)}")

    actual = load_actual_results(since, until)
    print(f"Actual-result rows available (race_results_*.csv.gz) in window: {len(actual)}")
    if actual.empty:
        print("\nNo actual data available yet for this window - run "
              "backfill_race_results.py --since <date> --commit first "
              "(this script's own GitHub Action does this automatically).")
        return

    # ---- Race shape: one row per race ----------------------------------
    pred_race = (
        pred.dropna(subset=["race_id"])
        .drop_duplicates(subset=["race_id"])[["race_id", "date", "rs_label", "rs_score"]]
    )
    actual_race = (
        actual.dropna(subset=["race_id", "raceShapeEarly"])
        .drop_duplicates(subset=["race_id"])[["race_id", "raceShapeEarly"]]
    )
    shape_merged = pred_race.merge(actual_race, on="race_id", how="inner")
    shape_merged["actual_bucket"] = shape_merged["raceShapeEarly"].apply(_actual_shape_bucket)
    shape_merged["predicted_bucket"] = shape_merged["rs_label"].apply(_predicted_shape_bucket)
    shape_valid = shape_merged.dropna(subset=["actual_bucket", "predicted_bucket"])

    print("\n" + "=" * 72)
    print("RACE SHAPE: predicted (rs_label) vs actual (toprate.au raceShapeEarly)")
    print("=" * 72)
    print(f"races with both a prediction and an actual result: {len(shape_valid)}")
    if len(shape_valid):
        match = (shape_valid["predicted_bucket"] == shape_valid["actual_bucket"]).mean()
        majority = shape_valid["actual_bucket"].value_counts(normalize=True).max()
        corr = shape_merged.dropna(subset=["rs_score", "raceShapeEarly"])[["rs_score", "raceShapeEarly"]].corr().iloc[0, 1]
        print(f"exact 3-way bucket match rate: {match*100:.1f}%")
        print(f"majority-class baseline (always guess the most common actual bucket): {majority*100:.1f}%")
        print(f"correlation(rs_score, raceShapeEarly): {corr:.3f}")
        print("\nconfusion matrix (rows=predicted, cols=actual):")
        print(pd.crosstab(shape_valid["predicted_bucket"], shape_valid["actual_bucket"]))
        print("\nactual bucket distribution:")
        print(shape_valid["actual_bucket"].value_counts())
    else:
        print("No overlapping races - nothing to compare yet.")

    # ---- Settle position: per runner ------------------------------------
    settle_merged = pred.merge(
        actual[["race_id", "horse_id", "positionSettled", "field_size"]],
        on=["race_id", "horse_id"], how="inner",
    ).copy()
    settle_merged["actual_rel"] = np.minimum(
        1.0, settle_merged["positionSettled"] / settle_merged["field_size"]
    )
    settle_merged["actual_band"] = settle_merged["actual_rel"].apply(_actual_settle_band)
    settle_merged["predicted_band"] = settle_merged["_settling"].apply(_normalize_settle)
    settle_valid = settle_merged.dropna(subset=["actual_band", "predicted_band"])

    print("\n" + "=" * 72)
    print("SETTLE POSITION: predicted (_settling) vs actual (toprate.au positionSettled)")
    print("=" * 72)
    print(f"runners with both a prediction and an actual positionSettled: {len(settle_valid)}")
    if len(settle_valid):
        match = (settle_valid["predicted_band"] == settle_valid["actual_band"]).mean()
        print(f"exact 4-way band match rate: {match*100:.1f}%")
        print("\nconfusion matrix (rows=predicted, cols=actual):")
        print(pd.crosstab(settle_valid["predicted_band"], settle_valid["actual_band"]))
    else:
        print("No data - positionSettled is not currently populated in "
              "race_results_*.csv.gz (confirmed Sep 2026: 0/160,598 rows "
              "in the 2026 file). This needs new capture work upstream, "
              "not a fix in this script - see this file's own docstring.")


if __name__ == "__main__":
    main()
