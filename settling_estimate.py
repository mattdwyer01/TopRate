"""
settling_estimate.py
--------------------
Stage 1 of the race-speed / settling work (see
SCOPING_race_speed_settling.md).

WHAT IT DOES
  For a race, estimates where each horse will SETTLE in the run -
  expressed as a 0-1 relative settling position (0 = leads, 1 = settles
  last) and a descriptive band (Leader / On-pace / Midfield / Back).

  This is the per-horse settling estimate. Race speed (Stage 2) emerges
  from the field's collective settling estimates, so this script is the
  foundation for both.

THE MODEL (deliberately simple and transparent)
  predicted_relative_settle =
      run_style_tendency  +  barrier_nudge

  - run_style_tendency: the horse's historical relative settle, the mean
    of (positionSettled / field_size) over its past runs. 0 = habitual
    leader, 1 = habitual backmarker. Same definition wpr_projection.py
    already uses for its run_style feature.
  - barrier_nudge: today's barrier relative to the field. A wide draw
    makes holding a forward position harder (nudge toward the back); an
    inside draw makes it easier (nudge toward the front). Small effect -
    barrier influences but does not dictate where a horse settles.

  Kept transparent on purpose: this estimate feeds the WPR adjustment
  layer (Stage 3), which must be auditable and overridable. A black-box
  settle model would defeat that.

USAGE
  python settling_estimate.py --race <race_id>      # estimate one race
  python settling_estimate.py --validate            # descriptive check
  python settling_estimate.py --validate --n 300    # larger validation

VALIDATION
  --validate compares the estimate to ACTUAL settled positions on past
  resulted runs: for each runner, predicted relative settle vs actual
  positionSettled / field_size. Reports mean absolute error and band-
  hit rate. This is descriptive - it does NOT touch ROI or betting.

NO EM DASHES policy: hyphens only in this file.
"""

import argparse
import sys
from pathlib import Path

import pandas as pd

FORM_CSV = Path(__file__).parent / "wpr_form_history.csv"
RUNNERS_CSV = Path(__file__).parent / "toprate_runners.csv"

# barrier_nudge: how much today's draw shifts the settling estimate.
# A horse drawn widest gets nudged BARRIER_MAX_NUDGE toward the back;
# drawn 1 gets nudged the same amount toward the front; the middle of
# the field gets ~0. Small by design - the draw influences settling but
# the horse's own run-style dominates.
BARRIER_MAX_NUDGE = 0.12

_MIN_RUNS_FOR_STYLE = 3   # fewer usable settle runs -> low confidence


def _band(rel):
    """Map a 0-1 relative settle to a descriptive band."""
    if rel is None:
        return "Unknown"
    if rel <= 0.20:
        return "Leader"
    if rel <= 0.45:
        return "On-pace"
    if rel <= 0.70:
        return "Midfield"
    return "Back"


def run_style_tendency(prior_runs):
    """Mean relative settle over a horse's past runs. Returns
    (tendency, n_usable). tendency is None if no usable runs.
    Mirrors wpr_projection.build_features' run_style definition:
    relative settle = positionSettled / field_size, 0-sentinels dropped."""
    if prior_runs is None or len(prior_runs) == 0:
        return None, 0
    settle = pd.to_numeric(prior_runs.get("positionSettled"), errors="coerce")
    fs = pd.to_numeric(prior_runs.get("field_size"), errors="coerce")
    valid = (settle > 0) & (fs > 0)
    rel = (settle[valid] / fs[valid]).clip(0, 1)
    if len(rel) == 0:
        return None, 0
    return float(rel.mean()), int(len(rel))


def barrier_nudge(barrier, field_size):
    """Shift from today's draw. Barrier 1 -> -BARRIER_MAX_NUDGE (toward
    the front), widest -> +BARRIER_MAX_NUDGE (toward the back), middle
    -> ~0. Returns 0.0 if barrier or field size is unknown."""
    if barrier is None or field_size is None or field_size < 2:
        return 0.0
    try:
        b = float(barrier)
        fs = float(field_size)
    except (TypeError, ValueError):
        return 0.0
    # position of the draw within the field, 0 (inside) to 1 (widest)
    draw_frac = (b - 1) / (fs - 1)
    draw_frac = min(1.0, max(0.0, draw_frac))
    # centre on 0: inside draw negative, wide draw positive
    return (draw_frac - 0.5) * 2 * BARRIER_MAX_NUDGE


def estimate_settle(prior_runs, barrier, field_size):
    """Estimate one horse's settling position today.
    Returns dict: rel (0-1 or None), band, tendency, n_runs, nudge,
    confidence ('ok' / 'low' / 'none')."""
    tendency, n = run_style_tendency(prior_runs)
    nudge = barrier_nudge(barrier, field_size)
    if tendency is None:
        # no settle history - cannot estimate from run-style. Fall back
        # to a neutral midfield estimate, flagged as no-confidence.
        return {"rel": None, "band": "Unknown", "tendency": None,
                "n_runs": n, "nudge": nudge, "confidence": "none"}
    rel = min(1.0, max(0.0, tendency + nudge))
    conf = "ok" if n >= _MIN_RUNS_FOR_STYLE else "low"
    return {"rel": rel, "band": _band(rel), "tendency": tendency,
            "n_runs": n, "nudge": nudge, "confidence": conf}


def _load_form():
    if not FORM_CSV.exists():
        sys.exit(f"ERROR: {FORM_CSV.name} not found.")
    fh = pd.read_csv(FORM_CSV, dtype={"horse": str, "horse_id": str},
                     low_memory=False)
    fh["horse_lc"] = fh["horse"].astype(str).str.strip().str.lower()
    fh["date"] = pd.to_datetime(fh["date"], errors="coerce")
    fh = fh.dropna(subset=["date"])
    if "isBarrierTrial" in fh.columns:
        fh = fh[fh["isBarrierTrial"].fillna(0).astype(int) == 0]
    return fh.sort_values(["horse_lc", "date"])


def estimate_race(race_id):
    """Estimate settling for every runner in a race."""
    if not RUNNERS_CSV.exists():
        sys.exit(f"ERROR: {RUNNERS_CSV.name} not found.")
    rdf = pd.read_csv(RUNNERS_CSV, dtype={"run_id": str, "race_id": str},
                      low_memory=False)
    race = rdf[rdf["race_id"].astype(str) == str(race_id)]
    if len(race) == 0:
        sys.exit(f"No race found with race_id {race_id}.")
    race_date = pd.to_datetime(race["date"].iloc[0], errors="coerce")
    field_size = len(race)
    fh = _load_form()

    print("=" * 70)
    print(f"SETTLING ESTIMATE - race {race_id}")
    venue = race["venue"].iloc[0] if "venue" in race.columns else "?"
    print(f"{venue}  field size {field_size}  date {race_date.date()}")
    print("=" * 70)
    rows = []
    for _, r in race.iterrows():
        horse_lc = str(r.get("horse", "")).strip().lower()
        hist = fh[(fh["horse_lc"] == horse_lc) & (fh["date"] < race_date)]
        est = estimate_settle(hist, r.get("barrier"), field_size)
        rows.append((r.get("horse"), r.get("barrier"), est))
    # print sorted by estimated settle - leaders first
    rows.sort(key=lambda x: (x[2]["rel"] if x[2]["rel"] is not None else 99))
    print(f"\n{'Horse':22s} {'Bar':>4s} {'Est':>6s} {'Band':10s} "
          f"{'Tend':>6s} {'Nudge':>7s} {'Runs':>5s} Conf")
    for horse, bar, e in rows:
        rels = f"{e['rel']:.2f}" if e["rel"] is not None else "  -"
        tends = f"{e['tendency']:.2f}" if e["tendency"] is not None else "  -"
        print(f"{str(horse)[:22]:22s} {str(bar):>4s} {rels:>6s} "
              f"{e['band']:10s} {tends:>6s} {e['nudge']:>+7.3f} "
              f"{e['n_runs']:>5d} {e['confidence']}")
    print("=" * 70)


def validate(n_runs):
    """Descriptive check: predicted relative settle vs actual, on past
    resulted runs. For each run with a known positionSettled + field_size,
    estimate it from the horse's PRIOR runs and compare."""
    fh = _load_form()
    # need positionSettled + field_size + barrier present
    usable = fh[
        pd.to_numeric(fh.get("positionSettled"), errors="coerce").notna()
        & pd.to_numeric(fh.get("field_size"), errors="coerce").notna()
    ].copy()
    usable["positionSettled"] = pd.to_numeric(usable["positionSettled"],
                                              errors="coerce")
    usable["field_size"] = pd.to_numeric(usable["field_size"],
                                         errors="coerce")
    usable = usable[(usable["positionSettled"] > 0)
                    & (usable["field_size"] >= 2)]
    # sample the most recent n_runs runs as the test set
    test = usable.sort_values("date", ascending=False).head(n_runs)

    print("=" * 70)
    print(f"SETTLING ESTIMATE - VALIDATION on {len(test)} past runs")
    print("descriptive only: predicted relative settle vs actual")
    print("=" * 70)

    abs_errs = []
    band_hits = 0
    band_total = 0
    skipped = 0
    for _, run in test.iterrows():
        horse_lc = run["horse_lc"]
        run_date = run["date"]
        prior = fh[(fh["horse_lc"] == horse_lc) & (fh["date"] < run_date)]
        est = estimate_settle(prior, run.get("barrier"),
                              run["field_size"])
        if est["rel"] is None:
            skipped += 1
            continue
        actual_rel = min(1.0, run["positionSettled"] / run["field_size"])
        abs_errs.append(abs(est["rel"] - actual_rel))
        band_total += 1
        if est["band"] == _band(actual_rel):
            band_hits += 1

    if not abs_errs:
        print("No runs had enough prior history to estimate. "
              "If this is unexpected, check field_size is populated "
              "(run backfill_sectionals.py --all).")
        return
    mae = sum(abs_errs) / len(abs_errs)
    print(f"\n  runs estimated   : {len(abs_errs)}  "
          f"(skipped {skipped} - no prior settle history)")
    print(f"  relative-settle MAE : {mae:.3f}  "
          f"(0 = perfect, ~0.29 = random guessing)")
    print(f"  band hit rate    : {band_hits}/{band_total} "
          f"= {100*band_hits/band_total:.1f}%  (random ~25%)")
    print("\n  Interpretation: MAE well below 0.29 and band hit rate")
    print("  well above 25% means the estimate carries real signal.")
    print("  This is a descriptive check, not an ROI claim.")
    print("=" * 70)


def main():
    ap = argparse.ArgumentParser(description="Estimate horse settling.")
    ap.add_argument("--race", default=None, help="race_id to estimate")
    ap.add_argument("--validate", action="store_true",
                    help="run the descriptive validation")
    ap.add_argument("--n", type=int, default=500,
                    help="validation sample size (default 500)")
    args = ap.parse_args()

    if args.validate:
        validate(args.n)
    elif args.race:
        estimate_race(args.race)
    else:
        ap.print_help()


if __name__ == "__main__":
    main()
