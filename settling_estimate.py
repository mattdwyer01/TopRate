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
      run_style_tendency  +  barrier_nudge  +  sect_early_nudge

  - run_style_tendency: the horse's historical relative settle, the mean
    of (positionSettled / field_size) over its past runs. 0 = habitual
    leader, 1 = habitual backmarker. Same definition wpr_projection.py
    already uses for its run_style feature.
  - barrier_nudge: today's barrier relative to the field. A wide draw
    makes holding a forward position harder (nudge toward the back); an
    inside draw makes it easier (nudge toward the front). Small effect -
    barrier influences but does not dictate where a horse settles.
  - sect_early_nudge (added Sep 2026, see wpr_settle_sectional_test.py):
    this horse's own trailing early-speed RATING (sect_i_early), ranked
    against the OTHER runners in today's actual field. Genuinely
    different information from run_style_tendency, which is ordinal
    (settled 3rd of 8 either way, whether by a nose or ten lengths) -
    validated bidirectionally as a real, if modest, accuracy gain. Needs
    the WHOLE field's trailing ratings to rank against - see
    estimate_race_settling(), not estimate_settle() alone, to get this
    filled in (estimate_settle() alone leaves it at 0 unless a caller
    supplies sect_rank_in_race itself).

  Kept transparent on purpose: this estimate feeds the WPR adjustment
  layer (Stage 3), which must be auditable and overridable. A black-box
  settle model would defeat that.

USAGE
  python settling_estimate.py --race <race_id>      # estimate one race
  python settling_estimate.py --validate            # descriptive check
  python settling_estimate.py --validate --n 300    # sample 300 races

VALIDATION
  --validate compares the estimate to ACTUAL settled positions on past
  resulted runs, working race-by-race (sect_rank_in_race needs a whole
  field to rank against): for each runner, predicted relative settle vs
  actual positionSettled / field_size. Reports mean absolute error and
  band-hit rate. This is descriptive - it does NOT touch ROI or betting.

NO EM DASHES policy: hyphens only in this file.
"""

import argparse
import sys
from pathlib import Path

import pandas as pd

FORM_CSV = Path(__file__).parent / "wpr_form_history.csv.gz"
RUNNERS_CSV = Path(__file__).parent / "toprate_runners.csv"

# barrier_nudge: how much today's draw shifts the settling estimate.
# A horse drawn widest gets nudged BARRIER_MAX_NUDGE toward the back;
# drawn 1 gets nudged the same amount toward the front; the middle of
# the field gets ~0. Small by design - the draw influences settling but
# the horse's own run-style dominates.
#
# NOT changed to the properly-fit value (~0.081, see
# wpr_settle_barrier_nudge_calibration_test.py) - that fit was only
# validated jointly WITH the sect_early_nudge below, and this constant is
# also read directly by wpr_projection.py's own build_features()
# (`from settling_estimate import barrier_nudge`) for cur_settle_band,
# which is out of scope here (see estimate_race_settling's own docstring
# for why). Changing it alone would be an unvalidated, silent change to
# that separate, live rating pipeline.
BARRIER_MAX_NUDGE = 0.12

# sect_early_nudge: a SEPARATE, ADDITIONAL nudge from this horse's own
# trailing early-speed RATING (sect_i_early, "individualEarlySpeed" per
# toprate_json_capture.py's field mapping) relative to the OTHER runners
# in today's field - genuinely different information from run_style_
# tendency (which is ordinal: settled 3rd of 8 either way, whether by a
# nose or ten lengths) or barrier_nudge (today's draw only). Validated
# (Sep 2026, wpr_settle_sectional_test.py) bidirectionally: jointly
# refitting the draw-nudge slope (0.0806, matching BARRIER_MAX_NUDGE's
# effect almost exactly) alongside this sect coefficient improved held-out
# settling MAE in BOTH directions of a swapped chronological split
# (0.2092 -> 0.2085 and 0.2176 -> 0.2172) - final coefficients refit on
# all available data.
SECT_NUDGE_DRAW_SLOPE = 0.0806    # draw-nudge slope, fit JOINTLY with the term below
SECT_NUDGE_COEF = -0.0162         # negative: a stronger relative early-speed rating pulls forward
SECT_EARLY_LO, SECT_EARLY_HI = -24.54, 6.80   # winsorization bounds (1st/99th pctile, fit-time population)
_MIN_RUNS_FOR_SECT = 1

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


def trailing_sect_early(prior_runs):
    """Mean early-speed RATING (sect_i_early) over a horse's past runs,
    winsorized at the fitted population bounds (SECT_EARLY_LO/HI) so a
    rare extreme outlier does not dominate a horse with few runs. Returns
    (mean, n_usable); mean is None if no usable runs. Mirrors
    run_style_tendency's own shape."""
    if prior_runs is None or len(prior_runs) == 0:
        return None, 0
    raw = pd.to_numeric(prior_runs.get("sect_i_early"), errors="coerce")
    clipped = raw.clip(SECT_EARLY_LO, SECT_EARLY_HI).dropna()
    if len(clipped) == 0:
        return None, 0
    return float(clipped.mean()), int(len(clipped))


def sect_early_nudge(sect_rank_in_race):
    """Shift from this horse's trailing early-speed rating RANKED against
    the other runners in today's actual field (0 = weakest rating in the
    field, 1 = strongest). None (unknown rank - e.g. this horse has no
    sect_i_early history) returns 0.0, same "unseen -> 0" contract as
    barrier_nudge."""
    if sect_rank_in_race is None or sect_rank_in_race != sect_rank_in_race:  # NaN
        return 0.0
    r = min(1.0, max(0.0, float(sect_rank_in_race)))
    # centre on 0; HIGH rank (strong relative early speed) pulls TOWARD
    # the front - since 0=lead in this scale, that is a NEGATIVE nudge.
    return (r - 0.5) * 2 * SECT_NUDGE_COEF


def estimate_settle(prior_runs, barrier, field_size, sect_rank_in_race=None):
    """Estimate one horse's settling position today.

    sect_rank_in_race: this horse's trailing_sect_early ranked against the
    REST of today's field (0-1, see sect_early_nudge) - optional, since it
    needs the whole field's trailing values to compute (unlike barrier_
    nudge, which only needs this one horse's own barrier/field_size).
    None (the default) leaves that term at 0.0 - existing callers are
    unaffected. Use estimate_race_settling() to get this filled in for
    every runner in a race at once.

    Returns dict: rel (0-1 or None), band, tendency, n_runs, nudge,
    confidence ('ok' / 'low' / 'none')."""
    tendency, n = run_style_tendency(prior_runs)
    nudge = barrier_nudge(barrier, field_size) + sect_early_nudge(sect_rank_in_race)
    if tendency is None:
        # no settle history - cannot estimate from run-style. Fall back
        # to a neutral midfield estimate, flagged as no-confidence.
        return {"rel": None, "band": "Unknown", "tendency": None,
                "n_runs": n, "nudge": nudge, "confidence": "none"}
    rel = min(1.0, max(0.0, tendency + nudge))
    conf = "ok" if n >= _MIN_RUNS_FOR_STYLE else "low"
    return {"rel": rel, "band": _band(rel), "tendency": tendency,
            "n_runs": n, "nudge": nudge, "confidence": conf}


def estimate_race_settling(field):
    """Estimate settling for every runner in a race AT ONCE - needed for
    sect_rank_in_race, which requires comparing this horse's trailing
    early-speed rating against the REST of today's actual field (a single-
    horse function like estimate_settle cannot compute this alone).

    field: list of (label, prior_runs, barrier, field_size) tuples - label
    is caller-defined (horse name, run_id, whatever the caller wants back
    to identify the row).

    Uses the JOINTLY-fit draw-nudge slope (SECT_NUDGE_DRAW_SLOPE), not the
    standalone BARRIER_MAX_NUDGE - see SECT_NUDGE_DRAW_SLOPE's own comment
    for why those two coefficients must travel together.

    Returns {label: estimate_settle(...) dict}."""
    trailing = {label: trailing_sect_early(prior_runs) for label, prior_runs, _, _ in field}
    vals = pd.Series({label: t for label, (t, n) in trailing.items() if t is not None})
    ranks = vals.rank(pct=True) if len(vals) else pd.Series(dtype=float)

    out = {}
    for label, prior_runs, barrier, field_size in field:
        tendency, n = run_style_tendency(prior_runs)
        draw_nudge = 0.0
        if barrier is not None and field_size is not None and field_size >= 2:
            try:
                b, fs = float(barrier), float(field_size)
                draw_frac = min(1.0, max(0.0, (b - 1) / (fs - 1)))
                draw_nudge = (draw_frac - 0.5) * 2 * SECT_NUDGE_DRAW_SLOPE
            except (TypeError, ValueError):
                pass
        sect_rank = ranks.get(label)
        nudge = draw_nudge + sect_early_nudge(sect_rank)
        if tendency is None:
            out[label] = {"rel": None, "band": "Unknown", "tendency": None,
                          "n_runs": n, "nudge": nudge, "confidence": "none"}
            continue
        rel = min(1.0, max(0.0, tendency + nudge))
        conf = "ok" if n >= _MIN_RUNS_FOR_STYLE else "low"
        out[label] = {"rel": rel, "band": _band(rel), "tendency": tendency,
                      "n_runs": n, "nudge": nudge, "confidence": conf}
    return out


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
    # MANDATORY dedup (this session's own established finding, re-verified
    # the hard way in wpr_settle_barrier_nudge_calibration_test.py): 42% of
    # (horse, date) row-pairs are duplicated from a WPR rebaseline
    # re-scrape issue. Without this, run_style_tendency silently double-
    # (or triple-, etc.) counts whichever historical runs happened to be
    # re-scraped more often - quantified impact on this exact function's
    # own output: mean |difference| 0.013 across 18,185 horses, 25% of
    # horses shifted by >0.02, 5.5% by >0.05 (enough to flip a displayed
    # band) - this fed the LIVE speed map (toprate_daily.py's settling-
    # band lookup uses the same undeduped pattern this fixes here) before
    # being caught and fixed (Sep 2026).
    if "scrape_date" in fh.columns:
        fh = fh.sort_values("scrape_date").drop_duplicates(
            subset=["horse_lc", "date", "track"], keep="last")
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
    field = []
    for _, r in race.iterrows():
        horse_lc = str(r.get("horse", "")).strip().lower()
        hist = fh[(fh["horse_lc"] == horse_lc) & (fh["date"] < race_date)]
        field.append((r.get("horse"), hist, r.get("barrier"), field_size))
    ests = estimate_race_settling(field)
    rows = [(label, barrier, ests[label]) for label, _, barrier, _ in field]
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
    resulted runs. Works RACE-BY-RACE (not row-by-row, unlike the pre-
    Sep-2026 version) - sect_rank_in_race needs the WHOLE field's trailing
    early-speed ratings to rank against, which a single-row loop cannot
    provide. n_runs is now the number of most-recent RACES sampled (each
    contributing multiple runner-rows), not individual rows."""
    fh = _load_form()
    if "race_id" not in fh.columns:
        print("No race_id column - cannot group into races for validation.")
        return
    usable = fh[
        pd.to_numeric(fh.get("positionSettled"), errors="coerce").notna()
        & pd.to_numeric(fh.get("field_size"), errors="coerce").notna()
        & fh["race_id"].notna()
    ].copy()
    usable["positionSettled"] = pd.to_numeric(usable["positionSettled"], errors="coerce")
    usable["field_size"] = pd.to_numeric(usable["field_size"], errors="coerce")
    usable = usable[(usable["positionSettled"] > 0) & (usable["field_size"] >= 2)]

    race_dates = usable.groupby("race_id")["date"].first().sort_values(ascending=False)
    test_race_ids = race_dates.head(n_runs).index

    print("=" * 70)
    print(f"SETTLING ESTIMATE - VALIDATION on {len(test_race_ids)} past races")
    print("descriptive only: predicted relative settle vs actual")
    print("=" * 70)

    abs_errs = []
    band_hits = 0
    band_total = 0
    skipped = 0
    for race_id, race_rows in usable[usable["race_id"].isin(test_race_ids)].groupby("race_id"):
        race_date = race_rows["date"].iloc[0]
        field_size = race_rows["field_size"].iloc[0]
        field = []
        for _, run in race_rows.iterrows():
            prior = fh[(fh["horse_lc"] == run["horse_lc"]) & (fh["date"] < race_date)]
            field.append((run.name, prior, run.get("barrier"), field_size))
        ests = estimate_race_settling(field)
        for label, _, _, _ in field:
            run = race_rows.loc[label]
            est = ests[label]
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
    ap.add_argument("--n", type=int, default=200,
                    help="number of most-recent RACES to sample (default 200; "
                         "each race contributes multiple runner-rows)")
    args = ap.parse_args()

    if args.validate:
        validate(args.n)
    elif args.race:
        estimate_race(args.race)
    else:
        ap.print_help()


if __name__ == "__main__":
    main()
