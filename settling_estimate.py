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

THE MODEL (Sep 2026 rebuild: trained, not a hand-tuned formula)
  A small LightGBM regressor on 5 features, predicting actual relative
  settle directly:
    - run_style_tendency: the horse's historical relative settle, the
      mean of (positionSettled / field_size) over its past runs. 0 =
      habitual leader, 1 = habitual backmarker.
    - last5_tendency: the SAME thing over just the horse's last 5 runs -
      recency-weighted, catches a horse maturing tactically or a stable
      changing tactics before a flat all-time average would.
    - draw_signal: today's barrier, centred (-1 = widest, +1 = inside).
    - sect_signal: this horse's trailing early-speed RATING (sect_i_early,
      "individualEarlySpeed"), ranked against the OTHER runners in
      today's actual field and centred - genuinely different information
      from run_style_tendency, which is ordinal (settled 3rd of 8 either
      way, whether by a nose or ten lengths).
    - field_size.

  HISTORY - why this replaced a hand-tuned linear formula: the original
  design (predicted_rel = run_style_tendency + barrier_nudge, later +
  sect_early_nudge - see git history) was "kept transparent on purpose"
  by explicit original design choice, since this estimate feeds the WPR
  adjustment layer, which must be auditable. Testing a trained model on
  the EXACT SAME inputs (wpr_settle_recency_nonlinear_test.py) found the
  linear form was leaving real accuracy on the table - MAE 0.2080 ->
  0.1985 (forward split) and 0.2171 -> 0.2034 (reversed), roughly 10x
  every other improvement found in this whole investigation (barrier-
  nudge recalibration and same-day track-bias tally: no gain;
  sect_early_nudge and the last5/all-time blend: real but an order of
  magnitude smaller). Given that size gap, the user explicitly chose to
  trade the old design's auditability for it (see the actual conversation
  for the tradeoff discussion) - the individual ingredients
  (run_style_tendency, barrier_nudge, trailing_sect_early) are all still
  here as named, inspectable functions for that reason, even though the
  live combination is now a trained model's own weights, not a visible
  sum.

  barrier_nudge()/BARRIER_MAX_NUDGE are UNCHANGED and NOT part of this
  model - they are separately imported by wpr_projection.py's own
  build_features() for cur_settle_band, a different, live rating
  pipeline this rebuild deliberately does not touch (see git history for
  the full scoping rationale - nothing downstream of cur_settle_band is
  currently live in WPR's own rating, so there was no validated benefit
  to justify the risk of changing it).

USAGE
  python settling_estimate.py --race <race_id>      # estimate one race
  python settling_estimate.py --validate            # descriptive check
  python settling_estimate.py --validate --n 300    # sample 300 races
  python settling_estimate.py --retrain             # refit the model

VALIDATION
  --validate compares the estimate to ACTUAL settled positions on past
  resulted runs, working race-by-race (sect_signal needs a whole field
  to rank against): for each runner, predicted relative settle vs actual
  positionSettled / field_size. Reports mean absolute error and band-hit
  rate. This is descriptive - it does NOT touch ROI or betting.

NO EM DASHES policy: hyphens only in this file.
"""

import argparse
import json
import sys
from pathlib import Path

import numpy as np
import pandas as pd

_DIR = Path(__file__).parent
FORM_CSV = _DIR / "wpr_form_history.csv.gz"
RUNNERS_CSV = _DIR / "toprate_runners.csv"
MODEL_PATH = _DIR / "settling_model.joblib"
CONFIG_PATH = _DIR / "settling_config.json"

_MODEL = None
_CFG = None

# Training window: bounded to the last 2 years, not the full archive
# (which goes back to 2017) - matches EXACTLY what
# wpr_settle_recency_nonlinear_test.py actually validated (ship what was
# tested, not a superset of it). This also sidesteps a real memory-
# scaling issue found earlier in this session's research with a
# DIFFERENT per-day-dictionary-cache pattern (race_speed_estimate.py's
# own train()) - not applicable to this file's vectorized groupby
# approach, but the bounded window is kept anyway for fidelity to the
# validated result.
TRAIN_WINDOW_DAYS = 730

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

# sect_i_early ("individualEarlySpeed" per toprate_json_capture.py's
# field mapping) is a continuous early-speed RATING, genuinely different
# information from run_style_tendency (which is ordinal: settled 3rd of 8
# either way, whether by a nose or ten lengths). Winsorization bounds
# below are the fitted population 1st/99th percentile, used by
# trailing_sect_early() - the hand-fit SECT_NUDGE_DRAW_SLOPE/SECT_NUDGE_COEF
# constants that used to combine this with barrier_nudge in a linear
# formula are gone (see module docstring "HISTORY") - the trained model
# now learns that combination itself, on this same underlying feature.
SECT_EARLY_LO, SECT_EARLY_HI = -24.54, 6.80   # winsorization bounds (1st/99th pctile, fit-time population)

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


def last5_tendency(prior_runs):
    """Mean relative settle over just a horse's LAST 5 runs (recency-
    weighted alternative to run_style_tendency's all-time average).
    prior_runs must already be date-sorted ascending (same contract
    run_style_tendency implicitly relies on via its caller). Returns
    (mean, n_usable); mean is None if no usable runs."""
    if prior_runs is None or len(prior_runs) == 0:
        return None, 0
    tail = prior_runs.sort_values("date").tail(5) if "date" in prior_runs.columns else prior_runs.tail(5)
    settle = pd.to_numeric(tail.get("positionSettled"), errors="coerce")
    fs = pd.to_numeric(tail.get("field_size"), errors="coerce")
    valid = (settle > 0) & (fs > 0)
    rel = (settle[valid] / fs[valid]).clip(0, 1)
    if len(rel) == 0:
        return None, 0
    return float(rel.mean()), int(len(rel))


def _load_model():
    """Load the trained settling model and config once."""
    global _MODEL, _CFG
    if _MODEL is not None:
        return
    if not MODEL_PATH.exists() or not CONFIG_PATH.exists():
        raise FileNotFoundError(
            f"settling_model.joblib / settling_config.json not found in {_DIR}. "
            f"Run: python settling_estimate.py --retrain")
    import joblib
    _MODEL = joblib.load(MODEL_PATH)
    _CFG = json.load(open(CONFIG_PATH))


def _predict(feat_rows):
    """feat_rows: list of dicts with keys matching _CFG['features'].
    Missing/None values are median-filled from the fitted config, same
    "unseen -> population median" convention race_speed_estimate.py
    already uses. Returns a list of predicted_rel floats, one per row."""
    _load_model()
    med = _CFG["medians"]
    X = pd.DataFrame([
        {f: (row.get(f) if row.get(f) is not None and row.get(f) == row.get(f)
             else med.get(f, 0.0))
         for f in _CFG["features"]}
        for row in feat_rows
    ], columns=_CFG["features"])
    pred = _MODEL.predict(X)
    return [float(min(1.0, max(0.0, p))) for p in pred]


def estimate_settle(prior_runs, barrier, field_size, sect_rank_in_race=None):
    """Estimate one horse's settling position today, via the trained
    model. sect_rank_in_race is optional (needs the whole field's
    trailing ratings to compute - see estimate_race_settling) and is
    median-filled if not supplied, same as any other missing feature.

    Returns dict: rel (0-1 or None), band, tendency, n_runs, nudge,
    confidence ('ok' / 'low' / 'none'). 'nudge' is now the model's total
    departure from a naive tendency-only baseline (rel - tendency) - kept
    for rough interpretability, no longer a clean linear breakdown (see
    module docstring for why)."""
    tendency, n = run_style_tendency(prior_runs)
    if tendency is None:
        return {"rel": None, "band": "Unknown", "tendency": None,
                "n_runs": n, "nudge": 0.0, "confidence": "none"}
    l5, _ = last5_tendency(prior_runs)
    sect, _ = trailing_sect_early(prior_runs)
    draw_frac = None
    if barrier is not None and field_size is not None and field_size >= 2:
        try:
            draw_frac = min(1.0, max(0.0, (float(barrier) - 1) / (float(field_size) - 1)))
        except (TypeError, ValueError):
            pass
    feat = {
        "run_style_tendency": tendency, "last5_tendency": l5,
        "draw_signal": (draw_frac - 0.5) * 2 if draw_frac is not None else None,
        "sect_signal": (sect_rank_in_race - 0.5) * 2 if sect_rank_in_race is not None else None,
        "field_size": field_size,
    }
    rel = _predict([feat])[0]
    conf = "ok" if n >= _MIN_RUNS_FOR_STYLE else "low"
    return {"rel": rel, "band": _band(rel), "tendency": tendency,
            "n_runs": n, "nudge": rel - tendency, "confidence": conf}


def estimate_race_settling(field):
    """Estimate settling for every runner in a race AT ONCE - needed for
    sect_signal, which requires comparing this horse's trailing early-
    speed rating against the REST of today's actual field (a single-
    horse function like estimate_settle cannot compute this alone).

    field: list of (label, prior_runs, barrier, field_size) tuples - label
    is caller-defined (horse name, run_id, whatever the caller wants back
    to identify the row).

    Returns {label: estimate_settle(...)-shaped dict}."""
    trailing_sect = {label: trailing_sect_early(prior_runs)[0] for label, prior_runs, _, _ in field}
    vals = pd.Series({label: t for label, t in trailing_sect.items() if t is not None})
    ranks = vals.rank(pct=True) if len(vals) else pd.Series(dtype=float)

    labels, feats, tendencies, ns = [], [], [], []
    for label, prior_runs, barrier, field_size in field:
        tendency, n = run_style_tendency(prior_runs)
        l5, _ = last5_tendency(prior_runs)
        draw_frac = None
        if barrier is not None and field_size is not None and field_size >= 2:
            try:
                draw_frac = min(1.0, max(0.0, (float(barrier) - 1) / (float(field_size) - 1)))
            except (TypeError, ValueError):
                pass
        sect_rank = ranks.get(label)
        labels.append(label)
        tendencies.append(tendency)
        ns.append(n)
        feats.append({
            "run_style_tendency": tendency, "last5_tendency": l5,
            "draw_signal": (draw_frac - 0.5) * 2 if draw_frac is not None else None,
            "sect_signal": (sect_rank - 0.5) * 2 if sect_rank is not None and sect_rank == sect_rank else None,
            "field_size": field_size,
        })

    # Rows with no own-history tendency can't be scored meaningfully -
    # still need a placeholder prediction to keep _predict's batch shape
    # simple, but the "none" confidence result below overrides it anyway.
    preds = _predict([{**f, "run_style_tendency": f["run_style_tendency"] or 0.5} for f in feats])

    out = {}
    for label, tendency, n, rel in zip(labels, tendencies, ns, preds):
        if tendency is None:
            out[label] = {"rel": None, "band": "Unknown", "tendency": None,
                          "n_runs": n, "nudge": 0.0, "confidence": "none"}
            continue
        conf = "ok" if n >= _MIN_RUNS_FOR_STYLE else "low"
        out[label] = {"rel": rel, "band": _band(rel), "tendency": tendency,
                      "n_runs": n, "nudge": rel - tendency, "confidence": conf}
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


def train(out_dir=None):
    """Retrain the settling model. Reproduces
    wpr_settle_recency_nonlinear_test.py's validated pipeline exactly
    (same dedup, same 2-year window, same 5 features, same LightGBM
    hyperparameters) - ship what was tested, not a superset of it.

    Race key for the sect_signal ranking: (track, date, raceNumber) -
    same convention race_speed_estimate.py's own train() uses and
    documents (race_id in the raw form history identifies which race a
    row's CAPTURE was taken for, not necessarily a stable grouping key
    across a horse's whole scraped table for THIS purpose - track/date/
    raceNumber is the one already-verified-reliable alternative)."""
    import lightgbm as lgb
    from sklearn.metrics import mean_absolute_error
    import joblib

    print("Loading form history...")
    fh = _load_form()
    since = fh["date"].max() - pd.Timedelta(days=TRAIN_WINDOW_DAYS)
    n_before = len(fh)
    fh = fh[fh["date"] >= since].copy()
    print(f"  bounded to last {TRAIN_WINDOW_DAYS} days ({since.date()} onward): "
          f"{n_before:,} -> {len(fh):,} rows")
    fh = fh.sort_values(["horse_lc", "date"]).reset_index(drop=True)

    settle = pd.to_numeric(fh["positionSettled"], errors="coerce")
    fh["field_size"] = pd.to_numeric(fh["field_size"], errors="coerce")
    fs = fh["field_size"]
    valid = (settle > 0) & (fs > 0)
    rel = (settle / fs).clip(0, 1)
    rel_valid = rel.where(valid)
    g = fh["horse_lc"]

    print("Computing trailing run_style_tendency (all-time)...")
    csum_incl = rel_valid.fillna(0).groupby(g).cumsum()
    ccount_incl = valid.astype(int).groupby(g).cumsum()
    fh["run_style_tendency"] = (csum_incl.groupby(g).shift(1) /
                                ccount_incl.groupby(g).shift(1).replace(0, np.nan))

    print("Computing last5_tendency...")
    fh["_rel_for_roll"] = rel_valid
    fh["last5_tendency"] = fh.groupby("horse_lc")["_rel_for_roll"].transform(
        lambda s: s.rolling(5, min_periods=1).mean().shift(1))
    fh = fh.drop(columns=["_rel_for_roll"])

    print("Computing trailing sect_i_early...")
    sect_raw = pd.to_numeric(fh["sect_i_early"], errors="coerce")
    sect_clipped = sect_raw.clip(SECT_EARLY_LO, SECT_EARLY_HI)
    sect_valid = sect_clipped.notna()
    sect_valid_vals = sect_clipped.where(sect_valid)
    sect_csum = sect_valid_vals.fillna(0).groupby(g).cumsum()
    sect_ccount = sect_valid.astype(int).groupby(g).cumsum()
    fh["trailing_sect_i_early"] = (sect_csum.groupby(g).shift(1) /
                                   sect_ccount.groupby(g).shift(1).replace(0, np.nan))

    print("Computing race-relative sect_signal...")
    fh["barrier"] = pd.to_numeric(fh["barrier"], errors="coerce")
    fh["raceNumber"] = pd.to_numeric(fh["raceNumber"], errors="coerce")
    fh["_race_key"] = fh["track"].astype(str) + "|" + fh["date"].astype(str) + "|" + fh["raceNumber"].astype(str)
    fh["sect_rank_in_race"] = fh.groupby("_race_key")["trailing_sect_i_early"].rank(pct=True, na_option="keep")

    fh["draw_frac"] = ((fh["barrier"] - 1) / (fh["field_size"] - 1)).clip(0, 1)
    fh["draw_signal"] = (fh["draw_frac"] - 0.5) * 2
    fh["sect_signal"] = (fh["sect_rank_in_race"] - 0.5) * 2
    fh["actual_rel"] = rel_valid

    features = ["run_style_tendency", "last5_tendency", "draw_signal", "sect_signal", "field_size"]
    usable = fh.dropna(subset=features + ["actual_rel"]).copy()
    print(f"  usable rows (all features + target present): {len(usable):,}")

    cut = usable["date"].quantile(0.70)
    trn = usable[usable["date"] < cut]
    te = usable[usable["date"] >= cut]
    print(f"  split at {cut.date()}: {len(trn):,} train, {len(te):,} held-out test")

    med = trn[features].median()
    model = lgb.LGBMRegressor(n_estimators=200, max_depth=3, learning_rate=0.05,
                              num_leaves=8, random_state=42, verbosity=-1)
    model.fit(trn[features].fillna(med), trn["actual_rel"])
    pred_te = model.predict(te[features].fillna(med))
    mae = float(mean_absolute_error(te["actual_rel"], pred_te))
    print(f"  held-out MAE: {mae:.4f}")

    out_dir = Path(out_dir) if out_dir else _DIR
    out_dir.mkdir(exist_ok=True)
    joblib.dump(model, out_dir / "settling_model.joblib")
    json.dump({
        "features": features,
        "medians": med.to_dict(),
        "heldout_mae": mae,
        "n_train": int(len(trn)),
        "train_window_days": TRAIN_WINDOW_DAYS,
    }, open(out_dir / "settling_config.json", "w"), indent=1)
    print(f"  written -> {out_dir}/settling_model.joblib, settling_config.json")


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
    ap.add_argument("--retrain", action="store_true",
                    help="refit the settling model from wpr_form_history.csv.gz")
    args = ap.parse_args()

    if args.retrain:
        train()
    elif args.validate:
        validate(args.n)
    elif args.race:
        estimate_race(args.race)
    else:
        ap.print_help()


if __name__ == "__main__":
    main()
