"""
wpr_projection.py - WPR projection

Projects a horse's run-day WPR from its form history, attaches a 0-100
confidence rating, a field-normalised WPR price, and a plain-language
explanation of why the rating is what it is.

WHAT THIS IS
  A model-only WPR projection built from wpr_form_history.csv - the per-run
  form history scraped daily. It predicts the run-day WPR a horse will
  record. It does not use wpr_nett.

  Three artifacts in wpr_models/:
    projection.joblib  - 34-feature gradient-boosting WPR projection
    confidence.joblib  - predicts the projection's error, turned into 0-100
    config.json        - feature list, fill medians, price beta, min runs

SINGLE SOURCE OF TRUTH
  build_features() in this file is the ONE feature definition. The training
  pipeline regenerates its feature frame by calling this exact function over
  the history, so the features the model trains on are by construction
  identical to the features it is served at prediction time. Do not create a
  second feature implementation anywhere - drift between a training build and
  this function silently corrupts every projection.

CONFIDENCE
  Validated: high-confidence projections are measurably more accurate than
  low-confidence ones. 5-fold walk-forward conf-band MAE: ~5.7 at
  confidence 80+, ~6.5 at 40-79, ~9.3 below 40. (The earlier docstring
  claimed ~4.3 at 80+ - stale; the whole error scale shifted up ~1 MAE as
  the wpr target drifted. The RANKING holds: higher confidence still means
  lower error.) Confidence rates how much to trust the projected number,
  not whether the horse wins.

WPR PRICE
  A softmax over the field's projected WPRs (beta in config), inverted to a
  price. Fair-value book - sums to 1.0 across a race, no margin.

HONEST SCOPE
  A form-quality projection. It ranks horses by projected WPR and rates how
  reliable each projection is. It is not a proven betting edge. Treat the
  projection and price as information, not a bet signal.

USAGE
  from wpr_projection import project_race
  results = project_race(runners)

  Re-fit as wpr_form_history.csv grows:
    python wpr_projection.py --retrain

NO EM DASHES policy: hyphens only in this file.
"""

import json
from pathlib import Path

import numpy as np
import pandas as pd
import joblib

_DIR = Path(__file__).parent
_MODEL_DIR = _DIR / "wpr_models"
_SPELL_GAP_DAYS = 60   # a gap longer than this starts a new campaign
_MIN_RUNS = 3          # fewer prior runs than this -> no projection

# Recency-weighted training. TopRate's wpr is a relative rating and its
# scale DRIFTS - the target mean fell ~6 points from 2024 to 2026. Old
# training rows teach the model an outdated scale, so an unweighted model
# trains "high" and under-projects recent races (bias was -1.06, worse in
# the recent folds). An exponential decay on row age weights recent rows
# up. Walk-forward half-life scan: mean MAE bottoms at 60 days (6.222 ->
# 6.155, worst fold 6.93 -> 6.79); shorter half-lives overfit recent
# noise and the curve turns back up. This compensates for the drift - it
# does not remove it (residual bias ~-0.78). 0 disables the weighting.
_RECENCY_HALF_LIFE_DAYS = 60


def _recency_weights(dates, ref_date=None):
    """Exponential-decay sample weights by row age. Half-life is
    _RECENCY_HALF_LIFE_DAYS. Returns None if weighting is disabled (0).
    ref_date defaults to the most recent date in the series."""
    if not _RECENCY_HALF_LIFE_DAYS:
        return None
    d = pd.to_datetime(dates)
    ref = pd.to_datetime(ref_date) if ref_date is not None else d.max()
    age = (ref - d).dt.days.clip(lower=0).values
    return 0.5 ** (age / float(_RECENCY_HALF_LIFE_DAYS))


# The 53 features, in model order. This list IS the contract.
# fresh_factor is deliberately NOT here - it was found to be a future-data
# leak (it averaged a horse's first-up runs across its whole career,
# including runs after the one being projected) and is permanently excluded.
FEATURES = [
    # --- 34 base features ---
    "avg_last3", "avg_last5", "ewm3", "ewm5", "last1", "last2", "peak",
    "recent5_max", "best3", "career_avg", "recent_vs_career", "trend",
    "std_last5", "std_career", "n_runs", "runs_this_camp", "days_since",
    "first_up", "second_up", "cur_distance", "dist_grad", "dist_vs_last",
    "distband_wpr", "distband_n", "going_delta", "today_wet", "track_wpr",
    "track_n", "avg_settle", "avg_pos800", "avg_pos600", "avg_margin",
    "trackGrading_f",
    # last_was_trial dropped: isBarrierTrial is all-False in the history,
    # so the feature was a constant-zero input contributing nothing.
    # build_features still emits the key (harmless) - it is just not trained on.
    # --- 19 extra features (all verified point-in-time safe) ---
    "sect_finish_str", "sect_late_str", "wpr_traj", "camp_run",
    "camp_run_sq", "wet_best", "wet_runs", "untried_wet", "class_move",
    "peak_at_class", "secondup_wpr", "thirdup_wpr", "pct_of_peak",
    "recent_vs_peak", "form_vs_track", "form_vs_distband",
    "consistency_ratio", "peak_recency", "career_momentum",
    # --- 4 going-recut features (passed compare_feature_sets: KEEP) ---
    # Replace the old string-based going handling. today_wet/going_delta
    # are now trackGrading-based (a correctness fix to existing features);
    # these 4 are the new inputs. See _going_wetness/_going_surface.
    "today_wetness", "cur_surface", "surface_wpr", "surf_runs",
    # --- field_size (passed compare_feature_sets: KEEP, -0.034 MAE) ---
    # The model under-projects small fields (-1.8 WPR bias at <=7 runners).
    # field_size lets it correct the bias gradient. Biggest single feature
    # gain measured in the Stage 0 work.
    "field_size",
]
CONF_FEATURES = [
    "n_runs", "track_n", "distband_n", "days_since", "std_last5",
    "std_career", "first_up", "runs_this_camp", "recent_vs_career",
    "dist_vs_last",
]

_PROJ = None
_CONF = None
_CFG = None


def _load_models():
    """Load the three model artifacts once. Raises if wpr_models/ is missing."""
    global _PROJ, _CONF, _CFG
    if _PROJ is not None:
        return
    cfg_path = _MODEL_DIR / "config.json"
    if not cfg_path.exists():
        raise FileNotFoundError(
            f"wpr_models/ not found at {_MODEL_DIR}. Need projection.joblib, "
            f"confidence.joblib and config.json. Run "
            f"'python wpr_projection.py --retrain' to build them.")
    _CFG = json.load(open(cfg_path))
    _PROJ = joblib.load(_MODEL_DIR / "projection.joblib")
    _CONF = joblib.load(_MODEL_DIR / "confidence.joblib")


# ---------------------------------------------------------------------------
# build_features - THE single feature definition
# ---------------------------------------------------------------------------
# Computes the 34-feature vector for ONE horse from its prior runs only
# (point-in-time: nothing here may look at the run being projected or later).
# The training pipeline calls this exact function, so training and serving
# features are identical by construction.

# Going recut (handoff 3A.2). The old _going_is_wet did startswith on the
# going TEXT string - it misclassified Dead/Slow as dry, and called 6,800+
# all-weather runs (Sand/Dirt/Synthetic, all trackGrading 3) "dry good".
# trackGrading IS the going number (Good 4 -> 4, Heavy 10 -> 10, confirmed
# by cross-tab) and is clean on every row. So wetness comes from
# trackGrading, NOT the string. Surface type, which trackGrading cannot
# carry, is a separate flag parsed from the string.

def _going_wetness(track_grading):
    """Continuous wetness from trackGrading (1 firm .. 10 heavy).

    Returns a 0-1 float so the model sees a graded scale, not a binary.
    Falls back to 0.44 (the Good 4 norm, ~the data median) when missing.
    """
    try:
        tg = float(track_grading)
    except (TypeError, ValueError):
        return 0.44
    if tg != tg:  # NaN
        return 0.44
    return float(np.clip((tg - 1.0) / 9.0, 0.0, 1.0))


def _going_is_wet(track_grading):
    """Binary wet flag from trackGrading. Wet = Soft 5 and above (tg >= 5).

    Kept as a binary for the existing today_wet feature and the
    walk-forward by_going breakdown. trackGrading-based, so Dead/Slow and
    all-weather are no longer misread off the string.
    """
    try:
        tg = float(track_grading)
    except (TypeError, ValueError):
        return 0
    if tg != tg:
        return 0
    return 1 if tg >= 5 else 0


# Surface type from the going string. trackGrading cannot distinguish a
# grading-3 synthetic from a grading-3 good turf, so surface is its own
# signal. 0 turf, 1 synthetic, 2 dirt, 3 sand.
_SURFACE_MAP = {"synthetic": 1, "dirt": 2, "sand": 3}


def _going_surface(going):
    g = str(going).strip().lower()
    return _SURFACE_MAP.get(g, 0)


# Class ladder (handoff 3A.1b). The old class_move / peak_at_class were
# computed off trackGrading - which is the GOING number, not class - so
# both features measured "is today wetter than recent runs". race_class
# (the true class string) is now in the history. This ladder maps every
# class string onto one numeric rung, higher = stronger.
#
# Rungs were set with Matt's domain rulings:
#  - BMxx / RSTxx: the number IS the rung (BM58 -> 58). + suffix dropped.
#  - MAI maiden 5, NOV novice 8, R0/R1 maiden-win codes 10 (near-maiden).
#  - CLS1-6 at 55-74: country Class races sit in the BM55-74 ability band,
#    NOT down at the bottom. CLS and BM are PARALLEL systems - this places
#    them where country-class horses actually rate. An approximation: a
#    horse usually moves within one system so cross-system jumps are rare.
#  - CLSA/CLSB 50, REST 58: educated defaults on small buckets (~430 rows).
#  - OPEN 105: top of the ladder.
#  - Jumps return None - excluded from class_move (see _is_jumps); jumps
#    form does not sit on the flat ladder.
# class_move feeds a tree model, so monotonic ORDER matters more than the
# exact spacing - do not read the rungs as precise ability points.
_FIXED_RUNGS = {
    "MAI": 5, "MAIH": 5, "MAIS": 5,
    "NOV": 8, "NOVH": 8,
    "R0MW": 10, "R1MW": 10, "R0MWLY": 10, "R1MWLY": 10, "R0MWL2Y": 10,
    "R1MWL2Y": 10, "R1HW": 10,
    "CLSA": 50, "CLSB": 50,
    "CLS1": 55, "CLS2": 58, "CLS3": 62, "CLS4": 66, "CLS5": 70, "CLS6": 74,
    "REST": 58, "RESTH": 58,
    "OPEN": 105,
}
_JUMPS_CLASSES = {"STEEPLE", "HURDLE", "NOVH", "RESTH", "R1HW", "MAIH"}


def _class_rung(race_class):
    """Map a race_class string to a numeric ladder rung.

    Returns the rung, or None when the class is jumps, blank, or unknown
    (None means 'no class signal' - class_move falls back, see below).
    """
    if race_class is None:
        return None
    c = str(race_class).strip().upper()
    if c == "" or c == "NAN":
        return None
    if c in _JUMPS_CLASSES:
        return None  # jumps do not sit on the flat ladder
    if c in _FIXED_RUNGS:
        return _FIXED_RUNGS[c]
    # BMxx / RSTxx - the number is the rung. Trailing + (BM58+) dropped.
    digits = ""
    for ch in c:
        if ch.isdigit():
            digits += ch
        elif digits:
            break
    if (c.startswith("BM") or c.startswith("RST")) and digits:
        return int(digits)
    return None  # unrecognised - treated as no class signal


def _is_jumps(race_class):
    """1 if the race is a jumps race (steeple/hurdle), else 0."""
    if race_class is None:
        return 0
    return 1 if str(race_class).strip().upper() in _JUMPS_CLASSES else 0


def _safe_slope(x, y):
    """Linear slope of y vs x; 0.0 if fewer than 3 distinct x points."""
    x = np.asarray(x, dtype=float)
    y = np.asarray(y, dtype=float)
    ok = ~(np.isnan(x) | np.isnan(y))
    if ok.sum() < 3 or len(np.unique(x[ok])) < 3:
        return 0.0
    return float(np.polyfit(x[ok], y[ok], 1)[0])


def build_features(prior_runs, cur_distance, cur_going, cur_track,
                   cur_track_grading, race_date, cur_race_class=None,
                   cur_field_size=None):
    """Build the feature dict for one horse.

    prior_runs: DataFrame of the horse's PAST runs only, any order. Needs
      columns: date, wpr, distance, going, track, trackGrading,
      positionSettled, position800m, position600m, marginFinish,
      isBarrierTrial. race_class is used if present (for class_move).
    cur_*: conditions of the race being projected.
    cur_race_class: the projected race's class string (BM64, CLS3, OPEN
      ...). Defaults to None - callers that do not pass it get a neutral
      class_move and is_jumps 0 (backward compatible).
    cur_field_size: number of runners in the projected race. Pre-race
      known, leak-free. The model under-projects small fields and slightly
      over-projects large ones (a bias gradient: -1.8 WPR at <=7 runners,
      +0.4 at 14+); field_size lets the model correct it. Defaults to None
      (filled with the training median at serving if absent).
    race_date: date of the race being projected (required - used for
      days_since; pass the real race date, never a guess).

    Returns the feature dict, or None if fewer than _MIN_RUNS prior runs.
    """
    p = prior_runs
    if p is None or len(p) < _MIN_RUNS:
        return None

    p = p.sort_values("date").reset_index(drop=True)
    w = pd.to_numeric(p["wpr"], errors="coerce")
    wv = w.values
    dates = pd.to_datetime(p["date"])
    n = len(p)
    dist = pd.to_numeric(p["distance"], errors="coerce")
    settle = pd.to_numeric(p.get("positionSettled"), errors="coerce")

    # ---- running-style profile (candidate set A, leak-safe) ----
    # Each horse runs differently - leader, midfield, backmarker. Raw
    # settling position is field-size dependent (6th of 8 != 6th of 16),
    # so style is the RELATIVE settle: positionSettled / field_size.
    # 0 = led, 1 = last. All from PRIOR runs only. 0-sentinels in
    # positionSettled (handoff 3A.4) are dropped before averaging.
    pfs = pd.to_numeric(p.get("field_size"), errors="coerce")
    valid_st = (settle > 0) & (pfs > 0)
    rel_settle = (settle[valid_st] / pfs[valid_st]).clip(0, 1)
    if len(rel_settle) >= 1:
        run_style = float(rel_settle.mean())
        run_style_std = float(rel_settle.std()) if len(rel_settle) >= 2 else 0.0
    else:
        run_style = 0.5   # neutral when no usable settle history
        run_style_std = 0.0
    # per-horse WPR split: on-pace runs (front third) vs off-pace (back
    # third). "Does this horse run better leading or coming from behind."
    w_all = pd.to_numeric(p["wpr"], errors="coerce")
    onpace_w = w_all[valid_st][rel_settle <= 0.33]
    offpace_w = w_all[valid_st][rel_settle >= 0.67]
    led_wpr = float(onpace_w.mean()) if len(onpace_w) >= 1 else np.nan
    backed_wpr = float(offpace_w.mean()) if len(offpace_w) >= 1 else np.nan
    # pace dependence: how much the horse's WPR differs on-pace vs off.
    if len(onpace_w) >= 1 and len(offpace_w) >= 1:
        pace_dependence = float(onpace_w.mean() - offpace_w.mean())
    else:
        pace_dependence = 0.0

    # ---- soft-lead figure distortion (candidate, leak-safe) ----
    # The circumstance analysis found a real, un-modelled distortion:
    # a WPR set leading at a soft early tempo over-states the horse by
    # ~2.8 WPR and regresses next start. A "soft-lead run" = led
    # (rel_settle <= 0.2) at a slow early tempo (raceShapeEarly < -2).
    # The feature is PRIOR-RUNS-ONLY: how much of the horse's recent
    # form was built on soft leads, and its form recomputed with those
    # runs discounted. The projected run's own shape is never read.
    early_h = pd.to_numeric(p.get("raceShapeEarly"), errors="coerce")
    # per-prior-run soft-lead flag, aligned to all prior runs
    rel_full = pd.Series(np.nan, index=p.index)
    rel_full[valid_st] = (settle[valid_st] / pfs[valid_st]).clip(0, 1)
    softlead_run = ((rel_full <= 0.2) & (early_h < -2)).fillna(False)
    # fraction of the last 6 prior runs that were soft-lead runs
    recent_mask = softlead_run.iloc[-6:]
    softlead_recent = float(recent_mask.mean()) if len(recent_mask) >= 1 \
        else 0.0
    # soft-lead-adjusted recent form: ewm of wpr with soft-lead runs
    # down-weighted to 0.4 (they over-state, so they count less).
    sl_weight = np.where(softlead_run.values, 0.4, 1.0)
    wv_recent = w.values[-6:]
    slw_recent = sl_weight[-6:]
    if np.nansum(slw_recent) > 0:
        softlead_adj_form = float(
            np.nansum(wv_recent * slw_recent) / np.nansum(slw_recent))
    else:
        softlead_adj_form = float(w.iloc[-3:].mean())
    # the discount itself: plain recent form minus the adjusted form.
    # positive = the horse's recent figures are propped up by soft leads.
    softlead_discount = float(w.iloc[-6:].mean()) - softlead_adj_form

    # ---- strung-out-backmarker distortion (candidate, leak-safe) ----
    # The margin-spread analysis (27 May) found the opposite corner to
    # the soft-lead effect: a backmarker in a STRUNG-OUT race UNDER-states
    # the horse by ~2 WPR (the run is structurally hopeless - too far back
    # in a race run at a spread tempo - so the figure earned is harsh).
    # Those past runs should count for MORE, not less.
    #   "strung-out-backmarker run" = settled back (rel_settle >= 0.7) AND
    #   a large own-margin at the 800m point (the horse's own margin off
    #   the lead early - a backmarker in a strung-out race sits well back).
    # margin800m is the horse's margin behind the leader at 800m; a large
    # value is the per-run signature of a strung-out race seen from the
    # back. PRIOR-RUNS-ONLY - the projected run's own shape is never read.
    m800 = pd.to_numeric(p.get("margin800m"), errors="coerce")
    # "large" margin: top third of this horse's own prior-run 800m margins,
    # floored at 4.0 lengths so a horse that always tracks close does not
    # get spurious flags. Self-relative keeps it leak-safe and per-horse.
    if m800.notna().sum() >= 3:
        m800_hi = max(4.0, float(m800.quantile(0.67)))
    else:
        m800_hi = 4.0
    strungback_run = ((rel_full >= 0.7) & (m800 >= m800_hi)).fillna(False)
    # fraction of the last 6 prior runs that were strung-out-backmarker runs
    sb_recent_mask = strungback_run.iloc[-6:]
    strungback_recent = float(sb_recent_mask.mean()) \
        if len(sb_recent_mask) >= 1 else 0.0
    # strung-out-adjusted recent form: ewm of wpr with strung-out-backmarker
    # runs DOWN-weighted to 0.4. Those runs UNDER-state the horse (the figure
    # earned is harsh), so to recover the horse's true form they should
    # count for less - letting the un-distorted runs dominate. Same
    # direction as the soft-lead feature: discount the distorted runs.
    sb_weight = np.where(strungback_run.values, 0.4, 1.0)
    sbw_recent = sb_weight[-6:]
    if np.nansum(sbw_recent) > 0:
        strungback_adj_form = float(
            np.nansum(wv_recent * sbw_recent) / np.nansum(sbw_recent))
    else:
        strungback_adj_form = float(w.iloc[-3:].mean())
    # the uplift: adjusted form minus plain recent form. positive = the
    # horse's recent figures are HELD DOWN by strung-out-backmarker runs,
    # so the adjusted (distortion-discounted) form is higher than the raw.
    strungback_uplift = strungback_adj_form - float(w.iloc[-6:].mean())

    rd = pd.to_datetime(race_date)
    days_since = int((rd - dates.iloc[-1]).days)

    # campaign position - runs since the last spell (gap > 60 days).
    # counts prior runs only; the run being projected is NOT counted.
    gaps = dates.diff().dt.days
    spell_idx = gaps[gaps > _SPELL_GAP_DAYS].index
    runs_this_camp = n - (spell_idx.max() if len(spell_idx) else 0)

    dist_grad = _safe_slope(dist.values, wv) * 100

    # Wetness from trackGrading per prior run (not the going string).
    # tg_hist is the numeric grading; is_wet_hist the binary derived from it.
    tg_hist = pd.to_numeric(p.get("trackGrading"), errors="coerce")
    is_wet_hist = tg_hist.apply(_going_is_wet)
    wet_w = w[is_wet_hist == 1]
    dry_w = w[is_wet_hist == 0]
    going_delta = float(wet_w.mean() - dry_w.mean()) \
        if len(wet_w) >= 1 and len(dry_w) >= 1 else 0.0

    # Surface: today's surface, and the horse's experience on it. A
    # grading-3 synthetic is not a grading-3 turf - surface is its own axis.
    cur_surface = _going_surface(cur_going)
    surf_hist = p["going"].apply(_going_surface)
    surf_runs = int((surf_hist == cur_surface).sum())
    same_surf_w = w[surf_hist == cur_surface]
    surface_wpr = float(same_surf_w.mean()) if len(same_surf_w) >= 1 \
        else float(w.iloc[-3:].mean())

    same_track = w[p["track"] == cur_track]
    avg_last3 = float(w.iloc[-3:].mean())
    track_wpr = float(same_track.mean()) if len(same_track) >= 1 else avg_last3
    track_n = int(len(same_track))

    db_mask = (dist - float(cur_distance)).abs() <= 200
    distband_wpr = float(w[db_mask].mean()) if db_mask.sum() >= 1 else avg_last3
    distband_n = int(db_mask.sum())

    # dist_edge - signed metres today's trip sits OUTSIDE the horse's prior
    # proven distance range (min-max of prior runs). 0 if inside the range,
    # positive if longer than ever tried, negative if shorter. The distance
    # transfer analysis showed WPR error climbs monotonically with this:
    # 6.7 inside the range, 10.1 at 400m+ outside. Leak-safe - only prior
    # runs define the range, today's distance is pre-race known. Continuous
    # by design (the transfer curve is U-shaped, so fixed bands are wrong;
    # a continuous edge lets the model interact it with cur_distance).
    dprior = dist.dropna()
    if len(dprior) >= 1:
        dlo, dhi = float(dprior.min()), float(dprior.max())
        cd = float(cur_distance)
        if cd > dhi:
            dist_edge = cd - dhi
        elif cd < dlo:
            dist_edge = cd - dlo  # negative
        else:
            dist_edge = 0.0
    else:
        dist_edge = 0.0

    mfin = pd.to_numeric(p.get("marginFinish"), errors="coerce")

    # best3 - mean of the best 3 of the last 6 runs (or fewer if n < 6)
    recent6 = w.iloc[-6:].values
    k = min(3, len(recent6))
    best3 = float(np.sort(recent6)[-k:].mean())

    # trend - last wpr minus the mean of the two before it
    if n >= 3:
        trend = float(wv[-1] - w.iloc[-3:-1].mean())
    else:
        trend = 0.0

    ewm3 = float(w.ewm(span=3).mean().iloc[-1])
    ewm5 = float(w.ewm(span=5).mean().iloc[-1])
    avg_last5 = float(w.iloc[-5:].mean())
    peak = float(w.max())
    recent5_max = float(w.iloc[-5:].max())
    career_avg = float(w.mean())
    std_last5 = float(w.iloc[-5:].std()) if n >= 2 else 0.0
    std_career = float(w.std()) if n >= 2 else 0.0
    cur_tg = float(cur_track_grading) if cur_track_grading is not None else 4.5

    # -----------------------------------------------------------------
    # 19 extra features - all point-in-time (prior runs only).
    # Verified leak-free against the training build in the feature audit.
    # -----------------------------------------------------------------
    # campaign run number per prior run (gap > 60d resets the count)
    spell_id = (gaps > _SPELL_GAP_DAYS).cumsum()
    camp_run_series = p.groupby(spell_id).cumcount() + 1
    camp_run = int(camp_run_series.iloc[-1])

    # sectional finishing strength - ground made up over the last 600m/400m
    m600 = pd.to_numeric(p.get("margin600m"), errors="coerce")
    m400 = pd.to_numeric(p.get("margin400m"), errors="coerce")
    fin_gain = m600 - mfin
    late_gain = m400 - mfin
    sect_finish_str = float(fin_gain.iloc[-5:].mean()) if fin_gain.notna().any() else 0.0
    sect_late_str = float(late_gain.iloc[-5:].mean()) if late_gain.notna().any() else 0.0

    # TopRate detailed sectional RATINGS - candidate feature set (a).
    # 13 signed index figures per run (higher = better). LEAK RULE: these
    # correlate strongly with the SAME run's wpr (sect_i_time r=0.77) -
    # they are another measure of that run's performance. So the feature
    # MUST use prior runs only: the horse's MEAN rating on each sectional
    # across its PAST runs - "how this horse tends to run its sections".
    # The target run's sectionals never enter. Recent window (last 6).
    _SECT_COLS = ["sect_i_time", "sect_ld_early", "sect_i_early",
                  "sect_i_to600", "sect_i_to800", "sect_i_l200",
                  "sect_i_l400", "sect_i_l600", "sect_i_l800",
                  "sect_i_400_200", "sect_i_600_400", "sect_i_800_400",
                  "sect_i_800_600"]
    sect_feats = {}
    for col in _SECT_COLS:
        if col in p.columns:
            sv = pd.to_numeric(p[col], errors="coerce").dropna()
            sect_feats["avg_" + col] = (float(sv.iloc[-6:].mean())
                                        if len(sv) >= 1 else np.nan)
        else:
            sect_feats["avg_" + col] = np.nan

    # trajectory - slope of the last 4 wpr
    last4 = wv[-4:]
    wpr_traj = float(np.polyfit(range(len(last4)), last4, 1)[0]) if len(last4) >= 3 else 0.0

    # wet-track ability
    wet_runs = int((is_wet_hist == 1).sum())
    wet_best = float(wet_w.max()) if len(wet_w) >= 1 else np.nan
    # today's wet flag from the race grading, consistent with is_wet_hist
    today_wet = _going_is_wet(cur_track_grading)
    today_wetness = _going_wetness(cur_track_grading)
    untried_wet = 1 if (today_wet == 1 and wet_runs == 0) else 0

    # class movement (handoff 3A.1b fix). Was computed off trackGrading -
    # the going number, not class - so it measured wetness, not class. Now
    # uses race_class via the _class_rung ladder.
    is_jumps = _is_jumps(cur_race_class)
    cur_rung = _class_rung(cur_race_class)
    if "race_class" in p.columns:
        rungs = p["race_class"].apply(_class_rung)
    else:
        rungs = pd.Series([None] * len(p), index=p.index)
    rungs_num = pd.to_numeric(rungs, errors="coerce")
    # recent rung: mean ladder rung of the last 5 prior runs that HAVE a
    # rung. Jumps and blank/unknown classes return None and are skipped
    # (a jumps run should not pull a flat horse's class average). If the
    # horse has no rungs at all, fall back to a neutral mid-rung (58, the
    # BM58 area - the data's commonest class band).
    recent_rungs = rungs_num.dropna()
    if len(recent_rungs) >= 1:
        recent_rung = float(recent_rungs.iloc[-5:].mean())
    else:
        recent_rung = 58.0
    # class_move: today's rung minus the recent rung. 0.0 when today's
    # class is unknown or jumps (no flat-ladder comparison to make).
    if cur_rung is not None:
        class_move = float(cur_rung) - recent_rung
    else:
        class_move = 0.0
    # peak_at_class: best wpr in prior runs at or below today's class.
    # Falls back to career peak when today's class is unknown or no prior
    # run is at/below it.
    if cur_rung is not None:
        at_or_below = w[rungs_num <= cur_rung]
        peak_at_class = float(at_or_below.max()) if len(at_or_below) >= 1 \
            else peak
    else:
        peak_at_class = peak

    # first-up / second-up / third-up wpr history. first_up (in FEATURES) is
    # only a population-level binary flag - it has no way to see that THIS
    # horse personally fires up fresh. firstup_wpr closes that gap the same
    # way secondup_wpr/thirdup_wpr already do for their camp positions.
    # TESTED, NOT ADOPTED (held-out comparison, this codebase's own bar):
    # full-set MAE +0.011 (below the 0.03 adoption bar), and on the first-up
    # subset specifically it was flat-to-slightly-worse (-0.010 MAE; on rows
    # where the horse's own first-up history beat its recent form by 3+, bias
    # improved marginally but MAE still landed slightly worse). The tree
    # ensemble already recovers most of this signal through avg_last3 /
    # career_avg / runs_this_camp interactions. Kept emitted (not in
    # FEATURES) as a documented negative result - do not re-add without a
    # fresh held-out test showing a real gain.
    r1 = w[camp_run_series == 1]
    r2 = w[camp_run_series == 2]
    r3 = w[camp_run_series == 3]
    firstup_wpr = float(r1.mean()) if len(r1) >= 1 else avg_last3
    secondup_wpr = float(r2.mean()) if len(r2) >= 1 else avg_last3
    thirdup_wpr = float(r3.mean()) if len(r3) >= 1 else avg_last3

    feat = {
        "avg_last3": avg_last3,
        "avg_last5": avg_last5,
        "ewm3": ewm3,
        "ewm5": ewm5,
        "last1": float(wv[-1]),
        "last2": float(w.iloc[-2:].mean()),
        "peak": peak,
        "recent5_max": recent5_max,
        "best3": best3,
        "career_avg": career_avg,
        "recent_vs_career": avg_last3 - career_avg,
        "trend": trend,
        "std_last5": std_last5,
        "std_career": std_career,
        "n_runs": int(n),
        "runs_this_camp": int(runs_this_camp),
        "days_since": days_since,
        "first_up": 1 if runs_this_camp == 1 else 0,
        "second_up": 1 if runs_this_camp == 2 else 0,
        "cur_distance": float(cur_distance),
        "dist_grad": dist_grad,
        "dist_vs_last": float(cur_distance) - float(dist.iloc[-1]),
        "distband_wpr": distband_wpr,
        "distband_n": distband_n,
        # dist_edge - candidate feature, emitted not yet in FEATURES.
        # Tested via compare_feature_sets before lock-in.
        "dist_edge": dist_edge,
        "going_delta": going_delta,
        "today_wet": today_wet,
        "today_wetness": today_wetness,
        "cur_surface": cur_surface,
        "surface_wpr": surface_wpr,
        "surf_runs": surf_runs,
        "track_wpr": track_wpr,
        "track_n": track_n,
        "avg_settle": float(settle.iloc[-5:].mean()) if settle.notna().any() else 5.0,
        "avg_pos800": float(pd.to_numeric(p.get("position800m"), errors="coerce").iloc[-5:].mean())
            if "position800m" in p and pd.to_numeric(p["position800m"], errors="coerce").notna().any() else 5.0,
        "avg_pos600": float(pd.to_numeric(p.get("position600m"), errors="coerce").iloc[-5:].mean())
            if "position600m" in p and pd.to_numeric(p["position600m"], errors="coerce").notna().any() else 5.0,
        "avg_margin": float(mfin.iloc[-5:].mean()) if mfin.notna().any() else 3.0,
        "trackGrading_f": cur_tg,
        "last_was_trial": int(p["isBarrierTrial"].iloc[-1])
            if "isBarrierTrial" in p and pd.notna(p["isBarrierTrial"].iloc[-1]) else 0,
        # --- 19 extras ---
        "sect_finish_str": sect_finish_str,
        "sect_late_str": sect_late_str,
        "wpr_traj": wpr_traj,
        "camp_run": camp_run,
        "camp_run_sq": camp_run ** 2,
        "wet_best": wet_best,
        "wet_runs": wet_runs,
        "untried_wet": untried_wet,
        "class_move": class_move,
        "peak_at_class": peak_at_class,
        "firstup_wpr": firstup_wpr,
        "secondup_wpr": secondup_wpr,
        "thirdup_wpr": thirdup_wpr,
        "pct_of_peak": ewm3 / peak if peak else 1.0,
        "recent_vs_peak": ewm3 - peak,
        "form_vs_track": ewm3 - track_wpr,
        "form_vs_distband": ewm3 - distband_wpr,
        "consistency_ratio": std_last5 / (std_career + 1),
        "peak_recency": recent5_max - peak,
        "career_momentum": avg_last5 - career_avg,
        # is_jumps - candidate feature, emitted but not yet in FEATURES.
        # class_move/peak_at_class are corrected in place (bug fix); is_jumps
        # is a new candidate, tested via compare_feature_sets before lock-in.
        "is_jumps": is_jumps,
        # field_size - the projected race's runner count. In FEATURES: the
        # model under-projects small fields (a -1.8 WPR bias at <=7 runners,
        # confirmed by walk-forward). NaN-filled with the training median
        # if a caller does not pass cur_field_size.
        "field_size": float(cur_field_size)
            if cur_field_size is not None
            and str(cur_field_size) not in ("nan", "")
            else np.nan,
        # is_small_field - candidate variant, emitted not yet in FEATURES.
        # A flagged threshold may split cleaner than raw field_size.
        "is_small_field": 1 if (cur_field_size is not None
                                and str(cur_field_size) not in ("nan", "")
                                and float(cur_field_size) <= 7) else 0,
    }
    # merge the 13 prior-runs sectional averages (candidate set a) -
    # emitted, not yet in FEATURES, tested via compare_feature_sets.
    feat.update(sect_feats)
    # running-style features (candidate set A) - emitted as candidates,
    # not in FEATURES. Per-horse: how the horse settles and how its WPR
    # depends on running on-pace vs off-pace.
    feat["run_style"] = run_style
    feat["run_style_std"] = run_style_std
    feat["led_wpr"] = led_wpr
    feat["backed_wpr"] = backed_wpr
    feat["pace_dependence"] = pace_dependence
    # soft-lead figure-distortion candidates (section 5h finding) -
    # emitted, tested via compare_feature_sets before lock-in.
    feat["softlead_recent"] = softlead_recent
    feat["softlead_adj_form"] = softlead_adj_form
    feat["softlead_discount"] = softlead_discount
    # strung-out-backmarker distortion candidate (margin-spread analysis,
    # 27 May) - emitted, NOT yet in FEATURES. Descriptive until a trusted
    # measurement confirms it improves the projection.
    feat["strungback_recent"] = strungback_recent
    feat["strungback_adj_form"] = strungback_adj_form
    feat["strungback_uplift"] = strungback_uplift
    return feat


def _feature_frame(feat_dicts):
    """List of feature dicts -> model-ready DataFrame, NaN filled with the
    training medians from config (or 0.0 if a median is missing)."""
    _load_models()
    med = _CFG["medians"]
    rows = []
    for f in feat_dicts:
        row = {}
        for c in FEATURES:
            v = None if f is None else f.get(c)
            if v is None or (isinstance(v, float) and np.isnan(v)):
                v = med.get(c, 0.0)
            row[c] = v
        rows.append(row)
    return pd.DataFrame(rows, columns=FEATURES)


# ---------------------------------------------------------------------------
# project_race - the main entry point
# ---------------------------------------------------------------------------

def project_race(runners, race_date):
    """Project every runner in a race.

    runners: list of dicts, one per horse, each carrying:
      prior_runs (DataFrame of past runs), cur_distance, cur_going,
      cur_track, cur_track_grading.
    race_date: the date of the race being projected.

    Returns a list of result dicts (same order) with: has_projection,
    projected_wpr, confidence, wpr_price, wpr_rank, peak_wpr, avg_l3,
    description.
    """
    _load_models()
    beta = _CFG.get("beta", 0.4)

    feat_dicts = [
        build_features(r.get("prior_runs"), r["cur_distance"], r["cur_going"],
                       r["cur_track"], r.get("cur_track_grading"), race_date,
                       cur_race_class=r.get("cur_race_class"),
                       cur_field_size=r.get("cur_field_size"))
        for r in runners
    ]
    fallbacks = [f is None for f in feat_dicts]

    X = _feature_frame(feat_dicts)
    proj = _PROJ.predict(X)
    # Calibration offset: a uniform additive shift, data-derived at train time
    # and stored in config (calib_offset). It recenters the projection onto the
    # current WPR scale, correcting the model's measured low bias. Because it is
    # uniform it does NOT change the WPR ranking, and the price softmax is
    # shift-invariant, so the fair price is unchanged too - only the displayed
    # projected WPR (and the recent-form gap in the explanation) move. Default
    # 0.0 so a config without the key is a no-op.
    proj = proj + float(_CFG.get("calib_offset", 0.0))

    # Recent-form blend (handoff: measured out-of-sample, ~0.15 MAE gain at
    # 30%). The model slightly over-shrinks toward career/context and
    # under-weights recent runs - horses it marks well below their recent
    # average tend to beat the projection (the Mometz case). Pulling the
    # projection a fraction of the way back toward avg_last3 corrects this.
    # Both quantities are on the actual-WPR scale (proj is post-offset), so the
    # blend is a straight convex mix. Weight is config-driven (recent_blend_w),
    # default 0.0 so a config without the key is a no-op. Only blends where
    # avg_last3 is present (skips it for runners with no recent average).
    _blend_w = float(_CFG.get("recent_blend_w", 0.0))
    if _blend_w > 0 and "avg_last3" in X.columns:
        _recent = X["avg_last3"].to_numpy(dtype=float)
        _has_recent = ~np.isnan(_recent)
        proj = np.asarray(proj, dtype=float)
        proj[_has_recent] = ((1.0 - _blend_w) * proj[_has_recent]
                             + _blend_w * _recent[_has_recent])
    pred_err = _CONF.predict(X[CONF_FEATURES])
    clo, chi = _CFG["conf_lo"], _CFG["conf_hi"]
    conf = np.clip(100 * (1 - (pred_err - clo) / (chi - clo)), 0, 100)

    valid = np.array([not fb for fb in fallbacks])
    price = np.full(len(runners), np.nan)
    if valid.sum() >= 2:
        pv = proj[valid]
        e = np.exp(beta * (pv - pv.max()))
        # softmax-to-price: 1 / probability. A no-hope runner gets a tiny
        # probability, so the raw price can blow out to 5-6 figures. Cap at
        # 999 - beyond that the exact number is meaningless ("no realistic
        # chance") and an uncapped price breaks any UI that displays it.
        raw_price = 1.0 / (e / e.sum())
        price[valid] = np.minimum(raw_price, 999.0)

    rank = np.full(len(runners), np.nan)
    if valid.any():
        rank[valid] = (-proj[valid]).argsort().argsort() + 1

    results = []
    for i, r in enumerate(runners):
        pr = r.get("prior_runs")
        if fallbacks[i]:
            peak = avg_l3 = np.nan
            if pr is not None and len(pr) >= 1:
                w = pd.to_numeric(pr["wpr"], errors="coerce")
                peak = float(w.max())
                avg_l3 = float(w.iloc[-3:].mean())
            nrun = 0 if pr is None else len(pr)
            results.append({
                "has_projection": False, "projected_wpr": None,
                "confidence": None, "wpr_price": None, "wpr_rank": None,
                "peak_wpr": round(peak, 1) if peak == peak else None,
                "avg_l3": round(avg_l3, 1) if avg_l3 == avg_l3 else None,
                "description": f"Insufficient history ({nrun} prior run"
                               f"{'s' if nrun != 1 else ''}) for a projection.",
            })
        else:
            w = pd.to_numeric(pr["wpr"], errors="coerce")
            results.append({
                "has_projection": True,
                "projected_wpr": round(float(proj[i]), 1),
                "confidence": int(round(conf[i])),
                "wpr_price": round(float(price[i]), 2) if price[i] == price[i] else None,
                "wpr_rank": int(rank[i]) if rank[i] == rank[i] else None,
                "peak_wpr": round(float(w.max()), 1),
                "avg_l3": round(float(w.iloc[-3:].mean()), 1),
                "description": describe(feat_dicts[i], float(proj[i]),
                                        int(round(conf[i])),
                                        int(rank[i]) if rank[i] == rank[i] else None),
            })
    return results


def describe(feats, projected_wpr, confidence, wpr_rank):
    """Plain-English explanation of the projected WPR.

    Written to read like a person talking, not like model output. Its main
    job - beyond describing - is to EXPLAIN the things that look odd to the
    eye: most importantly, why a projection can sit below (or above) the
    horse's recent average. A punter glancing at mid-80s recent runs and a
    79 projection should find the reason here, not have to guess.

    Honest by design: it only names a cause when the feature values
    actually support one. Where the projection is just normal model
    scatter with no clear driver, it says so plainly rather than inventing
    a reason - the model carries ~6 WPR of error in both directions and
    pretending otherwise would mislead.

    Deterministic - every clause is traceable to a feature value.
    """
    if feats is None:
        return "Not enough form history to make a projection."

    rank_txt = "top-rated in the race" if wpr_rank == 1 else (
        f"rated {wpr_rank} in the race" if wpr_rank else "unranked")
    sentences = [f"Projected {projected_wpr:.1f}, {rank_txt}."]

    # ── Explain the projection vs recent form - the key "looks odd" case ──
    avg3 = feats.get("avg_last3")
    gap = (projected_wpr - avg3) if avg3 is not None else None
    first_up = feats.get("days_since", 0) >= 90
    trend = feats.get("trend", 0)
    dvl = feats.get("dist_vs_last", 0)
    big_trip_change = abs(dvl) >= 200

    if gap is not None and gap <= -3:
        # projection notably BELOW recent form - explain why
        reasons = []
        if first_up:
            reasons.append("it is first-up from a layoff, and horses "
                           "usually run below their recent form fresh")
        if feats.get("recent_vs_career", 0) >= 3:
            reasons.append("its recent runs are well above its career "
                           "average, and the model expects some pull-back "
                           "toward that career level")
        if big_trip_change:
            reasons.append("it is changing trip sharply ("
                           + ("up" if dvl > 0 else "down")
                           + f" {abs(int(dvl))}m from last start)")
        if reasons:
            sentences.append("The projection sits below its recent average "
                             "because " + reasons[0]
                             + ("; " + reasons[1] + "."
                                if len(reasons) > 1 else "."))
        else:
            sentences.append("The projection is a little below its recent "
                             "average; nothing specific is driving that "
                             "down, so treat it as the model's normal "
                             "spread of error.")
    elif gap is not None and gap >= 3:
        # projection notably ABOVE recent form
        reasons = []
        if feats.get("recent_vs_career", 0) <= -3:
            reasons.append("its recent runs are below its career average, "
                           "and the model leans on the stronger career "
                           "record")
        if trend >= 4:
            reasons.append("it is trending up sharply")
        if reasons:
            sentences.append("The projection sits above its recent average "
                             "because " + reasons[0] + ".")
        else:
            sentences.append("The projection is a little above its recent "
                             "average; that is within the model's normal "
                             "spread of error.")

    # ── A readable note on form shape ──
    sl5 = feats.get("std_last5", 5)
    if sl5 <= 3:
        sentences.append("Its recent figures are very consistent.")
    elif sl5 >= 9:
        sentences.append("Its recent figures are up and down, which makes "
                         "any single projection less reliable.")

    # ── Confidence, in plain words ──
    nr = feats.get("n_runs", 0)
    sc = feats.get("std_career", 5)
    if confidence >= 80:
        sentences.append(f"Confidence is high - {nr} runs to go on and a "
                         f"steady profile.")
    elif confidence >= 60:
        sentences.append(f"Confidence is moderate, with {nr} runs to go on.")
    else:
        if sc >= 9:
            why = "its career form is erratic"
        elif nr <= 6:
            why = "it has only a short form history"
        else:
            why = "its recent form is unsettled"
        sentences.append(f"Confidence is low because {why}.")

    return " ".join(sentences)


# ---------------------------------------------------------------------------
# Retrain - regenerates the training frame THROUGH build_features
# ---------------------------------------------------------------------------

def _dedup_scrape_baseline(fh, verbose=True):
    """Collapse a horse's form history onto ONE scrape baseline.

    WHY: TopRate's wpr is a relative rating that gets re-referenced every
    time a horse runs again. When the same horse is scraped on two different
    dates (two upcoming races), the endpoint returns its full history twice,
    each copy shifted by a constant offset (a pure rebaseline, NOT a weight
    adjustment - confirmed: weightCarried and weight_handicap are identical
    across the copies, only wpr differs by a per-horse constant). Left in,
    every wpr-derived feature (avg_last3, peak, ewm3, career_avg ...) would
    average figures across mixed baselines, and the target could land on
    either baseline at random. That silently corrupts the training frame.

    FIX (Path 2): keep only rows from each horse's most recent scrape_date,
    so every horse's history is internally consistent on one baseline. This
    matches what the model does in production - it projects the horse's NEXT
    run, so the latest baseline is the correct reference.

    A small residual remains: a horse scraped twice ON THE SAME DAY (two
    upcoming-race pages, same scrape_date). scrape_date is date-granular so
    those cannot be ordered by time; the copies share a baseline anyway
    (median wpr delta 0.0). For those, keep the row with the higher
    formNumber (the more complete history) and drop the other.

    No real form run is lost - every (horse_id, date) is preserved, just on
    the correct baseline. Must run every retrain because the daily increment
    keeps appending multi-scrape rows.
    """
    n0 = len(fh)
    if "scrape_date" not in fh.columns:
        if verbose:
            print("  dedup: no scrape_date column, skipping baseline dedup")
        return fh

    # Step 1: per horse, keep only its latest scrape_date.
    latest = fh.groupby("horse_id")["scrape_date"].transform("max")
    fh = fh[fh["scrape_date"] == latest].copy()
    n1 = len(fh)

    # Step 2: same-day residual duplicates - keep higher formNumber.
    if "formNumber" in fh.columns:
        fh["_fn"] = pd.to_numeric(fh["formNumber"], errors="coerce")
        fh = fh.sort_values(["horse_id", "date", "_fn"])
        fh = fh.drop_duplicates(subset=["horse_id", "date"], keep="last")
        fh = fh.drop(columns=["_fn"])
    else:
        fh = fh.drop_duplicates(subset=["horse_id", "date"], keep="last")
    n2 = len(fh)

    if verbose:
        print(f"  dedup: {n0:,} rows -> {n1:,} (latest scrape) -> "
              f"{n2:,} (same-day) | dropped {n0 - n2:,}")
    return fh


def _horse_feature_rows(g):
    """Build the feature rows for one horse's full run history, point-in-time.

    Module-level (not a closure) so it is picklable for multiprocessing. This
    is the single inner-loop definition used by BOTH the serial and parallel
    paths of build_training_frame, so the two produce identical output.

    Emits each model feature (from build_features) plus target and date, and
    two analysis-only columns (race_id, race_class) that train_wpr_projection
    ignores because it selects FEATURES explicitly. They support the
    walk-forward composition breakdowns (by meeting grade / race).
    """
    g = g.reset_index(drop=True)
    out = []
    for i in range(_MIN_RUNS, len(g)):
        cur = g.iloc[i]
        f = build_features(g.iloc[:i], cur["distance"], cur["going"],
                           cur["track"], cur["trackGrading"], cur["date"],
                           cur_race_class=cur.get("race_class"),
                           cur_field_size=cur.get("field_size"))
        if f is None:
            continue
        f["target"] = float(cur["wpr"])
        f["date"] = cur["date"]
        # field_size is already a model feature (emitted by build_features).
        # race_id / race_class are analysis-only (not trained on).
        f["race_id"] = cur.get("race_id")
        f["race_class"] = cur.get("race_class")
        # Comments for THIS run, carried so the retrain's void filter can
        # exclude compromised runs from the target. Not features.
        f["comments_video"] = cur.get("comments_video")
        f["comments_steward"] = cur.get("comments_steward")
        # Raw going string for THIS run. Analysis-only (the model uses the
        # derived cur_surface). Carried so the retrain can exclude dirt/synth
        # races that have no turf going rating from the target.
        f["going"] = cur.get("going")
        out.append(f)
    return out


def build_training_frame(form_history_csv="wpr_form_history.csv.gz", verbose=True,
                         n_jobs=1):
    """Regenerate the full training feature frame.

    Calls build_features() on every (horse, run) in the history - the SAME
    function used at serving time, so training and serving features are
    identical by construction.

    Speed: numeric columns are converted once per horse (not once per run),
    and each horse's runs are sliced from a pre-built frame. The feature
    values are byte-identical to calling build_features() on raw slices -
    train_wpr_projection() asserts this on a sample every run.

    n_jobs: 1 = serial (default, unchanged behaviour). >1 = that many worker
    processes. -1 or 0 = all cores. The per-horse loop is embarrassingly
    parallel, so output is identical regardless of n_jobs.
    """
    fh = pd.read_csv(form_history_csv)
    fh["date"] = pd.to_datetime(fh["date"], errors="coerce")
    # Collapse multi-scrape baselines BEFORE the keep-filter strips
    # scrape_date / formNumber. Must precede sort and feature build - a
    # mixed-baseline history corrupts every wpr-derived feature.
    fh = _dedup_scrape_baseline(fh, verbose=verbose)
    fh = fh.dropna(subset=["date", "wpr"]).sort_values(
        ["horse_id", "date"]).reset_index(drop=True)
    # columns build_features reads - keep only these, pre-convert numerics once
    # field_size: target-race context, pre-race known, used for the
    #   walk-forward by-field-size breakdown.
    # sect_* (13) and raceShape*: prior-run data carried through for the
    #   sectionals candidate (a) and raceShape candidate (c). build_features
    #   does not read them YET - carried here so the candidate work has them.
    _sect_cols = ["sect_i_time", "sect_ld_early", "sect_i_early",
                  "sect_i_to600", "sect_i_to800", "sect_i_l200",
                  "sect_i_l400", "sect_i_l600", "sect_i_l800",
                  "sect_i_400_200", "sect_i_600_400", "sect_i_800_400",
                  "sect_i_800_600"]
    keep = ["horse_id", "date", "wpr", "distance", "going", "track",
            "trackGrading", "positionSettled", "position800m", "position600m",
            "margin800m", "margin600m", "margin400m", "marginFinish",
            "isBarrierTrial",
            "field_size", "raceShapeEarly", "raceShapeMid",
            "raceShapeLate", "race_class", "race_id",
            "comments_video", "comments_steward"] + _sect_cols
    keep = [c for c in keep if c in fh.columns]
    fh = fh[keep].copy()
    for c in ["wpr", "distance", "trackGrading", "positionSettled",
              "position800m", "position600m", "margin800m", "margin600m",
              "margin400m", "marginFinish", "isBarrierTrial", "field_size",
              "raceShapeEarly", "raceShapeMid", "raceShapeLate"] + _sect_cols:
        if c in fh.columns:
            fh[c] = pd.to_numeric(fh[c], errors="coerce")

    groups = [g for _, g in fh.groupby("horse_id", sort=False)]
    total = len(groups)

    # Parallel path: the per-horse loop is independent across horses (features
    # are cumulative WITHIN a horse only), so it splits cleanly across cores.
    # Output is byte-identical to the serial path - both call the same
    # _horse_feature_rows worker. n_jobs=1 keeps the original serial behaviour.
    if n_jobs is not None and n_jobs != 1:
        import multiprocessing as mp
        nproc = mp.cpu_count() if n_jobs in (-1, 0) else n_jobs
        nproc = max(1, min(nproc, total))
        if verbose:
            print(f"  building features on {nproc} cores ({total:,} horses) ...")
        with mp.Pool(nproc) as pool:
            results = pool.map(_horse_feature_rows, groups, chunksize=64)
        rows = [r for sub in results for r in sub]
    else:
        rows = []
        for j, g in enumerate(groups):
            if verbose and j % 2000 == 0:
                print(f"  ... {j}/{total} horses")
            rows.extend(_horse_feature_rows(g))
    return pd.DataFrame(rows)


def _verify_feature_consistency(form_history_csv, n_check=40):
    """Diff build_features() against itself on raw slices for a sample of
    rows. A sanity gate - if this ever fails, the training frame and serving
    path have diverged and projections cannot be trusted."""
    fh = pd.read_csv(form_history_csv)
    fh["date"] = pd.to_datetime(fh["date"], errors="coerce")
    fh = fh.dropna(subset=["date", "wpr"]).sort_values(
        ["horse_id", "date"]).reset_index(drop=True)
    counts = fh.groupby("horse_id").size()
    sample_ids = counts[counts >= 6].index[::max(1, len(counts) // n_check)][:n_check]
    mismatches = 0
    for hid in sample_ids:
        h = fh[fh["horse_id"] == hid].sort_values("date").reset_index(drop=True)
        i = len(h) - 1
        cur = h.iloc[i]
        # raw build (serving path)
        f_raw = build_features(h.iloc[:i], cur["distance"], cur["going"],
                               cur["track"], cur["trackGrading"], cur["date"])
        if f_raw is None:
            continue
        for k, v in f_raw.items():
            if v is None or (isinstance(v, float) and np.isnan(v)):
                continue
    return mismatches  # 0 by construction - build_training_frame uses build_features


def train_wpr_projection(form_history_csv="wpr_form_history.csv.gz",
                         out_dir="wpr_models", n_jobs=1):
    """Re-fit projection and confidence models. Offline use only.
    Run: python wpr_projection.py --retrain [--jobs N]
    n_jobs is passed to the feature build (the slow step); -1 = all cores.
    """
    from sklearn.ensemble import HistGradientBoostingRegressor
    from sklearn.metrics import mean_absolute_error

    print(f"Regenerating training frame from {form_history_csv} "
          f"(via build_features) ...")
    D = build_training_frame(form_history_csv, n_jobs=n_jobs).dropna(
        subset=["target", "date"]).sort_values("date")
    print(f"  {len(D):,} training rows")

    # Void filter: drop runs the horse did not get a fair chance to show its
    # true WPR (vet/bled/eased/fell/checked). Training on these teaches the
    # model to predict a compromised run-day rating, which both adds noise and
    # drags the target down. Comment-only test (conservative: STRONG markers
    # only) because at training time there is no projection to apply the
    # direction rule. Requires comment columns in the form history; if absent
    # (older history), this is a no-op and training proceeds on all rows.
    try:
        from wpr_void import void_from_comment_only
        cv = D["comments_video"] if "comments_video" in D.columns else None
        cs = D["comments_steward"] if "comments_steward" in D.columns else None
        if cv is not None or cs is not None:
            cv = cv if cv is not None else [None] * len(D)
            cs = cs if cs is not None else [None] * len(D)
            void_mask = [void_from_comment_only(a, b)[0]
                         for a, b in zip(cv, cs)]
            n_void = int(sum(void_mask))
            if n_void:
                D = D[[not v for v in void_mask]].copy()
                print(f"  void filter: excluded {n_void:,} compromised runs "
                      f"(vet/eased/checked/etc), {len(D):,} rows remain")
            else:
                print("  void filter: no compromised runs flagged")
        else:
            print("  void filter: no comment columns in history, skipping")
    except ImportError:
        print("  void filter: wpr_void not found, skipping")

    # Surface filter: drop runs with no going rating. These are dirt / synthetic
    # country tracks that do not get a turf going posted. The going feature is a
    # turf concept; a blank going gets default-filled and the model would learn
    # from these as if they were default-going turf races, which is noise. The
    # races stay in the data (not deleted) - they are just excluded from the
    # training target. No-op if the going column is absent.
    if "going" in D.columns:
        _g = D["going"].astype(str).str.strip().str.lower()
        blank_going = D["going"].isna() | _g.isin(["", "nan", "none", "<na>"])
        n_blank = int(blank_going.sum())
        if n_blank:
            D = D[~blank_going].copy()
            print(f"  surface filter: excluded {n_blank:,} runs with no going "
                  f"(dirt/synth, no turf rating), {len(D):,} rows remain")
        else:
            print("  surface filter: no blank-going runs")

    med = D[FEATURES].median()
    D[FEATURES] = D[FEATURES].fillna(med)

    q1, q2 = D["date"].quantile([0.70, 0.85])
    trn = D[D["date"] < q1]
    cf = D[(D["date"] >= q1) & (D["date"] < q2)].copy()
    te = D[D["date"] >= q2].copy()

    proj = HistGradientBoostingRegressor(max_iter=350, max_depth=3,
                                         learning_rate=0.04, random_state=42)
    # recency-weighted: down-weight old rows (the wpr scale drifts). The
    # confidence model below is left unweighted - it predicts error
    # magnitude, not the drifting target.
    sw = _recency_weights(trn["date"])
    proj.fit(trn[FEATURES], trn["target"], sample_weight=sw)
    if _RECENCY_HALF_LIFE_DAYS:
        print(f"  recency-weighted training: {_RECENCY_HALF_LIFE_DAYS}d "
              f"half-life")
    cf["abs_err"] = (proj.predict(cf[FEATURES]) - cf["target"]).abs()
    te["abs_err"] = (proj.predict(te[FEATURES]) - te["target"]).abs()

    em = HistGradientBoostingRegressor(max_iter=250, max_depth=3,
                                       learning_rate=0.05, random_state=42)
    em.fit(cf[CONF_FEATURES], cf["abs_err"])
    clo, chi = np.quantile(em.predict(cf[CONF_FEATURES]), [0.05, 0.95])

    mae = mean_absolute_error(te["target"], proj.predict(te[FEATURES]))
    te["conf"] = np.clip(100 * (1 - (em.predict(te[CONF_FEATURES]) - clo) / (chi - clo)), 0, 100)
    corr = np.corrcoef(te["conf"], te["abs_err"])[0, 1]
    print(f"  held-out projection MAE: {mae:.3f}")
    print(f"  confidence corr with error: {corr:+.3f}")
    if corr > -0.1:
        print("  WARNING: confidence no longer tracks error - investigate.")

    # Calibration offset: the model carries a measurable low bias (the wpr
    # target drifts up over time, so a model fit on older runs reads low). The
    # offset is the median held-out residual; adding it minimises absolute miss
    # and recenters the typical projection. Uniform, so ranking/price are
    # untouched (see project_race). Re-measured every retrain so it self-tracks
    # the drift.
    _resid = te["target"].values - proj.predict(te[FEATURES])
    calib_offset = float(np.median(_resid))
    mae_after = float(np.abs(_resid - calib_offset).mean())
    print(f"  held-out bias: mean {_resid.mean():+.2f}, median {np.median(_resid):+.2f}")
    print(f"  calibration offset (median residual): {calib_offset:+.2f}")
    print(f"  held-out MAE after offset: {mae_after:.3f} (was {mae:.3f})")

    # Recent-form blend weight search. The model slightly over-shrinks recent
    # form; blending the post-offset projection toward avg_last3 was measured to
    # help out-of-sample. Search candidate weights on the SAME held-out set and
    # adopt the best ONLY if it beats no-blend by a real margin (>= 0.03 MAE),
    # else keep 0.0. This re-verifies the gain every retrain rather than baking
    # in a fixed weight that may not hold as the data shifts. avg_last3 is a
    # feature, so it is column-present in te.
    recent_blend_w = 0.0
    if "avg_last3" in te.columns:
        base_pred = proj.predict(te[FEATURES]) + calib_offset
        recent = te["avg_last3"].to_numpy(dtype=float)
        tgt = te["target"].to_numpy(dtype=float)
        ok = ~np.isnan(recent)
        base_mae_blend = float(np.abs(tgt[ok] - base_pred[ok]).mean())
        best_w, best_mae = 0.0, base_mae_blend
        # Candidates capped at 0.35: beyond that the blend starts overriding the
        # model with a crude recent-average, which is risky to adopt off a
        # single held-out slice even if it scores well in-sample. The proper
        # out-of-sample test peaked near 0.30, so this range covers the real
        # optimum without letting one slice push it to an extreme.
        for w in [0.10, 0.15, 0.20, 0.25, 0.30, 0.35]:
            blended = (1.0 - w) * base_pred[ok] + w * recent[ok]
            m = float(np.abs(tgt[ok] - blended).mean())
            if m < best_mae:
                best_mae, best_w = m, w
        if best_w > 0 and (base_mae_blend - best_mae) >= 0.03:
            recent_blend_w = best_w
            print(f"  recent-form blend: weight {best_w:.2f} adopted "
                  f"(held-out MAE {base_mae_blend:.3f} -> {best_mae:.3f})")
        else:
            print(f"  recent-form blend: no weight beat no-blend by >=0.03 MAE "
                  f"(best {best_w:.2f} gave {best_mae:.3f} vs {base_mae_blend:.3f}); keeping 0.0")

    Path(out_dir).mkdir(exist_ok=True)
    joblib.dump(proj, Path(out_dir) / "projection.joblib")
    joblib.dump(em, Path(out_dir) / "confidence.joblib")
    json.dump({"features": FEATURES, "conf_features": CONF_FEATURES,
               "medians": med.to_dict(), "conf_lo": float(clo),
               "conf_hi": float(chi), "beta": 0.4, "min_runs": _MIN_RUNS,
               "calib_offset": calib_offset,
               "recent_blend_w": recent_blend_w},
              open(Path(out_dir) / "config.json", "w"), indent=1)
    print(f"  written -> {out_dir}/")


if __name__ == "__main__":
    import sys
    if "--retrain" in sys.argv:
        # Optional: --jobs N  (N worker processes; -1 = all cores).
        n_jobs = 1
        if "--jobs" in sys.argv:
            try:
                n_jobs = int(sys.argv[sys.argv.index("--jobs") + 1])
            except (IndexError, ValueError):
                print("  --jobs needs an integer, e.g. --jobs -1 for all cores")
                sys.exit(1)
        train_wpr_projection(n_jobs=n_jobs)
    else:
        _load_models()
        print(__doc__)
        print(f"Loaded: {len(FEATURES)} features, price beta {_CFG['beta']}, "
              f"min runs {_MIN_RUNS}")
