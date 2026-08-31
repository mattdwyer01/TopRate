"""
wpr_projection.py - WPR projection

Projects a horse's run-day WPR from its form history, attaches a 0-100
confidence rating, a field-normalised WPR price, and a plain-language
explanation of why the rating is what it is.

WHAT THIS IS
  A WPR projection built from wpr_form_history.csv - the per-run form
  history scraped daily. It predicts the run-day WPR a horse will record.

  ADDITIVE ARCHITECTURE (Aug 2026 rebuild #2, replacing the pure
  gradient-boosting model): projection = BASE + ADJUSTMENT. (A uniform
  calib_offset term used to be added here too - a data-derived shift that
  recentered projections onto the current WPR scale and measurably improved
  held-out MAE (5.836 -> 5.775). Removed at the user's explicit instruction
  (Aug 2026): it read as an unexplained constant fudge applied to every
  runner, which cost trust in the model even though it was a real, measured
  correction. See git history for the numbers if this is ever revisited.)
  BASE is the horse's own anchor: an _BASE_BLEND_ALPHA-weighted blend of
  wpr_nett (TopRate's own pre-race rating) and ewm3 (this horse's own
  recency-weighted average of its last ~3 runs) when both are available,
  falling back to whichever half is available, then avg_last3/career_avg;
  see _compute_base for the exact order. The blend weight was a flat 50/50
  until Aug 2026, when it was shifted to a data-derived 0.80 after finding
  the ratio itself had drifted with real data (wpr_nett steadily getting
  more predictive over the past ~18 months) rather than needing to vary by
  race condition (first-up, spell length, own consistency were all tested
  and didn't hold up independently of that drift) - then reverted back to a
  flat 50/50 shortly after at the user's explicit instruction, despite the
  0.80 shift's documented improvement - see _BASE_BLEND_ALPHA's docstring
  for both the drift analysis and the reversion rationale. (A brief Aug
  2026 period removed wpr_nett from base entirely for zero dependence on
  TopRate's own unaudited rating - reverted at the user's explicit
  instruction after it cost a real, measured ~0.56 held-out MAE; see git
  history for both sets of numbers.)
  ADJUSTMENT (rebuilt again, later Aug 2026, at the user's request
  for something simpler and more transparent than a fitted regression) is
  sum(ADJ_TERMS) - a handful of "+/- vs this horse's own career average at
  this condition" deltas (distance, going, first/second-up, lightly-raced
  trend, long-spell history), each computed purely from THAT horse's own
  prior runs and shrunk by sample size (see build_features' SIMPLE
  ADJUSTMENT MODEL block, _shrink()). No fitting, no population-level
  coefficients - what a UI shows in the breakdown IS the whole adjustment.
  This replaced an earlier Ridge regression on 15 population-level
  situational features (freshness, track/surface conditions, field size,
  recent form shape, MAE 5.150 held-out) - preserved in git history along
  with the numbers, for anyone revisiting the trade-off this simpler
  design makes (see ADJ_TERMS for what that trade-off costs structurally).

  WHY THE ADDITIVE SPLIT (BASE + ADJUSTMENT) AT ALL: a population-level
  gradient-boosting model, however well tuned, structurally regresses rare
  high-WPR horses toward the dense middle of the training population
  (held-out bias-by-actual-WPR-band was a clean, monotonic +0.85 at 70-80
  up to +8.7-9.1 at 100-105, confirmed irreducible by more sample weight or
  more tree capacity - both were tested and neither closed the gap).
  Anchoring on the horse's own current base rating sidesteps that failure
  mode entirely: it does not predict an absolute number from a shared
  population model, it predicts a small adjustment to a number that is
  already correct for that horse.

  Three artifacts in wpr_models/:
    projection.joblib  - vestigial empty dict (used to hold the fitted
      Ridge adjustment model; ADJ_TERMS needs no artifact, it's computed
      directly in build_features every time). Kept as an empty file so
      this directory's shape doesn't need to change.
    confidence.joblib  - {"lo": LightGBM q10, "hi": LightGBM q90} on the
      FULL feature set, unaffected by either adjustment rebuild above -
      interval width is still the confidence signal (see project_race).
    config.json         - the full feature list + median-fill table (for
      the confidence models), ADJ_TERMS names, price beta, min runs

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

try:
    from wpr_void import void_from_comment_only as _void_from_comment_only
except ImportError:
    _void_from_comment_only = None

try:
    # Reuse settling_estimate.py's barrier_nudge exactly rather than a
    # second copy that could drift - see own_settle below (build_features)
    # for why the SAME today's-predicted-settle-band formula matters here.
    from settling_estimate import barrier_nudge as _settle_barrier_nudge
except ImportError:
    _settle_barrier_nudge = None

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


# Elite-tier training rows (actual WPR >= 80) are a small, thinning tail -
# well under 1% of rows are 100+. An unweighted model naturally prioritises
# fitting the dense bulk of the population, which under-resolves the top
# end: held-out bias-by-actual-WPR-band (Aug 2026 investigation, triggered
# by a real horse - Autumn Glow, consistently 103-107.5 - projecting at
# 93-100) showed a clean, monotonic pattern: +0.85 at 70-80, +2.6 at 80-90,
# +3.7 at 90-95, +4.8 at 95-100, +8.7 at 100-105. A post-hoc recalibration
# (isotonic regression on the raw prediction) does NOT fix this - tested and
# made it WORSE (5.376 -> 5.568 MAE, bias unchanged) because the raw
# predictions themselves do not separate elite horses from sub-elite ones;
# no 1-D remapping can recover information the model never resolved.
# Upweighting rare high-target rows during training does fix it (this is
# the standard rare-value regression technique): held-out bias-by-band
# dropped to +2.1/+2.6/+3.7/+6.1 for the same bands, at a small aggregate
# cost (5.371 -> 5.399 MAE - every average-tier horse gives up a sliver of
# accuracy so the model resolves the tail). Weights beyond this were tested
# (15x/8x/5x/2x, 30x/15x/8x/3x) and did NOT improve the tail further - this
# is the ceiling a reweighting alone can reach; the rest is a model-capacity
# limit (max_depth=3, num_leaves=8), not a weighting problem.
_RARITY_BANDS = [(100.0, 8.0), (95.0, 5.0), (90.0, 3.0), (80.0, 1.5)]


def _rarity_weights(target):
    """Multiplier by actual target WPR, upweighting the rare high-WPR tail.
    Multiply into the recency weight (elementwise), never replace it - both
    corrections are needed for different reasons."""
    t = pd.to_numeric(target, errors="coerce").to_numpy()
    w = np.ones(len(t))
    # Apply lowest threshold first, highest last, so a row above several
    # thresholds ends up with the HIGHEST tier's multiplier (each later
    # pass overwrites only the rows that also clear its own, higher bar).
    for threshold, mult in sorted(_RARITY_BANDS):
        w = np.where(t >= threshold, mult, w)
    return w


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
    # --- wpr_nett: TopRate's own automated pre-race base rating. Feeds
    # BASE directly again (see _compute_base - a _BASE_BLEND_ALPHA-weighted
    # blend with ewm3, re-adopted Aug 2026 after a brief period without it),
    # and is also
    # an input to the confidence (q10/q90 interval width) models, a
    # separate architecture. See build_features' cur_wpr_nett docstring
    # for the leak-check (frozen at first capture per run_id).
    "wpr_nett",
]

# ADJ_TERMS: the adjustment, in full. Replaced the earlier Ridge-on-
# ADJ_FEATURES design (Aug 2026, population-level coefficients fit across
# every horse) at the user's explicit request for something simpler and
# more transparent - adjustment = sum(ADJ_TERMS), each term a shrunk +/-
# vs THIS horse's own career average computed from ITS OWN history only
# (see the SIMPLE ADJUSTMENT MODEL block in build_features and _shrink()
# above). No fitting, no coefficients - what you see in the breakdown IS
# the whole adjustment, by construction.
#
# This gives up whatever real signal the old population-level terms were
# carrying that a per-horse lookup structurally can't represent (today_wet,
# cur_surface, field_size - the same value for every runner in a race, so
# there's no "this horse's own history" version of them) for something the
# user can read and trust at a glance. The old Ridge design, its measured
# numbers, and prior negative results (barrier, going_delta as a flat
# effect, first/second_up as Ridge interaction terms) are preserved in git
# history and in this file's earlier revisions - worth revisiting if this
# simpler design's own numbers disappoint enough to reconsider the trade.
ADJ_TERMS = [
    "own_distance", "own_going", "own_first_up", "own_second_up",
    "own_trend", "own_long_spell", "track_barrier", "closing_merit",
]

# Serving-time calibration (Aug 2026): a review of projected_wpr vs the real
# post-race wpr_actual (~37k clean, void-excluded runs, once the
# update_results() backlog fix landed ~20k fresh results) found raw
# projections systematically too extreme. Two versions were tried, both fit
# on the first half of the data and evaluated purely out-of-sample on the
# second before being trusted:
#   1. A single blended slope on the whole projection (actual = a +
#      b*projected, b=0.8355) - cut held-out MAE ~2%.
#   2. DECOMPOSED base vs adjustment (this one, shipped): fitting
#      actual = a + b_base*base + b_adj*adjustment separately found the
#      adjustment term explains real outcomes MUCH more weakly than the
#      base (b_adj=0.1791 vs b_base=0.8807) - a raw adjustment of, say,
#      +3 should really only move the projection by about +0.54. Blending
#      base and adjustment into one slope (version 1) mostly corrected the
#      base, since base values dwarf adjustment values in magnitude, and
#      barely touched the real problem. Decomposing cut held-out MAE
#      4.88% - more than double version 1's gain. An asymmetric version
#      (separate slopes for positive vs negative adjustments) was also
#      tested and did NOT help further (4.86%, a wash) - the earlier-
#      looking pos/neg asymmetry was mostly base characteristics
#      correlating with adjustment sign, not a real direction effect, so
#      the fix is a uniform adjustment shrink, not an asymmetric cap.
#
# Applied here (not as a separate post-processing step) so it's the single
# source of truth every caller of _compute_base()/project_race() shares -
# describe()'s narration recomputes base_val independently and must match
# the base_wpr shown elsewhere in the UI exactly (see its own docstring).
# The intercept is folded entirely into the base (the anchor); the
# adjustment slope is applied to the adjustment total in project_race() -
# together they reproduce a + b_base*base + b_adj*adj = the fitted
# calibration exactly, so base_wpr + adjustment == projected_wpr still
# holds (an invariant the frontend relies on - see types/domain.ts).
#
# Deliberately NOT applied inside build_training_frame()'s own independent
# reimplementation of this same base formula (see "_base" there) - that
# path fits/evaluates the RAW model against real targets; calibration is a
# serving-time correction on top of it, not part of what gets trained.
# _CALIB_INTERCEPT/_CALIB_BASE_SLOPE are the MID-segment base calibration -
# re-fit together with _BASE_BLEND_ALPHA and the low/high segments below
# (see that block's docstring). _CALIB_ADJ_SLOPE is independent of the base
# blend entirely (calibrates the ADJUSTMENT sum, not the base anchor) and
# is untouched by the alpha revert.
_CALIB_INTERCEPT = 2.084
_CALIB_BASE_SLOPE = 0.9544
_CALIB_ADJ_SLOPE = 0.1791

# The blend weight was raised to 0.80 in Aug 2026 after finding a real,
# validated time-drift in how predictive wpr_nett is relative to ewm3 (see
# git history, commit "Shift base blend from a flat 50/50 to a data-derived
# 80/20" for the full analysis: quarter-by-quarter optimal alpha climbing
# 0.25->1.00 over ~18 months, held up under two independent forward-only
# validations, real held-out MAE improvement both directions when 0.80 was
# compared against 0.50 on a chronological half-split). Reverted back to a
# flat 50/50 at the user's explicit instruction (Aug 2026), despite that
# documented improvement - re-checked at the time of reverting: refitting
# the SAME validation on current data confirmed 50/50 still trails 0.80 in
# the H1-fit/H2-validate direction (calibrated MAE 5.706 vs the raw
# uncalibrated blend's 5.714 - barely better than doing nothing) and is
# outright worse than uncalibrated in the H2-fit/H1-validate direction
# (6.283 vs 5.868) - the older data (H1) behaves differently enough from
# recent data that a calibration fit on it doesn't generalise well, which
# is consistent with the original alpha-drift finding, not a contradiction
# of it. This is a deliberate override of that evidence, not a finding that
# 50/50 is actually better - if revisiting this, the alpha-drift analysis
# above still applies.
_BASE_BLEND_ALPHA = 0.50

# Base calibration is piecewise, not one global slope (Aug 2026, found while
# investigating a user-flagged case - a horse with strong, consistent recent
# form projected well below its actual result). A single slope fit across
# the whole population is a compromise: split by raw base value (the
# _BASE_BLEND_ALPHA-weighted nett/ewm3 blend, pre-calibration) into
# low/mid/high segments on real outcomes (H1 fit, H2 held-out, both
# directions checked) showed the true slope is NOT constant - low raw-base
# horses need heavier shrinkage (noisier/less reliable form) while high
# raw-base horses need almost none (an established level is real, not
# noise). A 3-segment piecewise fit (bottom 10% / middle 70% / top 20%,
# breakpoints and slopes fit on the full void-excluded resulted set) fixes
# the "strong horse projected too low" failure mode without moving the
# middle segment's own shape. Re-derived together with _BASE_BLEND_ALPHA
# above (changing the blend changes the raw base's whole distribution, so
# the breakpoints/slopes below are NOT independent of that choice - re-fit
# both together, never one without the other). Re-fit for the Aug 2026
# 0.80->0.50 revert using the same methodology (full-data fit, p10/p80
# breakpoints of THIS alpha's own raw-base distribution, not the old
# breakpoint values, since the distribution itself shifts with alpha).
_CALIB_LOW_BREAK = 64.25   # raw base <= this: low-segment slope
_CALIB_HIGH_BREAK = 81.96  # raw base > this: high-segment slope
_CALIB_LOW_INTERCEPT = -0.950
_CALIB_LOW_SLOPE = 0.9968
_CALIB_HIGH_INTERCEPT = 1.076
_CALIB_HIGH_SLOPE = 0.9679


def _calibrate_base(raw):
    """raw base (pre-calibration _BASE_BLEND_ALPHA-weighted nett/ewm3 blend,
    or a single-source fallback) -> calibrated base. See the piecewise-
    calibration note above _CALIB_LOW_BREAK for why this isn't one slope."""
    if raw <= _CALIB_LOW_BREAK:
        return _CALIB_LOW_INTERCEPT + _CALIB_LOW_SLOPE * raw
    if raw > _CALIB_HIGH_BREAK:
        return _CALIB_HIGH_INTERCEPT + _CALIB_HIGH_SLOPE * raw
    return _CALIB_INTERCEPT + _CALIB_BASE_SLOPE * raw


def _compute_base(feat):
    """The horse's own anchor for the additive model: an
    _BASE_BLEND_ALPHA-weighted blend of wpr_nett (TopRate's own pre-race
    rating) and ewm3 (this horse's own recency-weighted average of its last
    ~3 runs) when both are available. Was shifted from a flat 50/50 to a
    data-derived 0.80 in Aug 2026 after finding a real, validated time-drift
    (see _BASE_BLEND_ALPHA's docstring), then reverted back to a flat 50/50
    shortly after at the user's explicit instruction, despite that
    documented improvement - see _BASE_BLEND_ALPHA's docstring for the
    reversion rationale. wpr_nett is never
    dropped from base entirely - a brief Aug 2026 period that removed it
    cost a real, measured ~0.56 held-out MAE (5.769 -> 6.333) for zero
    dependence on TopRate's own unaudited rating, reverted at the user's
    explicit instruction. Falls back to whichever half is available, then
    down ewm3/avg_last3/career_avg, when one or both are unrated. Note this
    uses ewm3 specifically, not the ewm5-once->3-starts switch that briefly
    replaced it - that switch was introduced alongside the wpr_nett removal
    and is reverted together with it here.

    Returns the CALIBRATED base (see _CALIB_BASE_SLOPE/_CALIB_INTERCEPT
    above) - every caller wants the calibrated anchor, not the raw blend."""
    def _ok(v):
        return v is not None and not (isinstance(v, float) and v != v)

    nett = feat.get("wpr_nett")
    ewm3 = feat.get("ewm3")
    if _ok(nett) and _ok(ewm3):
        raw = _BASE_BLEND_ALPHA * float(nett) + (1 - _BASE_BLEND_ALPHA) * float(ewm3)
        return _calibrate_base(raw)
    for key in ("wpr_nett", "ewm3", "avg_last3", "career_avg"):
        v = feat.get(key)
        if _ok(v):
            return _calibrate_base(float(v))
    return None


def _adj_term_frame(feat_dicts):
    """List of feature dicts -> DataFrame of ADJ_TERMS (already computed
    per-horse in build_features, 0.0 when a term doesn't apply/has no own
    history - no median-filling needed, unlike the old Ridge design,
    since 0.0 already IS the correct "no signal" value here)."""
    rows = [{c: (0.0 if f is None else f.get(c, 0.0)) for c in ADJ_TERMS}
            for f in feat_dicts]
    return pd.DataFrame(rows, columns=ADJ_TERMS)


_PROJ = None
_CONF = None
_CFG = None


def _load_models():
    """Load the model artifacts once. Raises if wpr_models/ is missing.

    projection.joblib is now a vestigial empty dict - the ADJUSTMENT term
    used to be a fitted Ridge model here, replaced by the ADJ_TERMS sum
    (see module docstring / project_race). Kept as an empty artifact
    rather than removing the file so wpr_models/'s three-file shape (and
    this function's existence check) doesn't need to change.
    confidence.joblib is a dict {"lo": q10 model, "hi": q90 model}, on the
    FULL feature set - unaffected by the ADJUSTMENT rework above (a
    separate architecture entirely). Their predicted interval width is
    the confidence signal (see project_race).
    """
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


# Wet/Dry split for own_wet/own_dry (user-specified boundary, Aug 2026) -
# a different cut to _going_is_wet's tg>=5 above (left untouched; it feeds
# today_wet/going_delta, already-tested existing features). Wet = Soft 6
# and above (tg>=6), Dry = Soft 5 and firmer (tg<=5) - the boundary
# horsemen actually talk about, not the same as own_going's Firm/Good/
# Soft/Heavy string band (which lumps every Soft grading together and
# never separates soft5 from soft6).
def _wet_dry_band(track_grading):
    try:
        tg = float(track_grading)
    except (TypeError, ValueError):
        return None
    if tg != tg:
        return None
    return "Wet" if tg >= 6 else "Dry"


# Band for own_settle (see build_features). Same thresholds as
# settling_estimate.py's _band and toprate_daily.py's settling-band
# lookup (_band_of) - three small local copies of the same simple
# banding rule already exist across the codebase (this file, the
# settling estimate script, the frontend's lib/pace.ts settleBand), so
# a fourth here matches existing precedent rather than adding a new
# cross-module dependency for six lines of arithmetic.
def _settle_band(rel):
    if rel is None or rel != rel:  # NaN
        return None
    if rel <= 0.20:
        return "Leader"
    if rel <= 0.45:
        return "On-pace"
    if rel <= 0.70:
        return "Midfield"
    return "Back"


# own_pace ingredient: how did THIS horse's own early sectional shape
# compare to its own late sectional in a given prior run - Fast/Even/Slow.
# Exact same formula as toprate_daily.py's _tmp (the field the frontend's
# FormHistoryEntry.tempo carries) so a run banded "Fast" here means the
# same thing it already means everywhere else in the app - not a new,
# fourth definition of tempo. This describes how the HORSE raced within
# whatever shape its race had, which is a different (related but not
# identical) question to race_speed_estimate.py's race-WIDE early-tempo
# prediction used as cur_race_speed_label below - own_pace asks whether
# this horse personally goes well when ITS OWN sectional profile has
# looked like today's predicted race shape, using the model's own
# leak-safe pre-race prediction for today (never the actual post-race
# shape, which the model cannot know before the race is run).
def _own_tempo_band(early, l600):
    try:
        e, l = float(early), float(l600)
    except (TypeError, ValueError):
        return None
    if e != e or l != l:
        return None
    diff = e - l
    if diff >= 2:
        return "Fast"
    if diff <= -2:
        return "Slow"
    return "Even"


# Surface type from the going string. trackGrading cannot distinguish a
# grading-3 synthetic from a grading-3 good turf, so surface is its own
# signal. 0 turf, 1 synthetic, 2 dirt, 3 sand.
_SURFACE_MAP = {"synthetic": 1, "dirt": 2, "sand": 3}


def _going_surface(going):
    g = str(going).strip().lower()
    return _SURFACE_MAP.get(g, 0)


# Firm/Good/Soft/Heavy band from the going STRING - matches the frontend's
# lib/pace.ts goingBand() exactly (same 4 buckets, same startswith rule) so
# a horse's own-condition delta here means the same thing as what the
# runner detail modal already shows for career/condition stats.
def _going_band(going):
    g = str(going).strip().lower()
    if g.startswith("firm"):
        return "Firm"
    if g.startswith("good"):
        return "Good"
    if g.startswith("soft"):
        return "Soft"
    if g.startswith("heavy"):
        return "Heavy"
    return None


# Relative barrier band for own-history matching: barrier / field_size,
# not the raw stall number, so barrier 8 in an 18-horse field (mid) and
# barrier 8 in a 9-horse field (wide) are correctly treated as different
# draws. A flat population-level barrier feature already failed a test
# (Aug 2026 feature search) - this is a different question (does THIS
# horse personally go better or worse from a given relative draw), tried
# per the same reasoning as own_going/own_distance.
def _barrier_band(barrier, field_size):
    try:
        b = float(barrier)
        fs = float(field_size)
    except (TypeError, ValueError):
        return None
    if b != b or fs != fs or fs <= 0:
        return None
    rel = b / fs
    if rel <= 1 / 3:
        return "Inside"
    if rel <= 2 / 3:
        return "Mid"
    return "Wide"


# track_barrier: the one ADJ_TERMS entry that is NOT a per-horse own-history
# lookup - every other term above/below needs no fitting at all (each is
# just "this horse's own past runs at this condition"). This one is
# population-level: does barrier draw matter more at SOME tracks/distances
# than others, aggregated across every horse that has raced there. Tested
# Aug 2026 (user request) as a shrunk (track, 200m distance band) ->
# per-barrier-band residual-WPR lookup, residual = target - career_avg
# (quality-normalised, so it isn't just re-learning "this is a good/bad
# horse"), shrunk toward the pooled global mean for that barrier band with
# strength _TRACK_BARRIER_K, then centered per (track, dist_band) group so
# it can never become a flat track-quality bias (a wide-draw specialist
# track should shift Inside down and Wide up, not just shift everything
# up). Robustness-tested across K=30-1200 before adoption: held-out MAE
# improved at every K from 75 up (best -0.0094 at K=300), only K=30 (barely
# shrunk) was worse - see git history for the full sweep. The lookup itself
# is FIT in train_wpr_projection() (population statistics need a training
# pass, unlike every other term here) and shipped in config.json; this
# constant and the two helpers below are shared between that fit and the
# live per-runner lookup in project_race() so the two can never drift.
_TRACK_BARRIER_K = 300.0


def _dist_band(distance):
    """200m distance band, e.g. 1200-1399m -> 1200. None if unusable."""
    try:
        d = float(distance)
    except (TypeError, ValueError):
        return None
    if d != d:
        return None
    return int(d // 200 * 200)


def _track_barrier_term(cur_track, cur_distance, cur_barrier, cur_field_size, lookup):
    """Live per-runner lookup against the FITTED track_barrier table (see
    above). 0.0 (no adjustment) for any track/distance-band combo not seen
    in training - same "unseen -> 0" contract the robustness backtest was
    actually validated under, not a fallback to some other average."""
    if not cur_track or lookup is None:
        return 0.0
    db = _dist_band(cur_distance)
    band = _barrier_band(cur_barrier, cur_field_size)
    if db is None or band is None:
        return 0.0
    return float(lookup.get(f"{cur_track}|{db}", {}).get(band, 0.0))


# closing_merit: a second population+own-history hybrid ADJ_TERM (Aug 2026,
# strike-rate validation - see wpr_closing_merit_strike_eval.py), motivated
# by the Sectional Time Ratings doc's "flashing lights" warning: a horse's
# raw closing-sectional strength is misleading without race context (it
# looks fast closing on a race the leaders let die, not because it ran home
# genuinely well). The population half is "expected sect_i_l600 given how
# THAT run's race actually unfolded" (raceShapeEarly, bucketed by
# _CLOSING_MERIT_BINS) - fit once, in train_wpr_projection(), on trn only,
# from the RAW form history directly (not the per-horse training frame -
# this is a population fact about how races run, independent of any one
# horse's own history) and shipped in config.json as pace_baseline_lookup.
# The own-history half (which run's residual to average) DOES need
# prior_runs, so it is computed inside build_features() itself, same as
# every other own_* term - see the "closing_pairs" ingredient there. The
# two halves are combined post-hoc by _closing_merit_term below, called
# both at serve time (project_race, using the loaded lookup) and at
# train_wpr_projection()'s own cf/te scoring step (using the freshly-fit
# lookup) - same split as track_barrier's own two-stage pattern above,
# just with the own-history half needing prior_runs instead of being pure
# population. Validated (strike-rate rose in BOTH chronological
# half-split directions, held-out MAE worse in both - a real, adopted
# strike-rate/MAE tradeoff, same as gear_change; see git history).
_CLOSING_MERIT_BINS = [-999, -7, -5, -3, -1, 1, 3, 5, 7, 999]


def _closing_merit_bucket(v):
    """Bucket a raceShapeEarly value into _CLOSING_MERIT_BINS, string-keyed
    to match pandas' own str(Interval) format for INTEGER bins exactly
    (verified: "(-7, -5]", no decimal point) - the same key format used by
    both the population fit (pd.cut in _fit_pace_baseline) and this
    manual, per-call version (avoids pd.cut's per-call overhead when
    called up to 3x per horse across a full retrain). None if v is
    missing or outside the binned range."""
    try:
        v = float(v)
    except (TypeError, ValueError):
        return None
    if v != v or v <= _CLOSING_MERIT_BINS[0] or v > _CLOSING_MERIT_BINS[-1]:
        return None
    for lo, hi in zip(_CLOSING_MERIT_BINS[:-1], _CLOSING_MERIT_BINS[1:]):
        if v <= hi:
            return f"({lo}, {hi}]"
    return None


def _closing_merit_term(pairs, lookup):
    """Combine the own-history half (pairs: a list of up to 3
    (sect_i_l600, bucket_str) tuples from this horse's own last prior
    runs - see build_features' "closing_pairs") with the FITTED
    population lookup (bucket_str -> expected sect_i_l600, see
    _fit_pace_baseline) into one shrunk residual, same _shrink convention
    as every other own_* term. 0.0 if either half is unavailable."""
    if not pairs or not lookup:
        return 0.0
    residuals = []
    for sect, bucket in pairs:
        if bucket is None:
            continue
        expected = lookup.get(bucket)
        if expected is None or sect is None or sect != sect:
            continue
        residuals.append(float(sect) - float(expected))
    if not residuals:
        return 0.0
    return _shrink(float(np.mean(residuals)), len(residuals))


def _fit_pace_baseline(form_history_csv, cutoff_date):
    """Population mean sect_i_l600 per _CLOSING_MERIT_BINS bucket, fit on
    RAW form history rows strictly before cutoff_date only (leak-safe,
    same trn-only convention as track_barrier's own fit). Reads the raw
    CSV directly (not the per-horse training frame D) since this is a
    population fact about race shape vs sectional time, independent of
    any one horse's own history - see wpr_closing_merit_strike_eval.py's
    fit_pace_baseline for the methodology this replicates."""
    fh = pd.read_csv(form_history_csv, low_memory=False)
    fh["date"] = pd.to_datetime(fh["date"], errors="coerce")
    fh = _dedup_scrape_baseline(fh, verbose=False)
    fh = fh[(fh.get("isBarrierTrial") != True) & (fh.get("is_jumpout") != True)]
    fh = fh[fh["date"] < pd.to_datetime(cutoff_date)]
    sect = pd.to_numeric(fh.get("sect_i_l600"), errors="coerce")
    early = pd.to_numeric(fh.get("raceShapeEarly"), errors="coerce")
    d = pd.DataFrame({"sect": sect, "early": early}).dropna()
    d["bucket"] = d["early"].apply(_closing_merit_bucket)
    d = d.dropna(subset=["bucket"])
    return {k: float(v) for k, v in d.groupby("bucket")["sect"].mean().items()}


# Shrinkage for the own-history adjustment deltas below: a delta computed
# from 1-2 of a horse's own runs is mostly noise dressed up as a personal
# signal - the same small-sample trap CareerStats' vsBase colouring and
# ComparisonGrid's MIN_RUNS_TO_COMPARE guard against on the frontend, just
# applied here as a continuous discount instead of an on/off threshold so
# a horse with, say, 2 matching runs still gets a (heavily discounted)
# personalised nudge rather than either the full raw delta or nothing.
# n / (n + K): 0 at n=0, 0.25 at n=K, approaches 1 as n grows.
_OWN_DELTA_SHRINK_K = 3.0

# Cap on each individual term's contribution, applied after shrinkage. With
# enough matching history (large n) a term passes shrink almost unshrunk,
# and real data has produced swings up to +/-45 (own_trend) - a lot of a
# single dimension for one term to move the projection.
_OWN_DELTA_CAP = 3.0

# Cap on the SUM of all ADJ_TERMS for one runner, applied in
# _cap_adj_sum() below. A horse could hit the per-term cap on several
# terms at once (e.g. a lightly-raced horse that's both improving fast AND
# first-up), stacking to a much bigger swing than any one term alone
# should justify. When the raw sum exceeds this, every nonzero term for
# that runner is scaled down by the same factor so they still sum to
# exactly +/-_OWN_DELTA_TOTAL_CAP - proportions between terms are
# preserved, so the breakdown panel still adds up to the total shown.
_OWN_DELTA_TOTAL_CAP = 6.0


def _shrink(delta, n):
    if n <= 0:
        return 0.0
    shrunk = float(delta) * n / (n + _OWN_DELTA_SHRINK_K)
    return max(-_OWN_DELTA_CAP, min(_OWN_DELTA_CAP, shrunk))


def _cap_adj_sum(term_values):
    """term_values: (n_rows, n_terms) array of already per-term-capped
    ADJ_TERMS values. Rescales any row whose absolute sum exceeds
    _OWN_DELTA_TOTAL_CAP so it sums to exactly that cap, preserving each
    term's relative share. Rows within the cap are returned unchanged."""
    term_values = np.asarray(term_values, dtype=float)
    row_sum = term_values.sum(axis=1)
    scale = np.ones(len(row_sum))
    over = np.abs(row_sum) > _OWN_DELTA_TOTAL_CAP
    nonzero_over = over & (row_sum != 0)
    scale[nonzero_over] = _OWN_DELTA_TOTAL_CAP / np.abs(row_sum[nonzero_over])
    return term_values * scale[:, None]


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
                   cur_field_size=None, cur_wpr_nett=None, cur_barrier=None,
                   cur_race_speed_label=None):
    """Build the feature dict for one horse.

    prior_runs: DataFrame of the horse's PAST runs only, any order. Needs
      columns: date, wpr, distance, going, track, trackGrading,
      positionSettled, position800m, position600m, marginFinish,
      isBarrierTrial, barrier, field_size. race_class is used if present
      (for class_move).
    cur_*: conditions of the race being projected.
    cur_race_class: the projected race's class string (BM64, CLS3, OPEN
      ...). Defaults to None - callers that do not pass it get a neutral
      class_move and is_jumps 0 (backward compatible).
    cur_race_speed_label: today's PREDICTED race-wide early tempo (Hot/
      Fast/Even/Slow, from race_speed_estimate.py's trained model - the
      SAME leak-safe pre-race estimate the dashboard already shows,
      never the actual post-race shape). Feeds own_pace (see
      _own_tempo_band). Defaults to None - own_pace is then 0.0.
    cur_barrier: this runner's barrier (stall number) for the race being
      projected. Combined with cur_field_size to bucket a RELATIVE draw
      (Inside/Mid/Wide, see _barrier_band) for own_barrier. Defaults to
      None - own_barrier is then 0.0 (no signal, not a leak risk).
    cur_field_size: number of runners in the projected race. Pre-race
      known, leak-free. The model under-projects small fields and slightly
      over-projects large ones (a bias gradient: -1.8 WPR at <=7 runners,
      +0.4 at 14+); field_size lets the model correct it. Defaults to None
      (filled with the training median at serving if absent).
    cur_wpr_nett: TopRate's own automated pre-race base rating for this
      run (Base + Adj from get_user_cache_race, captured at the SAME
      pre-race fetch as everything else - not a leak, verified against a
      held-out split where it improved MAE even MORE on genuinely
      pre-race-fetched rows than on backfilled ones). By far the single
      largest accuracy gain found in the Aug 2026 feature search (held-out
      MAE 5.75 -> 5.14). Defaults to None (filled with the training
      median at serving if absent, e.g. a race TopRate has not rated).
    race_date: date of the race being projected (required - used for
      days_since; pass the real race date, never a guess).

    Returns the feature dict, or None if fewer than _MIN_RUNS prior runs.
    """
    p = prior_runs
    if p is not None:
        # Barrier trials (and any other unrated row) carry no wpr - they are
        # not a "prior run" in the modelling sense and must not stand in for
        # one. Until the Aug 2026 capture-depth fix, isBarrierTrial was
        # always False in the captured history (trials simply weren't being
        # captured as rows at all), so nothing downstream ever needed to
        # filter them out. Now
        # that trials ARE captured with real dates, an unfiltered trial row
        # can become dates.iloc[-1] below - corrupting days_since/first_up
        # for exactly the freshening-up-for-a-comeback horses this feature
        # exists to catch (confirmed live: a horse's most recent captured
        # row was a trial 22 days out, so first_up read False instead of
        # True for a horse off a 130+ day spell). Drop unrated rows before
        # any date-based reasoning runs.
        p = p[pd.to_numeric(p["wpr"], errors="coerce").notna()]
    if p is None or len(p) < _MIN_RUNS:
        return None

    p = p.sort_values("date").reset_index(drop=True)
    w = pd.to_numeric(p["wpr"], errors="coerce")

    # Void-aware base (per user request): a prior run flagged void (vet/
    # checked/eased/fell/etc, per video+steward comments) is not valid
    # evidence of this horse's true WPR (see wpr_void.py's own docstring) -
    # exclude it from every "how good is this horse" computation below.
    # avg_last3/ewm3/career_avg/peak/std/best3/trend AND the own_* ADJ_TERMS
    # deltas are all pure functions of w, so masking it once here covers all
    # of them without touching p/dist/settle - campaign-sequence features
    # (first-up/second-up/days_since, which read p/dates directly, not w)
    # are completely unaffected; only the WPR VALUE at a void position is
    # discounted, not the row itself. void_from_comment_only, not is_void:
    # there is no historical projection to compare a prior run's miss
    # against, so only the conservative STRONG-marker-only test applies -
    # same test the training target's own void filter already uses (see
    # train_wpr_projection), same markers, same conservatism.
    n_void_excluded = 0
    if _void_from_comment_only is not None:
        cv_hist = p.get("comments_video")
        cs_hist = p.get("comments_steward")
        if cv_hist is not None or cs_hist is not None:
            if cv_hist is None:
                cv_hist = pd.Series([None] * len(p), index=p.index)
            if cs_hist is None:
                cs_hist = pd.Series([None] * len(p), index=p.index)
            void_mask = pd.Series(
                [_void_from_comment_only(a, b)[0] for a, b in zip(cv_hist, cs_hist)],
                index=p.index)
            w_excl = w.mask(void_mask)
            # Safety fallback: never let exclusion wipe out ALL history (every
            # downstream feature would go NaN) - if every prior run happens
            # to be flagged, fall back to the raw values rather than nothing.
            if w_excl.notna().sum() >= 1:
                w = w_excl
                n_void_excluded = int(void_mask.sum())

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

    # own_settle ingredients (own_distance/own_going pattern - see the
    # ADJ_TERMS computation further below where career_avg is available).
    # settle_band_hist bands each PAST run by its own ACTUAL settle
    # (already happened, no prediction needed); cur_settle_band predicts
    # TODAY's band the same way settling_estimate.py does (this horse's
    # own run_style tendency, computed from PRIOR runs only above, plus a
    # small nudge from today's barrier) - leak-safe and pre-race-knowable
    # at both train and serve time, unlike a race-wide tempo estimate
    # (own_pace, below, needs one - it gets it from
    # race_speed_estimate.py's own trained, leak-safe model instead of a
    # per-horse formula like this one).
    _rel_settle_full = pd.Series(np.nan, index=p.index)
    _rel_settle_full.loc[valid_st] = (settle[valid_st] / pfs[valid_st]).clip(0, 1)
    settle_band_hist = _rel_settle_full.apply(_settle_band)

    # own_pace ingredients: this horse's own tempo band (Fast/Even/Slow, see
    # _own_tempo_band) for each PRIOR run - purely descriptive of a run
    # that's already happened, no leak risk. Matched against
    # cur_race_speed_label (today's PRE-race predicted race-wide shape)
    # further below, once career_avg is available.
    own_tempo_hist = None
    if "sect_i_early" in p.columns and "sect_i_l600" in p.columns:
        own_tempo_hist = pd.Series(
            [_own_tempo_band(e, l) for e, l in zip(p["sect_i_early"], p["sect_i_l600"])],
            index=p.index)
    cur_settle_band = None
    if len(rel_settle) >= 1 and _settle_barrier_nudge is not None:
        _nudge = _settle_barrier_nudge(cur_barrier, cur_field_size)
        _rel_est = min(1.0, max(0.0, run_style + _nudge))
        cur_settle_band = _settle_band(_rel_est)

    # closing_merit ingredients (own-history half - see _closing_merit_term's
    # docstring for the population half): this horse's own last up to 3
    # PRIOR runs' (sect_i_l600, raceShapeEarly-bucket) pairs, in the SAME
    # last-N-by-position-then-drop-invalid order wpr_closing_merit_strike_
    # eval.py's build_closing_merit validated (not "last 3 valid values
    # regardless of how far back" - a real behavioural difference when a
    # horse has gaps in sectional capture). Combined with the fitted
    # population lookup post-hoc by _closing_merit_term, both at serve
    # time (project_race) and at train_wpr_projection()'s own cf/te
    # scoring step.
    closing_pairs = []
    if "sect_i_l600" in p.columns and "raceShapeEarly" in p.columns:
        _cm_sect = pd.to_numeric(p["sect_i_l600"], errors="coerce").iloc[-3:]
        _cm_early = pd.to_numeric(p["raceShapeEarly"], errors="coerce").iloc[-3:]
        for _s, _e in zip(_cm_sect, _cm_early):
            if _s == _s and _e == _e:
                closing_pairs.append((float(_s), _closing_merit_bucket(_e)))

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

    # campaign position of the run being projected - runs since the last
    # spell (gap > 60 days), counting the gap from the last prior run to
    # TODAY as a possible spell too. Bug fix (Aug 2026): this previously
    # only looked at gaps WITHIN the prior-runs history (dates.diff()),
    # never days_since itself - so a horse whose CURRENT spell was longer
    # than any spell in its recorded history kept whatever campaign
    # position it was on before the layoff, and was never correctly
    # flagged first_up/second_up. Found via the Autumn Glow case: 8 prior
    # runs with a 105-day gap partway through (runs_this_camp=4 as of its
    # last run), then a 133-day spell before the race being projected -
    # the old code still said runs_this_camp=4 (mid-campaign) for what is
    # actually a fresh first-up run.
    gaps = dates.diff().dt.days
    spell_idx = gaps[gaps > _SPELL_GAP_DAYS].index
    if days_since > _SPELL_GAP_DAYS:
        runs_this_camp = 1
    else:
        runs_this_camp = (n - (spell_idx.max() if len(spell_idx) else 0)) + 1

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
    # Debut-campaign exclusion (Aug 2026 fix): spell_id==0 is the horse's
    # very first spell - its literal debut, not a genuine return from a
    # spell. camp_run_series==1 is trivially true for it (position 1 of
    # the first group), but that isn't what "first-up" means in racing
    # usage (back from a spell), and conflating debut form with genuine
    # first-up-from-a-spell form was silently corrupting own_first_up (and
    # every other camp-position match here) for any horse whose sample
    # happened to include its debut. Confirmed on real data (Cross Tasman,
    # Aug 2026): own_first_up was -2.02 (averaging a modest 81.7 debut
    # together with a genuine 93.0 first-up return) instead of the correct
    # +0.15ish from the return run alone. Matches lib/careerStats.ts's own
    # "First-up" row definition, which already excluded debuts for the
    # same reason - this fix brings the backend in line with it.
    _non_debut = spell_id != spell_id.iloc[0]
    r1 = w[(camp_run_series == 1) & _non_debut]
    r2 = w[(camp_run_series == 2) & _non_debut]
    r3 = w[(camp_run_series == 3) & _non_debut]
    r4 = w[(camp_run_series == 4) & _non_debut]
    r5 = w[(camp_run_series == 5) & _non_debut]
    firstup_wpr = float(r1.mean()) if len(r1) >= 1 else avg_last3
    secondup_wpr = float(r2.mean()) if len(r2) >= 1 else avg_last3
    thirdup_wpr = float(r3.mean()) if len(r3) >= 1 else avg_last3

    # -----------------------------------------------------------------
    # SIMPLE ADJUSTMENT MODEL (replaces the Ridge fit on ADJ_FEATURES,
    # see project_race/train_wpr_projection). Per user request: a fully
    # transparent adjustment = sum of "+/- vs this horse's own career
    # average, at this condition, using only ITS OWN history" deltas,
    # instead of population-level coefficients fit across every horse
    # (the "doesn't pass the pub test" complaint - a blanket wet-track or
    # first-up penalty applied identically to every runner regardless of
    # whether THAT horse personally goes better or worse in it). Each
    # delta is shrunk by _shrink() so a horse with only 1-2 matching runs
    # gets a heavily discounted nudge rather than a full-strength one from
    # noise. Zero (no adjustment) when a horse has no own history at that
    # condition, or the condition doesn't apply today (e.g. own_first_up
    # is 0 unless today actually IS this horse's first-up run).
    #
    # Scope note: settling position, early speed/pace, barrier and
    # combinations of the above were part of the original request but are
    # deferred - the first three need race-WIDE context (predicted pace/
    # settle depend on the whole field, not just this horse) which is a
    # separate, bigger change than a per-horse lookup; barrier already
    # failed a population-level test (Aug 2026 feature search) and would
    # be sparse to the point of near-always-zero here too (a horse rarely
    # repeats the same barrier band often enough to have real history).
    #
    # TESTED, NOT ADOPTED (Aug 2026): own_track (mirrors own_going exactly,
    # matching on p["track"] == cur_track), own_jockey and own_trainer
    # (upgrade/downgrade bucketing using each connection's CURRENT
    # jockey_rating/trainer_rating from toprate_runners.csv applied
    # retroactively to past rides, since no per-run historical rating is
    # captured - see the reverted _own_person_delta/_load_person_ratings).
    # All three had good coverage (own_track fired on 62% of held-out
    # runners, own_jockey 97%, own_trainer 48% - not a sparsity problem)
    # but each measurably WORSENED held-out MAE on its own (+0.10, +0.12,
    # +0.10 respectively vs the 6-term baseline, ~+0.36 combined,
    # roughly additive) with no offsetting legibility gain (the system was
    # already fully transparent without them). Reverted cleanly; worth
    # revisiting only with a real per-run historical rating source for
    # jockey/trainer, or a less noisy own_track methodology.
    # TESTED, NOT ADOPTED (Aug 2026): using MEDIAN instead of mean for the
    # matching-condition value below, on the theory that with typically
    # only 1-5 matching runs, a single freak result could swing a mean hard
    # and the median would be more robust to it. Held-out MAE 6.333 (mean)
    # -> 6.368 (median): a real, if small, REGRESSION, not an improvement -
    # the hypothesis didn't hold on real data. Reverted cleanly.
    # EXACT distance match (Aug 2026, user request - replaces the +/-10%
    # band this used before). Tested head-to-head against the band: exact
    # match held-out MAE 5.9049 vs the band's 5.9149 (-0.0100, a real
    # improvement) despite firing on fewer runners (21,552/32,101 held-out
    # rows matched exactly vs 28,118/32,101 within the band) - precision
    # outweighs the sample-size loss here. Replaces the band entirely,
    # no accuracy reason to keep both.
    dist_match = dist == float(cur_distance)
    n_dist = int(dist_match.sum())
    own_distance = _shrink(float(w[dist_match].mean() - career_avg), n_dist) \
        if n_dist >= 1 else 0.0

    going_band_hist = p["going"].apply(_going_band)
    cur_going_band = _going_band(cur_going)
    going_match = going_band_hist == cur_going_band
    n_going = int(going_match.sum())
    own_going = _shrink(float(w[going_match].mean() - career_avg), n_going) \
        if (cur_going_band is not None and n_going >= 1) else 0.0

    # TESTED, NOT ADOPTED (Aug 2026, user request): own_track_distance -
    # does THIS horse personally run above/below its own level at THIS
    # EXACT track AND THIS EXACT distance together (joint match), as
    # distinct from own_distance (adopted) and own_track (tested,
    # rejected: +0.10 MAE alone, see the own_track/own_jockey/own_trainer
    # note above). 34.2% held-out coverage (sparser than either dimension
    # alone, as expected). Held-out MAE 5.9049 -> 6.0265 (+0.1216 worse) -
    # the extra precision of joint conditioning does not beat the smaller
    # sample; same conclusion as own_track alone and every other narrow
    # own-history split tried this session. Not added to ADJ_TERMS. Still
    # emitted below (harmless, informative) even though it isn't part of
    # the projection.
    track_dist_match = (p["track"] == cur_track) & (dist == float(cur_distance))
    n_track_dist = int(track_dist_match.sum())
    own_track_distance = _shrink(float(w[track_dist_match].mean() - career_avg), n_track_dist) \
        if n_track_dist >= 1 else 0.0

    # TESTED, NOT ADOPTED (Aug 2026, user request): own_recent_trend - "is
    # this horse trending up or down lately" for EVERY horse, not just the
    # lightly-raced-only own_trend below (gated to n in [4,6]). avg_last3
    # vs career_avg, shrunk by full run count n - the shrunk, ADJ_TERM-
    # shaped version of the raw recent_vs_career feature already emitted
    # below (unshrunk, feeds the confidence model, not the projection
    # sum). Held-out MAE 5.9049 -> 6.4394 (+0.5344 worse) - by far the
    # worst result of any candidate tried this session, confirming the
    # suspicion in the note above: BASE already blends in ewm3 (a
    # recency-weighted average over the horse's whole history), so this
    # doesn't add trend signal, it double-counts what BASE already has
    # and then some. Not added to ADJ_TERMS. Still emitted below (harmless,
    # informative) even though it isn't part of the projection.
    own_recent_trend = _shrink(float(avg_last3 - career_avg), n)

    # TESTED, NOT ADOPTED (Aug 2026, user request): own_settle - does THIS
    # horse personally run above or below its own level when it settles in
    # a given position band (Leader/On-pace/Midfield/Back)? Same own_going/
    # own_distance pattern - see settle_band_hist/cur_settle_band above for
    # how "today's predicted band" is derived leak-safe. Good coverage
    # (93.7% of held-out rows had a matching-band own history) but held-out
    # MAE got measurably WORSE: 5.9049 (7-term baseline) -> 6.0231
    # (+0.1182), the same conclusion as every other narrow own-history
    # split tried this session (own_barrier, own_wet/own_dry). Not added
    # to ADJ_TERMS. Still emitted below (harmless, informative) even
    # though it isn't part of the projection.
    settle_match = settle_band_hist == cur_settle_band
    n_settle = int(settle_match.sum())
    own_settle = _shrink(float(w[settle_match].mean() - career_avg), n_settle) \
        if (cur_settle_band is not None and n_settle >= 1) else 0.0

    # TESTED, NOT ADOPTED (Aug 2026, user request): own_wet/own_dry - does
    # THIS horse personally run above or below its own level at wet (Soft
    # 6+) vs dry (Soft 5 or firmer) tracks specifically, using the
    # _wet_dry_band boundary (see its docstring - a tighter, differently-
    # placed cut than own_going's Firm/Good/Soft/Heavy band, which lumps
    # every Soft grading together). Mutually exclusive per race, same
    # pattern as own_first_up/own_second_up: only the one matching today's
    # actual going fires. Held-out MAE with both added: 6.0284 vs the
    # 6-term baseline's 5.9149 (+0.1134, clearly WORSE) - not added to
    # ADJ_TERMS. Still emitted below (harmless, informative) even though
    # they aren't part of the projection.
    wetdry_hist = tg_hist.apply(_wet_dry_band)
    cur_wetdry = _wet_dry_band(cur_track_grading)
    wet6_match = wetdry_hist == "Wet"
    dry5_match = wetdry_hist == "Dry"
    n_wet6 = int(wet6_match.sum())
    n_dry5 = int(dry5_match.sum())
    own_wet = _shrink(float(w[wet6_match].mean() - career_avg), n_wet6) \
        if (cur_wetdry == "Wet" and n_wet6 >= 1) else 0.0
    own_dry = _shrink(float(w[dry5_match].mean() - career_avg), n_dry5) \
        if (cur_wetdry == "Dry" and n_dry5 >= 1) else 0.0

    own_first_up = _shrink(float(r1.mean() - career_avg), len(r1)) \
        if (runs_this_camp == 1 and len(r1) >= 1) else 0.0
    own_second_up = _shrink(float(r2.mean() - career_avg), len(r2)) \
        if (runs_this_camp == 2 and len(r2) >= 1) else 0.0
    # TESTED, NOT ADOPTED (Aug 2026): third/fourth/fifth-up, same pattern
    # as own_first_up/own_second_up above - only counted when today
    # actually IS that camp position for this horse. Coverage was thin as
    # expected (9.4% / 7.1% / 5.0% of held-out rows respectively), and
    # unlike first-up/second-up, none of the three cleared the adoption
    # bar - each individually made held-out MAE WORSE vs the 6-term
    # baseline (5.9149): +0.0175 / +0.0144 / +0.0106. The first-up/
    # second-up result does not generalise to deeper campaign positions -
    # by 3rd-up+ a horse's recent form (already captured by ewm3/
    # avg_last3) is apparently a better read than its own history at that
    # specific camp position. Not added to ADJ_TERMS. Still emitted below
    # (harmless, informative features) even though they aren't part of
    # the projection.
    own_third_up = _shrink(float(r3.mean() - career_avg), len(r3)) \
        if (runs_this_camp == 3 and len(r3) >= 1) else 0.0
    own_fourth_up = _shrink(float(r4.mean() - career_avg), len(r4)) \
        if (runs_this_camp == 4 and len(r4) >= 1) else 0.0
    own_fifth_up = _shrink(float(r5.mean() - career_avg), len(r5)) \
        if (runs_this_camp == 5 and len(r5) >= 1) else 0.0

    # TESTED, NOT ADOPTED (Aug 2026): own_barrier, same shape as
    # own_going/own_distance but matched on RELATIVE barrier band (see
    # _barrier_band) instead of going/distance - does THIS horse personally
    # draw better or worse from a given relative position, same reasoning
    # as the other own_* terms. NOT sparse (94.7% of held-out runners had a
    # matching-band history, similar coverage to own_going) - but held-out
    # MAE got measurably WORSE with it in the additive sum: 5.9149 -> 6.0241
    # (+0.109), confirming the earlier flat population-level barrier
    # feature's rejection (Aug 2026 feature search) generalises to the
    # own-history framing too. Not added to ADJ_TERMS. Still emitted below
    # (0.0 when cur_barrier/cur_field_size are missing or there's no
    # matching-band history) since it's a harmless, informative feature
    # even though it isn't part of the projection.
    #
    # An earlier version of this backtest (before the fix below) found
    # own_barrier ALWAYS 0.0 on every held-out row and a spurious "no
    # change" MAE - build_training_frame()'s keep-columns list never
    # actually carried "barrier" through from the raw form-history CSV
    # (only field_size was kept), so p["barrier"] never existed at training
    # time even though it works fine at serving time via project_race's
    # cur_barrier. Fixed by adding "barrier" to that keep list; the real
    # result above is from the corrected training frame.
    cur_barrier_band = _barrier_band(cur_barrier, cur_field_size)
    if cur_barrier_band is not None and "barrier" in p.columns and "field_size" in p.columns:
        barrier_band_hist = [
            _barrier_band(bv, fv) for bv, fv in zip(p["barrier"], p["field_size"])
        ]
        barrier_match = pd.Series(barrier_band_hist, index=p.index) == cur_barrier_band
        n_barrier = int(barrier_match.sum())
        own_barrier = _shrink(float(w[barrier_match].mean() - career_avg), n_barrier) \
            if n_barrier >= 1 else 0.0
    else:
        own_barrier = 0.0

    # CANDIDATE (Aug 2026, user request - picking "race speed / shape"
    # projection back up after it was previously scoped as too big):
    # own_pace - does THIS horse personally run above or below its own
    # level when the race's early tempo looks like today's PREDICTED
    # shape? cur_race_speed_label is Hot/Fast/Even/Slow, race_speed_
    # estimate.py's own trained model output for TODAY's race (leak-safe:
    # that model itself only ever uses prior-run aggregates, computed
    # fresh at each historical point in time when this is backtested -
    # never the actual post-race shape, which the model cannot know
    # before the race is run). Hot folds into Fast for matching (see
    # own_tempo_hist above) since a single horse's own sectionals only
    # ever produce a three-way Fast/Even/Slow reading, same convention
    # the frontend's lib/pace.ts already uses. Solves the "field-level
    # aggregation" blocker that shelved this candidate before: the
    # aggregation happens once, inside race_speed_estimate.py's own
    # model, BEFORE build_features ever sees this horse - not something
    # build_features has to compute itself from a full race's runners.
    _cur_pace_band = "Fast" if cur_race_speed_label == "Hot" else cur_race_speed_label
    if _cur_pace_band is not None and own_tempo_hist is not None:
        pace_match = own_tempo_hist == _cur_pace_band
        n_pace = int(pace_match.sum())
        own_pace = _shrink(float(w[pace_match].mean() - career_avg), n_pace) \
            if n_pace >= 1 else 0.0
    else:
        n_pace, own_pace = 0, 0.0

    # TESTED, NOT ADOPTED (Aug 2026, user request): "all settle, mixed with
    # distance and/or barrier" - joint own-history conditioning combining
    # settle band and/or barrier band with distance, same "combination"
    # question as own_track_distance above but for the two OTHER rejected
    # single-dimension terms (own_settle: +0.1182 worse alone; own_barrier:
    # +0.109 worse alone) instead of own_track. All four WORSE, and worse
    # than any of their standalone components - pairing a working dimension
    # (own_distance, adopted, -0.0100) with a failing one does not rescue
    # it, and stacking failing dimensions compounds the damage:
    #   own_settle_distance:          5.9049 -> 6.0466 (+0.1417)
    #   own_settle_barrier:           5.9049 -> 6.0312 (+0.1262)
    #   own_distance_barrier:         5.9049 -> 6.0551 (+0.1502)
    #   own_settle_distance_barrier:  5.9049 -> 5.9792 (+0.0743)
    #   all four together:            5.9049 -> 6.3503 (+0.4454)
    # Confirms the own_track_distance finding generalises: joint
    # conditioning's narrower, sparser match never beats the accuracy lost
    # to sample size, for any pairing tried this session. Not added to
    # ADJ_TERMS. Still emitted below (harmless, informative) even though
    # they aren't part of the projection. All four default to 0.0 whenever
    # barrier isn't computable (same guard as own_barrier above) or settle
    # band isn't known today.
    _has_barrier_hist = cur_barrier_band is not None and "barrier" in p.columns and "field_size" in p.columns
    barrier_hist_series = pd.Series(barrier_band_hist, index=p.index) if _has_barrier_hist else None

    if cur_settle_band is not None:
        sd_match = (settle_band_hist == cur_settle_band) & (dist == float(cur_distance))
        n_settle_distance = int(sd_match.sum())
        own_settle_distance = _shrink(float(w[sd_match].mean() - career_avg), n_settle_distance) \
            if n_settle_distance >= 1 else 0.0
    else:
        n_settle_distance, own_settle_distance = 0, 0.0

    if cur_settle_band is not None and _has_barrier_hist:
        sb_match = (settle_band_hist == cur_settle_band) & (barrier_hist_series == cur_barrier_band)
        n_settle_barrier = int(sb_match.sum())
        own_settle_barrier = _shrink(float(w[sb_match].mean() - career_avg), n_settle_barrier) \
            if n_settle_barrier >= 1 else 0.0
    else:
        n_settle_barrier, own_settle_barrier = 0, 0.0

    if _has_barrier_hist:
        db_match = (dist == float(cur_distance)) & (barrier_hist_series == cur_barrier_band)
        n_distance_barrier = int(db_match.sum())
        own_distance_barrier = _shrink(float(w[db_match].mean() - career_avg), n_distance_barrier) \
            if n_distance_barrier >= 1 else 0.0
    else:
        n_distance_barrier, own_distance_barrier = 0, 0.0

    if cur_settle_band is not None and _has_barrier_hist:
        sdb_match = (settle_band_hist == cur_settle_band) & (dist == float(cur_distance)) \
            & (barrier_hist_series == cur_barrier_band)
        n_settle_distance_barrier = int(sdb_match.sum())
        own_settle_distance_barrier = _shrink(
            float(w[sdb_match].mean() - career_avg), n_settle_distance_barrier) \
            if n_settle_distance_barrier >= 1 else 0.0
    else:
        n_settle_distance_barrier, own_settle_distance_barrier = 0, 0.0

    # Lightly-raced trend: for a horse still early in its career (few
    # starts), is it improving? Second half of its runs so far vs the
    # first half - deliberately gated to lightly-raced horses only
    # (a well-established horse's "trend" is already captured by
    # avg_last3/career_avg without needing this).
    _LIGHTLY_RACED_MAX = 6
    if 4 <= n <= _LIGHTLY_RACED_MAX:
        half = n // 2
        own_trend = _shrink(float(w.iloc[-half:].mean() - w.iloc[:half].mean()), n)
    else:
        own_trend = 0.0

    # Long-spell decline: does THIS horse specifically run below its own
    # level after a genuinely long layoff (180+ days - well beyond the
    # standard 60-day first-up threshold, which already has its own term
    # above)? Only applies when today's own layoff is itself that long.
    _LONG_SPELL_DAYS = 180
    long_spell_mask = (gaps >= _LONG_SPELL_DAYS).fillna(False)
    n_long_spell = int(long_spell_mask.sum())
    own_long_spell = _shrink(float(w[long_spell_mask].mean() - career_avg), n_long_spell) \
        if (days_since >= _LONG_SPELL_DAYS and n_long_spell >= 1) else 0.0

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
        # ADJ_TERMS (see the SIMPLE ADJUSTMENT MODEL block above) - the
        # ENTIRE adjustment now, summed directly in project_race. No
        # regression, no coefficients: each is a shrunk +/- vs this
        # horse's own career average, computed from its own history only.
        "own_distance": own_distance,
        "own_going": own_going,
        "own_first_up": own_first_up,
        "own_second_up": own_second_up,
        "own_trend": own_trend,
        "own_long_spell": own_long_spell,
        # closing_merit's own-history half (see _closing_merit_term) - NOT
        # the ADJ_TERM itself (that needs the fitted population lookup,
        # injected post-hoc same as track_barrier - see project_race and
        # train_wpr_projection).
        "closing_pairs": closing_pairs,
        # Raw (unshrunk) record behind own_distance/own_going/own_first_up/
        # own_second_up above, and how many prior runs were discounted for
        # a comment-flagged issue (vet/checked/eased/etc) - for describe()'s
        # plain-language explanation, not used in the projection math itself
        # (that's what the shrunk own_* deltas above are for).
        "n_void_excluded": n_void_excluded,
        "dist_match_n": n_dist,
        "dist_match_avg": float(w[dist_match].mean()) if n_dist >= 1 else None,
        "going_match_n": n_going,
        "going_match_avg": float(w[going_match].mean())
            if (cur_going_band is not None and n_going >= 1) else None,
        "first_up_record_n": len(r1),
        "first_up_record_avg": float(r1.mean()) if len(r1) >= 1 else None,
        "second_up_record_n": len(r2),
        "second_up_record_avg": float(r2.mean()) if len(r2) >= 1 else None,
        # CANDIDATE terms (Aug 2026, not in ADJ_TERMS yet - being tested
        # individually for real held-out MAE gain before adoption).
        "own_third_up": own_third_up,
        "own_fourth_up": own_fourth_up,
        "own_fifth_up": own_fifth_up,
        "own_barrier": own_barrier,
        "own_settle": own_settle,
        "settle_match_n": n_settle,
        "cur_settle_band": cur_settle_band,
        "own_track_distance": own_track_distance,
        "track_dist_match_n": n_track_dist,
        "own_recent_trend": own_recent_trend,
        "own_settle_distance": own_settle_distance,
        "settle_distance_match_n": n_settle_distance,
        "own_settle_barrier": own_settle_barrier,
        "settle_barrier_match_n": n_settle_barrier,
        "own_distance_barrier": own_distance_barrier,
        "distance_barrier_match_n": n_distance_barrier,
        "own_settle_distance_barrier": own_settle_distance_barrier,
        "settle_distance_barrier_match_n": n_settle_distance_barrier,
        "own_pace": own_pace,
        "pace_match_n": n_pace,
        "own_wet": own_wet,
        "own_dry": own_dry,
        "wet_match_n": n_wet6,
        "dry_match_n": n_dry5,
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
        # wpr_nett - TopRate's own pre-race base rating for this run. In
        # FEATURES: the single biggest accuracy gain found in the Aug 2026
        # search. NaN-filled with the training median if absent (e.g. a
        # race TopRate has not rated).
        "wpr_nett": float(cur_wpr_nett)
            if cur_wpr_nett is not None and str(cur_wpr_nett) not in ("nan", "")
            else np.nan,
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


def get_price_beta():
    """The softmax beta used to turn projected WPR into wpr_price.

    Exposed so the dashboard can replicate the exact same price formula
    client-side when a user enters a manual rating override - otherwise a
    manual adjustment could only change the ONE runner's own displayed
    number, not the whole field's softmax-derived prices, which is what
    the real price model actually does (see project_race below).
    """
    _load_models()
    return _CFG.get("beta", 0.4)


EDGE_FEATURES = ["wprp_proj", "trainer_win_pct_365d", "jockey_win_pct_90d", "pfm_score"]


def compute_edge_scores(runners):
    """Blend WPR projection + trailing jockey/trainer form + a
    form-provider score (pfm_score) into a per-race win-probability
    estimate: the PRIMARY ranking model for the Race tab (promoted Aug
    2026 - see below), plus a bet-selection comparison against the
    market's own implied probability.

    runners: list of dicts, one per horse in the SAME race, each carrying
      whatever of EDGE_FEATURES is available plus "market_price" (the
      price to compare against - fixed_win_price pre-race, starting_price_sp/
      price_top once resulted).

    HOW THE SCORE IS COMPUTED: an unweighted average of z-scores (NOT a
    fitted model - see calibrate_edge_score.py's docstring for why a plain
    average beat a fitted logistic regression walked forward). Each
    feature is z-scored against its training mean/std; a runner missing a
    feature has it SKIPPED, not imputed - the score is the mean of
    whichever z-scores it actually has. A runner missing every feature
    gets no score at all (blend_prob/rank/price all None), same as a WPR
    projection with insufficient history - it does NOT get silently
    treated as "average".

    Returns a list of result dicts (same order):
      blend_prob, blend_rank, blend_price - the primary ranking. Softmax
        of the blend score over the WHOLE field (no market price needed -
        same convention as project_race's wpr_price). A missing wprp_proj
        forces the score to neutral (0.0) rather than leaving the runner
        unscored (see _score below) - practically, every runner with a
        valid config gets a blend_prob/rank/price. All three are None only
        in the defensive fallback case of an empty runners list.
      has_edge, model_prob, market_prob, edge (model_prob - market_prob,
        in probability points - multiply by 100 for percentage points).
        model_prob/market_prob are renormalised over just the runners with
        BOTH a score and a usable market_price, so they are directly
        comparable to each other (this is why they can differ slightly
        from blend_prob, which normalises over the whole scored field).
        has_edge is False (other keys None) for a runner with no usable
        market_price or score, or for every runner if fewer than 2 in the
        race qualify.
    All keys are None (blend_* included) if the edge_score calibration
    hasn't been fitted yet (see calibrate_edge_score.py --write).

    WHY THIS IS THE PRIMARY RANKING (not wprp_proj/wpr_rank), AND WHY THESE
    4 FEATURES: an Aug 2026 audit walked a model forward weekly (refit on
    strictly-prior data each time, not a single train/test split) across
    the full history and found this blend's ranking beats wpr_nett/
    wprp_proj alone on both AUC (~0.68 vs ~0.58) and top-1 strike rate
    (~27% vs ~23-25%) consistently across every burn-in window tested.
    Feature ablation showed trainer/jockey trailing form does almost all
    of that work; speed_rating and pf_ai_score added nothing and were
    dropped. pfm_score is a genuine mixed case (added AUC, but its
    presence/absence swung the ROI point estimate in a way neither
    version's ROI is significant enough to read as real) - kept in on the
    AUC evidence; see calibrate_edge_score.py's docstring for the full
    reasoning. It still does not beat the market favourite's raw strike
    rate (~34%) - the market has information this model doesn't (late
    scratches, drift, insider money).

    Separately, has_edge/model_prob/market_prob/edge is a bet-SELECTION
    filter on top of the ranking above - and the SAME walk-forward audit
    found NO overlay threshold reached statistical significance (max
    |t|=1.24 at edge>=0.20, n=362; low thresholds like edge>=0 were
    significantly NEGATIVE, t=-9.94). Treat edge as an experimental
    signal worth tracking forward, not a validated source of profit - see
    calibrate_edge_score.py's docstring for the full numbers.

    NOTE: the numbers above were walked forward under skip-and-average
    scoring (a runner missing wprp_proj scored from whatever else it had).
    Production _score below instead forces a missing wprp_proj to 0.0, a
    later explicit user decision made AFTER seeing that this measurably
    costs every metric (strike 27.25%->26.64%, ROI -0.02%->-1.87%, AUC
    0.6817->0.6701) - so the numbers above are not exactly what production
    currently does, they are the closest validated reference point. If
    re-validating, walk forward with the SAME force-zero rule production
    uses, not skip-and-average.

    Deliberately excludes jt_combo_win_pct - see toprate_daily.py's
    SIGNALS comment for why (confirmed leak of the runner's own result on
    low-ride-count combos). Mean/std come from calibrate_edge_score.py,
    computed offline on resulted races and stored in wpr_models/config.json
    under "edge_score" - never hand-edit that block, rerun the script
    (quarterly, or once a season's worth of new resulted races has
    accumulated).
    """
    _load_models()
    empty = {"blend_prob": None, "blend_rank": None, "blend_price": None,
             "has_edge": False, "model_prob": None, "market_prob": None, "edge": None}
    n = len(runners)
    cfg = _CFG.get("edge_score")
    if not cfg or n < 1:
        return [dict(empty) for _ in runners]

    feats = cfg["features"]
    means = cfg["means"]
    stds = cfg["stds"]

    def _score(r):
        # A missing wprp_proj forces the WHOLE score to neutral (0.0),
        # regardless of how strong the other signals (trainer/jockey form,
        # pfm_score) are - a deliberate user decision (Aug 2026), not the
        # better-performing option. Walk-forward tested against
        # skip-and-average (score the runner from whatever signals it DOES
        # have): forcing 0 measurably cost every metric (strike 27.25% ->
        # 26.64%, ROI -0.02% -> -1.87%, AUC 0.6817 -> 0.6701, logloss
        # 0.3032 -> 0.3051) and changed the top pick in 12.4% of races, 98.5%
        # of which were exactly this case (a no-wprp_proj runner winning on
        # strong trailing form under skip-and-average). Kept anyway per
        # explicit instruction - see calibrate_edge_score.py's docstring.
        wpr_v = r.get("wprp_proj")
        if wpr_v is None or wpr_v != wpr_v:
            return 0.0
        zs = []
        for f in feats:
            v = r.get(f)
            std = stds.get(f, 0.0)
            if v is None or v != v or not std:
                continue
            zs.append((float(v) - means.get(f, 0.0)) / std)
        return float(np.mean(zs)) if zs else 0.0

    score = np.array([_score(r) for r in runners], dtype=float)
    have_score = np.isfinite(score)
    results = [dict(empty) for _ in runners]
    if not have_score.any():
        return results

    # Primary ranking: softmax over runners that have a score. _score now
    # always returns a float (0.0 for a missing wprp_proj, per the user's
    # explicit instruction - see _score above), so have_score is true for
    # every real runner in practice; this guard is defensive only (an
    # empty runners list). Mirrors project_race's own wpr_price softmax so
    # the two "fair price" numbers behave alike.
    s_v = score[have_score]
    e_full = np.exp(s_v - s_v.max())
    blend_prob_v = e_full / e_full.sum()
    blend_rank_v = (-blend_prob_v).argsort().argsort() + 1
    blend_price_v = np.minimum(1.0 / blend_prob_v, 999.0)
    vi = 0
    for i in range(n):
        if have_score[i]:
            results[i]["blend_prob"] = round(float(blend_prob_v[vi]), 4)
            results[i]["blend_rank"] = int(blend_rank_v[vi])
            results[i]["blend_price"] = round(float(blend_price_v[vi]), 2)
            vi += 1

    prices = np.array([r.get("market_price") for r in runners], dtype=float)
    valid = have_score & np.isfinite(prices) & (prices > 1.0)
    if valid.sum() < 2:
        return results

    # Normalise model_prob over the SAME priced-and-scored subset as
    # market_prob (not the whole field) so the two are directly comparable -
    # an unpriced (e.g. late-scratched) or unscored runner shouldn't dilute
    # either side.
    s_valid = score[valid]
    e_v = np.exp(s_valid - s_valid.max())
    model_prob_v = e_v / e_v.sum()
    inv_v = 1.0 / prices[valid]
    market_prob_v = inv_v / inv_v.sum()

    vi = 0
    for i in range(n):
        if valid[i]:
            mp, kp = float(model_prob_v[vi]), float(market_prob_v[vi])
            results[i]["has_edge"] = True
            results[i]["model_prob"] = round(mp, 4)
            results[i]["market_prob"] = round(kp, 4)
            results[i]["edge"] = round(mp - kp, 4)
            vi += 1
    return results


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
                       cur_field_size=r.get("cur_field_size"),
                       cur_wpr_nett=r.get("cur_wpr_nett"),
                       cur_barrier=r.get("cur_barrier"),
                       cur_race_speed_label=r.get("cur_race_speed_label"))
        for r in runners
    ]
    fallbacks = [f is None for f in feat_dicts]

    # track_barrier: the one ADJ_TERMS entry not computed inside
    # build_features (see its docstring above _TRACK_BARRIER_K) - it needs
    # the FITTED population lookup from config.json, which only exists
    # after _load_models() above, so it is injected here rather than
    # threaded through build_features's own-history-only signature.
    _tb_lookup = _CFG.get("track_barrier_lookup")
    for f, r in zip(feat_dicts, runners):
        if f is not None:
            f["track_barrier"] = _track_barrier_term(
                r.get("cur_track"), r.get("cur_distance"),
                r.get("cur_barrier"), r.get("cur_field_size"), _tb_lookup)

    # closing_merit: same two-stage pattern as track_barrier above - the
    # own-history half (closing_pairs) IS computed inside build_features
    # (it needs prior_runs), but the fitted population lookup only exists
    # after _load_models(), so the final term is combined here.
    _pb_lookup = _CFG.get("pace_baseline_lookup")
    for f in feat_dicts:
        if f is not None:
            f["closing_merit"] = _closing_merit_term(f.get("closing_pairs"), _pb_lookup)

    # Confidence is computed FIRST (needs the FULL feature frame - the
    # Additive architecture: projection = base + sum(ADJ_TERMS). base is
    # the horse's own anchor (ewm5/ewm3, falling
    # back down a recency chain - see _compute_base); a fallback of None
    # only happens if EVERY level feature is missing, which
    # build_features() cannot produce once it has passed the _MIN_RUNS
    # gate (career_avg always exists by then) - the 0.0 fallback below is
    # defensive, not expected to fire in practice.
    base_arr = np.array([_compute_base(f) if f is not None else 0.0
                         for f in feat_dicts], dtype=float)
    X_adj = _adj_term_frame(feat_dicts)
    adj_contributions = _cap_adj_sum(X_adj.to_numpy())
    # Calibration slope (see _CALIB_ADJ_SLOPE/_CALIB_INTERCEPT above
    # _compute_base) applied to the adjustment here - the intercept and
    # base slope are already folded into base_arr via _compute_base,
    # together reproducing the fitted decomposed calibration exactly while
    # keeping base_wpr + adjustment == projected_wpr (per-feature
    # contributions scaled too, so they still sum to the scaled adjustment).
    adj_contributions = adj_contributions * _CALIB_ADJ_SLOPE
    adj = adj_contributions.sum(axis=1)
    proj = base_arr + adj

    # Confidence still needs the FULL feature frame - the q10/q90 models are
    # unchanged from the earlier gradient-boosting design (see _load_models).
    X = _feature_frame(feat_dicts)
    # Confidence: q90-q10 interval width from the quantile models, mapped
    # to 0-100 the same way the old error-predicting model's output was.
    # A wider interval = the model itself is less sure = lower confidence.
    # Measured better-calibrated than the old two-stage design (held-out
    # corr with actual error 0.289 vs 0.233, Aug 2026 rebuild) as well as
    # simpler (one architecture instead of two bolted-together models).
    interval_width = _CONF["hi"].predict(X) - _CONF["lo"].predict(X)
    clo, chi = _CFG["conf_lo"], _CFG["conf_hi"]
    conf = np.clip(100 * (1 - (interval_width - clo) / (chi - clo)), 0, 100)

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
            # base_wpr + adjustment reproduce projected_wpr exactly.
            base_wpr = float(base_arr[i])
            adjustment = float(proj[i]) - base_wpr
            contributions = dict(zip(ADJ_TERMS, adj_contributions[i]))
            results.append({
                "has_projection": True,
                "projected_wpr": round(float(proj[i]), 1),
                "base_wpr": round(base_wpr, 1),
                "adjustment": round(adjustment, 1),
                # Per-feature breakdown of `adjustment` - sums to it exactly.
                # Useful even when the total adjustment is too small for
                # describe()'s own >=3 WPR narration threshold to say
                # anything.
                "adjustment_contributions": {k: round(float(v), 2)
                                             for k, v in contributions.items()},
                "confidence": int(round(conf[i])),
                "wpr_price": round(float(price[i]), 2) if price[i] == price[i] else None,
                "wpr_rank": int(rank[i]) if rank[i] == rank[i] else None,
                "peak_wpr": round(float(w.max()), 1),
                "avg_l3": round(float(w.iloc[-3:].mean()), 1),
                "description": describe(feat_dicts[i], float(proj[i]),
                                        int(round(conf[i])),
                                        int(rank[i]) if rank[i] == rank[i] else None,
                                        contributions),
            })
    return results


# Plain-English phrase for each ADJ_TERMS term, keyed by (feature,
# negative-or-positive contribution).
def _adj_phrase(feat, value, contribution):
    """Plain-English phrase for one ADJ_TERMS contribution. value and
    contribution are the same number now (each term IS its own
    contribution, no coefficient to multiply through) - kept as two
    params for call-site compatibility with describe() below."""
    neg = contribution < 0
    if feat == "own_distance":
        return ("it has run below its own level at this trip before" if neg
                else "it has run above its own level at this trip before")
    if feat == "own_going":
        return ("it has run below its own level in this going before" if neg
                else "it has run above its own level in this going before")
    if feat == "own_first_up":
        return ("it has run below its own level first-up before" if neg
                else "it has run above its own level first-up before")
    if feat == "own_second_up":
        return ("it has run below its own level second-up before" if neg
                else "it has run above its own level second-up before")
    if feat == "own_trend":
        return ("its form has dipped across its short career so far" if neg
                else "it's a lightly raced horse improving with each run")
    if feat == "own_long_spell":
        return ("it has run below its own level after long layoffs before"
                if neg else
                "it has run above its own level after long layoffs before")
    if feat == "track_barrier":
        return ("its barrier draw tends to go worse than average at this "
                 "track and trip" if neg else
                 "its barrier draw tends to go better than average at this "
                 "track and trip")
    if feat == "closing_merit":
        return ("its recent closing sectionals have been weaker than the "
                 "pace of those races would suggest" if neg else
                 "its recent closing sectionals have been stronger than the "
                 "pace of those races would suggest")
    return None


def describe(feats, projected_wpr, confidence, wpr_rank, adj_contributions=None):
    """A formguide-style read of the projection, built from our own data.

    Reads like a pre-race form comment, not a model printout: what the
    base rating is built from (and what was set aside from it), where the
    horse sits in its current campaign (first-up/second-up record, or how
    deep into the prep it is), how it goes at this trip and in this going,
    then the number itself and how much to trust it - a few short, plain
    sentences in sequence rather than a list of disconnected observations
    (user request, Aug 2026, replacing the earlier "Projected X... That's
    above average because... Confidence is..." template).

    adj_contributions: {ADJ_TERMS name: contribution}, the additive
    model's actual per-term contribution to THIS runner's adjustment (see
    project_race). own_distance/own_going/own_first_up/own_second_up are
    already narrated above with real numbers (matched-run averages, not
    just a direction), so only own_trend/own_long_spell (no natural
    trip/going/prep sentence of their own) fall back to the older
    phrase-based explanation, reached for only when the projection sits
    a real distance from recent form.

    Honest by design, same as before: a clause only appears when the
    sample size behind it actually supports saying something - no clause
    is ever invented to fill space, and an unexplained gap says so
    plainly rather than guessing.
    """
    if feats is None:
        return "Not enough form history to make a projection."

    def _ordinal(n):
        if 10 <= n % 100 <= 20:
            suffix = "th"
        else:
            suffix = {1: "st", 2: "nd", 3: "rd"}.get(n % 10, "th")
        return f"{n}{suffix}"

    def _a_or_an(n):
        # "a 90-day break" vs "an 84-day break" - good enough for the day-
        # count ranges this actually sees (a spell is rarely in the
        # thousands), not a general-purpose English number-to-words rule.
        s = str(n)
        return "an" if s.startswith(("8", "11", "18")) else "a"

    def _vs(delta):
        """Plain-English comparator for a WPR delta, thresholds matching
        the frontend's own vsCareerAvg colour cutoffs (+/-1) so the text
        and the numbers next to it never disagree."""
        if delta is None:
            return None
        if delta >= 3:
            return "well above"
        if delta >= 1:
            return "above"
        if delta <= -3:
            return "well below"
        if delta <= -1:
            return "below"
        return "around"

    sentences = []
    career_avg = feats.get("career_avg")

    # ── What it's rated from ──
    # Always one short, concrete sentence stating the blended base itself
    # (user request, Aug 2026, replacing the earlier design that stayed
    # silent in the common case - see git history for that reasoning).
    # base_val matches _compute_base(feats) exactly (single source of
    # truth, same number the "base" figure shown elsewhere in the UI
    # uses) so this sentence and that figure can never disagree. Void-
    # excluded runs (interference/vet) fold into the same sentence as a
    # short trailing clause instead of a separate one - the "why" (which
    # runs, why) is secondary to the number itself.
    base_val = _compute_base(feats)
    nett = feats.get("wpr_nett")
    ewm3 = feats.get("ewm3")
    has_nett = nett is not None and nett == nett
    has_ewm3 = ewm3 is not None
    n_void = feats.get("n_void_excluded", 0)
    void_bit = f"; {n_void} run{'s' if n_void != 1 else ''} set aside" if n_void >= 1 else ""
    if base_val is not None:
        if has_nett and has_ewm3:
            sentences.append(f"Base {base_val:.1f} (TopRate {nett:.1f}, form {ewm3:.1f}{void_bit}).")
        elif has_nett:
            sentences.append(f"Base {base_val:.1f} (TopRate's rating only{void_bit}).")
        elif has_ewm3:
            sentences.append(f"Base {base_val:.1f} (recent form only{void_bit}).")
        else:
            sentences.append(f"Base {base_val:.1f} (career average only{void_bit}).")

    # ── Campaign context: first-up/second-up record, or how deep in the prep ──
    days_since = feats.get("days_since")
    an_days = _a_or_an(days_since) if days_since is not None else "a"
    # _ok: not None AND not NaN - n>=1 alone doesn't guarantee a usable
    # mean here. If a run's WPR was void-masked (see the void-aware base
    # block above), a match count of 1 landing entirely on that masked
    # run means avg is NaN (float, not None) even though n>=1. Found via
    # real-data testing (Aug 2026): printed literal "nan" in the
    # description text for exactly this case.
    def _ok(v):
        return v is not None and v == v

    if feats.get("first_up") == 1:
        n_r, avg_r = feats.get("first_up_record_n", 0), feats.get("first_up_record_avg")
        if n_r >= 1 and _ok(avg_r) and career_avg is not None:
            sentences.append(f"First-up off {an_days} {days_since}-day break, "
                             f"{_vs(avg_r - career_avg)} its 1st-up average "
                             f"({avg_r:.1f} from {n_r}).")
        else:
            sentences.append(f"First-up off {an_days} {days_since}-day break - "
                             f"no 1st-up runs on record.")
    elif feats.get("second_up") == 1:
        n_r, avg_r = feats.get("second_up_record_n", 0), feats.get("second_up_record_avg")
        if n_r >= 1 and _ok(avg_r) and career_avg is not None:
            sentences.append(f"Second-up today, {_vs(avg_r - career_avg)} "
                             f"its 2nd-up average ({avg_r:.1f} from {n_r}).")
        else:
            sentences.append("Second-up today - no 2nd-up runs on record.")
    else:
        runs_camp = feats.get("runs_this_camp")
        if runs_camp is not None and runs_camp >= 3:
            sentences.append(f"{_ordinal(runs_camp)}-up this campaign.")

    # ── Trip and going record ──
    cur_dist = feats.get("cur_distance")
    dn, davg = feats.get("dist_match_n", 0), feats.get("dist_match_avg")
    gn, gavg = feats.get("going_match_n", 0), feats.get("going_match_avg")
    trip_bits = []
    if dn >= 1 and _ok(davg) and career_avg is not None and cur_dist is not None:
        trip_bits.append(f"Races {_vs(davg - career_avg)} its {cur_dist:.0f}m average "
                         f"({davg:.1f} from {dn})")
    elif dn == 0 and cur_dist is not None:
        trip_bits.append(f"Untried at {cur_dist:.0f}m")
    # dn >= 1 but davg unusable (void-masked): say nothing rather than
    # falsely claim "untried" - it HAS run there, there's just no
    # reliable average to state.
    if gn >= 1 and _ok(gavg) and career_avg is not None:
        trip_bits.append(f"{_vs(gavg - career_avg)} its going average ({gavg:.1f} from {gn})")
    if trip_bits:
        # Capitalise explicitly rather than relying on the distance bit
        # (which supplies the leading "Races") always being first - the
        # going bit alone (distance bit skipped, see the void-masked note
        # above) would otherwise start the sentence lowercase.
        bit_text = " and ".join(trip_bits) + "."
        sentences.append(bit_text[0].upper() + bit_text[1:])

    # ── Anything else driving a real gap from recent form, not already covered above ──
    avg3 = feats.get("avg_last3")
    gap = (projected_wpr - avg3) if avg3 is not None else None
    if gap is not None and abs(gap) >= 3 and adj_contributions:
        _covered = {"own_distance", "own_going", "own_first_up", "own_second_up"}
        want_negative = gap < 0
        ranked = sorted(
            ((f, v) for f, v in adj_contributions.items() if f not in _covered),
            key=lambda t: t[1] if want_negative else -t[1])
        reason = None
        for f, c in ranked:
            if abs(c) < 0.5:
                break
            if (c < 0) != want_negative:
                continue
            reason = _adj_phrase(f, feats.get(f), c)
            if reason:
                break
        if reason:
            direction = "below" if want_negative else "above"
            sentences.append(f"That's {direction} its recent average because {reason}.")
        elif not trip_bits:
            # Only claim "just noise" when nothing above already gave a
            # real explanation - a gap driven by own_distance/own_going is
            # already explained in the trip/going sentence even though
            # this fallback would otherwise fire.
            direction = "below" if want_negative else "above"
            sentences.append(f"That's a touch {direction} its recent average, but nothing "
                             f"in particular explains it - just normal model noise.")

    # ── Form consistency ──
    sl5 = feats.get("std_last5", 5)
    if sl5 <= 3:
        sentences.append("Consistent form lately.")
    elif sl5 >= 9:
        sentences.append("Form's been up and down lately - less certain than usual.")

    # ── The number, and how much to trust it ──
    rank_txt = "top-rated" if wpr_rank == 1 else (
        f"rated {_ordinal(wpr_rank)}" if wpr_rank else "unranked")
    nr = feats.get("n_runs", 0)
    sc = feats.get("std_career", 5)
    if confidence >= 80:
        conf_txt = f"high confidence ({nr} runs)"
    elif confidence >= 60:
        conf_txt = f"moderate confidence ({nr} runs)"
    else:
        if sc >= 9:
            why = "career form's been all over the place"
        elif nr <= 6:
            why = "not much form to go on yet"
        else:
            why = "recent form's been patchy"
        conf_txt = f"low confidence - {why}"
    sentences.append(f"Projected {projected_wpr:.1f}, {rank_txt}; {conf_txt}.")

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


def _horse_feature_rows(g, race_speed_labels=None):
    """Build the feature rows for one horse's full run history, point-in-time.

    Module-level (not a closure) so it is picklable for multiprocessing. This
    is the single inner-loop definition used by BOTH the serial and parallel
    paths of build_training_frame, so the two produce identical output.

    race_speed_labels: optional {race_id: Hot/Fast/Even/Slow} lookup of each
    historical race's LEAK-SAFE predicted tempo (race_speed_estimate.py's
    own model, run with a prior-only cutoff - see the own_pace backtest
    script, not committed). Keyed by race_id, NOT run_id (fixed Aug 2026 -
    run_id is not a reliable per-row race key in the raw form history, see
    wpr_own_pace_backtest.merge_won_by_horse_date's docstring for the full
    writeup; race_id has no such problem). None (the default) leaves
    own_pace at 0.0 for every row - existing callers (the real retrain)
    are unaffected.

    Emits each model feature (from build_features) plus target and date, and
    three analysis-only columns (race_id, race_class, horse_id) that
    train_wpr_projection ignores because it selects FEATURES explicitly.
    They support the walk-forward composition breakdowns (by meeting grade
    / race) and correct-by-construction joins back to external per-row data.
    """
    g = g.reset_index(drop=True)
    out = []
    for i in range(_MIN_RUNS, len(g)):
        cur = g.iloc[i]
        _label = race_speed_labels.get(cur.get("race_id")) if race_speed_labels else None
        f = build_features(g.iloc[:i], cur["distance"], cur["going"],
                           cur["track"], cur["trackGrading"], cur["date"],
                           cur_race_class=cur.get("race_class"),
                           cur_field_size=cur.get("field_size"),
                           cur_wpr_nett=cur.get("wpr_nett"),
                           cur_barrier=cur.get("barrier"),
                           cur_race_speed_label=_label)
        if f is None:
            continue
        f["target"] = float(cur["wpr"])
        f["date"] = cur["date"]
        # field_size is already a model feature (emitted by build_features).
        # race_id / race_class / run_id / horse_id are analysis-only (not
        # trained on).
        # CAUTION (found Aug 2026 while building a strike-rate backtest):
        # run_id here is NOT a per-historical-row race key - every row in
        # a scraped horse's WHOLE form table gets stamped with whatever
        # run_id it was being scraped FOR at that scrape time, not the
        # run_id of each individual past run. Verified: of form-history
        # rows that inner-join to toprate_runners.csv via run_id, 96.6%
        # have a date that does NOT match that run_id's actual race date
        # in toprate_runners.csv - i.e. run_id-keyed joins silently
        # attach the WRONG race's data to most historical rows (a horse's
        # 2017 run getting labelled with its 2026 race's outcome/wpr_nett).
        # wpr_nett's own merge above (this function, ~40 lines up) uses
        # this same run_id key - the practical damage there looks limited
        # (wpr_nett rarely drifts much per horse - median observed
        # within-horse range 0.0 across the full history) but it is not
        # nothing, and analysis code needing an EXACT per-row race match
        # (e.g. "did this row's race actually get won") MUST join by
        # (horse_id via the mapping to horse name, date) instead - see
        # wpr_own_pace_backtest.merge_won_by_horse_date.
        f["race_id"] = cur.get("race_id")
        f["race_class"] = cur.get("race_class")
        f["run_id"] = cur.get("run_id")
        f["horse_id"] = cur.get("horse_id")
        # Comments for THIS run, carried so the retrain's void filter can
        # exclude compromised runs from the target. Not features.
        f["comments_video"] = cur.get("comments_video")
        f["comments_steward"] = cur.get("comments_steward")
        # Raw going string for THIS run. Analysis-only (the model uses the
        # derived cur_surface). Carried so the retrain can exclude dirt/synth
        # races that have no turf going rating from the target.
        f["going"] = cur.get("going")
        # Track name and raw barrier number for THIS run. Analysis-only (not
        # model features - own_barrier already captures the per-horse
        # signal). Carried for the track x distance-conditioned barrier
        # analysis (Aug 2026, being tested) - does barrier draw matter more
        # at some tracks/distances than others, a population-level question
        # a per-horse own_barrier lookup can't answer.
        f["track"] = cur.get("track")
        f["barrier"] = cur.get("barrier")
        out.append(f)
    return out


def build_training_frame(form_history_csv="wpr_form_history.csv.gz", verbose=True,
                         n_jobs=1, race_speed_labels=None):
    """Regenerate the full training feature frame.

    Calls build_features() on every (horse, run) in the history - the SAME
    function used at serving time, so training and serving features are
    identical by construction.

    Speed: numeric columns are converted once per horse (not once per run),
    and each horse's runs are sliced from a pre-built frame. The feature
    values are byte-identical to calling build_features() on raw slices -
    train_wpr_projection() asserts this on a sample every run.

    race_speed_labels: optional {run_id: Hot/Fast/Even/Slow} lookup, passed
    straight through to _horse_feature_rows - see its docstring. None (the
    default) leaves own_pace at 0.0 for every row.

    n_jobs: 1 = serial (default, unchanged behaviour). >1 = that many worker
    processes. -1 or 0 = all cores. The per-horse loop is embarrassingly
    parallel, so output is identical regardless of n_jobs.
    """
    fh = pd.read_csv(form_history_csv)
    fh["date"] = pd.to_datetime(fh["date"], errors="coerce")
    # wpr_nett (TopRate's own pre-race base rating) is not captured in the
    # form-history scrape - it only exists in toprate_runners.csv, keyed by
    # run_id, from the pre-race fetch. Merge it in here so _horse_feature_rows
    # can read cur["wpr_nett"] the same way it reads cur["distance"] etc.
    # Left join: a run with no matching runners.csv row (or no wpr_nett
    # captured for it) just gets NaN, filled with the training median same
    # as every other feature.
    if "run_id" in fh.columns:
        _runners_csv = _DIR / "toprate_runners.csv"
        if _runners_csv.exists():
            _tr = pd.read_csv(_runners_csv, dtype={"run_id": str},
                              usecols=lambda c: c in ("run_id", "wpr_nett"),
                              low_memory=False)
            _tr["run_id"] = _tr["run_id"].astype(str)
            _tr = _tr.drop_duplicates(subset="run_id", keep="last")
            fh["run_id"] = fh["run_id"].astype(str)
            fh = fh.merge(_tr, on="run_id", how="left")
            if verbose:
                print(f"  wpr_nett merged: {fh['wpr_nett'].notna().sum():,} "
                      f"/ {len(fh):,} rows")
        elif verbose:
            print(f"  wpr_nett merge skipped: {_runners_csv.name} not found")
    # Collapse multi-scrape baselines BEFORE the keep-filter strips
    # scrape_date / formNumber. Must precede sort and feature build - a
    # mixed-baseline history corrupts every wpr-derived feature.
    fh = _dedup_scrape_baseline(fh, verbose=verbose)
    fh = fh.dropna(subset=["date", "wpr"]).sort_values(
        ["horse_id", "date"]).reset_index(drop=True)
    # columns build_features reads - keep only these, pre-convert numerics once
    # field_size: target-race context, pre-race known, used for the
    #   walk-forward by-field-size breakdown.
    # barrier: this run's stall number, paired with field_size for the
    #   own_barrier candidate (relative barrier band, see _barrier_band).
    #   Was missing from this keep list until Aug 2026 - own_barrier
    #   silently evaluated to 0.0 on every training/backtest row (p["barrier"]
    #   never existed) even though it works correctly at serving time via
    #   project_race's cur_barrier. Any backtest run before this fix is invalid.
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
            "isBarrierTrial", "barrier",
            "field_size", "raceShapeEarly", "raceShapeMid",
            "raceShapeLate", "race_class", "race_id", "run_id", "wpr_nett",
            "comments_video", "comments_steward"] + _sect_cols
    keep = [c for c in keep if c in fh.columns]
    fh = fh[keep].copy()
    for c in ["wpr", "distance", "trackGrading", "positionSettled",
              "position800m", "position600m", "margin800m", "margin600m",
              "margin400m", "marginFinish", "isBarrierTrial", "barrier",
              "field_size", "raceShapeEarly", "raceShapeMid", "raceShapeLate",
              "wpr_nett"] + _sect_cols:
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
        from functools import partial
        nproc = mp.cpu_count() if n_jobs in (-1, 0) else n_jobs
        nproc = max(1, min(nproc, total))
        if verbose:
            print(f"  building features on {nproc} cores ({total:,} horses) ...")
        worker = partial(_horse_feature_rows, race_speed_labels=race_speed_labels)
        with mp.Pool(nproc) as pool:
            results = pool.map(worker, groups, chunksize=64)
        rows = [r for sub in results for r in sub]
    else:
        rows = []
        for j, g in enumerate(groups):
            if verbose and j % 2000 == 0:
                print(f"  ... {j}/{total} horses")
            rows.extend(_horse_feature_rows(g, race_speed_labels=race_speed_labels))
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
    """Re-fit the projection (q50) and confidence (q10/q90 interval) models.
    Offline use only. Run: python wpr_projection.py --retrain [--jobs N]
    n_jobs is passed to the feature build (the slow step); -1 = all cores.

    Quantile architecture (Aug 2026 rebuild): one LightGBM model per
    quantile (0.1, 0.5, 0.9), all on the same FEATURES. q50 is the
    projection - it replaced a separately-tuned HistGradientBoosting mean
    regressor because a walk-forward comparison showed LOWER held-out MAE
    from the quantile objective's median (more robust to this target's
    noise than squared-error loss). q90-q10 (the interval width) is the
    confidence signal - it replaced a second model that predicted the
    first model's error, because the interval width correlated MORE
    strongly with actual error on held-out data (+0.289 vs +0.233) than
    that bolted-on error model did, from one simpler architecture instead
    of two. See wpr_projection.py's module docstring / CLAUDE.md for the
    walk-forward numbers this is based on.
    """
    import lightgbm as lgb
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

    # BASE for the additive architecture - must match _compute_base()
    # exactly (an _BASE_BLEND_ALPHA-weighted wpr_nett/ewm3 blend when both
    # are present, else whichever half is available, else
    # avg_last3/career_avg). Computed from RAW values, BEFORE the FEATURES
    # median-fill below - the fallback chain only means anything before a
    # missing value gets silently replaced by the population median.
    # career_avg is guaranteed present once _MIN_RUNS is met, so this
    # should never actually fall through to NaN - the dropna is defensive.
    _both = D["wpr_nett"].notna() & D["ewm3"].notna()
    D["_base"] = np.where(_both, _BASE_BLEND_ALPHA * D["wpr_nett"] + (1 - _BASE_BLEND_ALPHA) * D["ewm3"],
                          D["wpr_nett"].fillna(D["ewm3"]))
    D["_base"] = pd.Series(D["_base"], index=D.index).fillna(D["avg_last3"]).fillna(D["career_avg"])
    n_before_base = len(D)
    D = D.dropna(subset=["_base"]).copy()
    if len(D) < n_before_base:
        print(f"  dropped {n_before_base - len(D):,} rows with no usable "
              f"base rating (should be rare/never)")
    D["_y"] = D["target"] - D["_base"]

    med = D[FEATURES].median()
    D[FEATURES] = D[FEATURES].fillna(med)

    q1, q2 = D["date"].quantile([0.70, 0.85])
    trn = D[D["date"] < q1]
    cf = D[(D["date"] >= q1) & (D["date"] < q2)].copy()
    te = D[D["date"] >= q2].copy()

    # track_barrier: fit the population lookup on trn only (see its
    # docstring near _TRACK_BARRIER_K above) - the one ADJ_TERMS entry that
    # needs an actual training pass, unlike every other term here, which is
    # a pure per-horse own-history lookup needing no fitting. cur_distance/
    # field_size are FEATURES columns (already median-filled above, never
    # NaN here); only barrier can be missing, handled by _barrier_band
    # returning None and the dropna below dropping it.
    print("  fitting track_barrier lookup (population, trn only)...")
    _tb_resid = trn["target"] - trn["career_avg"]
    _tb_band = [_barrier_band(b, f) for b, f in zip(trn["barrier"], trn["field_size"])]
    _tb_dist_band = (trn["cur_distance"] // 200 * 200).astype(int)
    _tb_frame = pd.DataFrame({
        "track": trn["track"], "dist_band": _tb_dist_band,
        "band": _tb_band, "residual": _tb_resid,
    }).dropna(subset=["track", "band", "residual"])
    _tb_global = _tb_frame.groupby("band")["residual"].mean().to_dict()
    track_barrier_lookup = {}
    for (trk, db), g in _tb_frame.groupby(["track", "dist_band"]):
        stats = g.groupby("band")["residual"].agg(["mean", "count"])
        shrunk = {}
        for b in ["Inside", "Mid", "Wide"]:
            if b in stats.index:
                n, m = stats.loc[b, "count"], stats.loc[b, "mean"]
                shrunk[b] = (n * m + _TRACK_BARRIER_K * _tb_global.get(b, 0.0)) / (n + _TRACK_BARRIER_K)
            else:
                shrunk[b] = _tb_global.get(b, 0.0)
        center = float(np.mean(list(shrunk.values())))
        track_barrier_lookup[f"{trk}|{int(db)}"] = {
            b: float(max(-_OWN_DELTA_CAP, min(_OWN_DELTA_CAP, shrunk[b] - center))) for b in shrunk
        }
    print(f"  track_barrier: {len(track_barrier_lookup):,} (track, dist-band) combos")

    # Applied to cf/te (not trn, which is never scored) so the held-out MAE
    # printed further down actually reflects this term - project_race()
    # injects it at serve time from this SAME lookup, saved to config.json
    # below.
    for _frame in (cf, te):
        _frame["track_barrier"] = [
            _track_barrier_term(trk, dist, bar, fs, track_barrier_lookup)
            for trk, dist, bar, fs in zip(_frame["track"], _frame["cur_distance"],
                                          _frame["barrier"], _frame["field_size"])
        ]

    # closing_merit: population half fit on trn's date cutoff (q1), same
    # leak-safe convention as track_barrier above - see _fit_pace_baseline
    # and _closing_merit_term's docstrings for the full two-stage design.
    print("  fitting closing_merit pace-context baseline (population, trn only)...")
    pace_baseline_lookup = _fit_pace_baseline(form_history_csv, q1)
    print(f"  closing_merit: {len(pace_baseline_lookup):,} pace-context buckets")
    for _frame in (cf, te):
        _frame["closing_merit"] = [
            _closing_merit_term(pairs, pace_baseline_lookup)
            for pairs in _frame["closing_pairs"]
        ]

    # recency-weighted: down-weight old rows (the wpr scale drifts). Used by
    # the confidence quantile models (ADJ_TERMS themselves have no fitting
    # step to weight - see below).
    sw_recency = _recency_weights(trn["date"])
    if _RECENCY_HALF_LIFE_DAYS:
        print(f"  recency-weighted training: {_RECENCY_HALF_LIFE_DAYS}d "
              f"half-life")

    # rarity-weighted: upweight the thin high-WPR tail (see _rarity_weights
    # docstring). This fixes a real, measured elite-tier under-projection
    # bias for a POPULATION-LEVEL model (a post-hoc calibration cannot fix
    # it - tested and confirmed). The ADJ_TERMS sum does NOT need this: it's
    # a per-horse lookup against that horse's own history, not a fitted
    # population model, so it does not have the "regress rare examples
    # toward the population" failure mode rarity-weighting was built to
    # counter. Kept ONLY for the confidence (q10/q90) models, which are
    # otherwise unchanged from the Aug 2026 additive-architecture design.
    rw = _rarity_weights(trn["target"])
    sw = rw if sw_recency is None else sw_recency * rw
    print("  rarity-weighted training: upweighting target>=80/90/95/100 rows "
          "(elite-tier calibration fix, confidence models only)")

    def _fit_quantile(q):
        m = lgb.LGBMRegressor(objective="quantile", alpha=q, n_estimators=350,
                              max_depth=3, learning_rate=0.04, num_leaves=8,
                              random_state=42, verbosity=-1)
        m.fit(trn[FEATURES], trn["target"], sample_weight=sw)
        return m

    # Confidence models only (q10/q90 interval width) - unchanged design.
    q_lo = _fit_quantile(0.1)
    q_hi = _fit_quantile(0.9)

    # The additive model's ADJUSTMENT term: sum(ADJ_TERMS) - each already a
    # complete, shrunk +/- (per-horse from build_features, or track_barrier
    # from the population fit just above - see ADJ_TERMS/SIMPLE ADJUSTMENT
    # MODEL). No further fitting here - this is where a Ridge regression
    # used to be, before the rebuild to a transparent, mostly-per-horse-
    # history design.
    def _additive_predict(frame):
        return frame["_base"].to_numpy() + _cap_adj_sum(
            frame[ADJ_TERMS].to_numpy()).sum(axis=1)

    cf["abs_err"] = (_additive_predict(cf) - cf["target"]).abs()
    te["abs_err"] = (_additive_predict(te) - te["target"]).abs()

    cf_interval = q_hi.predict(cf[FEATURES]) - q_lo.predict(cf[FEATURES])
    clo, chi = np.quantile(cf_interval, [0.05, 0.95])
    _conf_corr = np.corrcoef(
        q_hi.predict(te[FEATURES]) - q_lo.predict(te[FEATURES]),
        te["abs_err"])[0, 1]
    print(f"  confidence (interval width) corr with actual error, held-out: "
          f"{_conf_corr:+.3f}")
    if _conf_corr < 0.1:
        print("  WARNING: confidence barely tracks error - investigate.")

    te_pred = _additive_predict(te)
    mae = mean_absolute_error(te["target"], te_pred)
    print(f"  held-out projection MAE: {mae:.3f}")

    # Calibration offset (a uniform additive shift = the median held-out
    # residual, recentering the typical projection) used to be applied here
    # - removed at the user's explicit instruction (Aug 2026): it read as an
    # unexplained constant fudge applied to every runner. Left as a
    # diagnostic-only print (not applied, not saved to config) so the
    # residual bias this would have corrected stays visible across retrains.
    _resid = te["target"].values - te_pred
    _would_be_offset = float(np.median(_resid))
    _mae_if_calibrated = float(np.abs(_resid - _would_be_offset).mean())
    print(f"  held-out bias (uncorrected): mean {_resid.mean():+.2f}, "
          f"median {np.median(_resid):+.2f}")
    print(f"  MAE if calibration were applied: {_mae_if_calibrated:.3f} "
          f"(vs {mae:.3f} uncalibrated) - NOT applied, diagnostic only")

    # Recent-form blend: REMOVED in the additive-architecture rebuild. It
    # existed to correct the gradient-boosting model's over-shrinkage toward
    # career/context by pulling back toward avg_last3. The additive model's
    # BASE already anchors on the horse's own current level (ewm3/ewm5,
    # which already tracks recent competitive form directly), so this
    # correction no longer applies - re-blending toward avg_last3 on top of
    # a base that is already recent-form-anchored would double-count it.

    # beta (the price softmax parameter) is calibrated separately by
    # calibrate_price_beta.py against real resulted-race outcomes - it is
    # NOT re-derived here (this function has no win/loss data, only WPR
    # values). Carry the existing config's beta forward so a retrain does
    # not silently reset it back to the 0.4 default; only a config.json
    # that has never been calibrated falls back to 0.4.
    _existing_cfg_path = Path(out_dir) / "config.json"
    beta = 0.4
    if _existing_cfg_path.exists():
        try:
            beta = json.load(open(_existing_cfg_path)).get("beta", 0.4)
        except Exception:
            pass
    print(f"  beta carried forward from existing config: {beta} "
          f"(re-run calibrate_price_beta.py --write to re-derive it)")

    Path(out_dir).mkdir(exist_ok=True)
    # projection.joblib is now vestigial (no more Ridge model to store) -
    # kept as an empty artifact so _load_models()'s file-existence check
    # and wpr_models/'s three-file shape don't need to change.
    joblib.dump({}, Path(out_dir) / "projection.joblib")
    joblib.dump({"lo": q_lo, "hi": q_hi}, Path(out_dir) / "confidence.joblib")
    json.dump({"features": FEATURES, "adj_terms": ADJ_TERMS,
               "medians": med.to_dict(),
               "conf_lo": float(clo), "conf_hi": float(chi),
               "beta": beta, "min_runs": _MIN_RUNS,
               "track_barrier_lookup": track_barrier_lookup,
               "pace_baseline_lookup": pace_baseline_lookup},
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
