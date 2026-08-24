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
  BASE is the horse's own anchor: a 50/50 blend of wpr_nett (TopRate's own
  pre-race rating) and ewm3 (this horse's own recency-weighted average of
  its last ~3 runs) when both are available, falling back to whichever
  half is available, then avg_last3/career_avg; see _compute_base for the
  exact order. (A brief Aug 2026 period removed wpr_nett from base
  entirely for zero dependence on TopRate's own unaudited rating - reverted
  at the user's explicit instruction after it cost a real, measured ~0.56
  held-out MAE; see git history for both sets of numbers.)
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
    # BASE directly again (see _compute_base - a 50/50 blend with ewm3,
    # re-adopted Aug 2026 after a brief period without it), and is also
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
    "own_trend", "own_long_spell",
]
def _compute_base(feat):
    """The horse's own anchor for the additive model. Re-adopted (Aug 2026,
    explicit request) as a 50/50 blend of wpr_nett (TopRate's own pre-race
    rating) and ewm3 (this horse's own recency-weighted average of its last
    ~3 runs) when both are available - the same blend shipped previously
    (see git history, commit "Base rating: 50/50 wpr_nett/ewm3 blend"),
    after a brief period (Aug 2026) with wpr_nett removed entirely that
    cost a real, measured ~0.56 held-out MAE (5.769 -> 6.333) for zero
    dependence on TopRate's own unaudited rating - reverted here at the
    user's explicit instruction. Falls back to whichever half is available,
    then down ewm3/avg_last3/career_avg, when one or both are unrated.
    Note this uses ewm3 specifically, not the ewm5-once->3-starts switch
    that briefly replaced it - that switch was introduced alongside the
    wpr_nett removal and is reverted together with it here."""
    def _ok(v):
        return v is not None and not (isinstance(v, float) and v != v)

    nett = feat.get("wpr_nett")
    ewm3 = feat.get("ewm3")
    if _ok(nett) and _ok(ewm3):
        return 0.5 * float(nett) + 0.5 * float(ewm3)
    for key in ("wpr_nett", "ewm3", "avg_last3", "career_avg"):
        v = feat.get(key)
        if _ok(v):
            return float(v)
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
                   cur_field_size=None, cur_wpr_nett=None, cur_barrier=None):
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
    dist_lo, dist_hi = float(cur_distance) * 0.9, float(cur_distance) * 1.1
    dist_match = (dist >= dist_lo) & (dist <= dist_hi)
    n_dist = int(dist_match.sum())
    own_distance = _shrink(float(w[dist_match].mean() - career_avg), n_dist) \
        if n_dist >= 1 else 0.0

    going_band_hist = p["going"].apply(_going_band)
    cur_going_band = _going_band(cur_going)
    going_match = going_band_hist == cur_going_band
    n_going = int(going_match.sum())
    own_going = _shrink(float(w[going_match].mean() - career_avg), n_going) \
        if (cur_going_band is not None and n_going >= 1) else 0.0

    own_first_up = _shrink(float(r1.mean() - career_avg), len(r1)) \
        if (runs_this_camp == 1 and len(r1) >= 1) else 0.0
    own_second_up = _shrink(float(r2.mean() - career_avg), len(r2)) \
        if (runs_this_camp == 2 and len(r2) >= 1) else 0.0
    # CANDIDATE (Aug 2026, being tested): third/fourth/fifth-up, same
    # pattern as own_first_up/own_second_up above - only counted when
    # today actually IS that camp position for this horse. Expect thinner
    # coverage the further out (fewer horses race deep into a campaign
    # AND have enough matching history), so treat these as decreasingly
    # likely to clear the adoption bar - test each on its own held-out MAE
    # before adding to ADJ_TERMS, do not assume the first/second-up result
    # generalises.
    own_third_up = _shrink(float(r3.mean() - career_avg), len(r3)) \
        if (runs_this_camp == 3 and len(r3) >= 1) else 0.0
    own_fourth_up = _shrink(float(r4.mean() - career_avg), len(r4)) \
        if (runs_this_camp == 4 and len(r4) >= 1) else 0.0
    own_fifth_up = _shrink(float(r5.mean() - career_avg), len(r5)) \
        if (runs_this_camp == 5 and len(r5) >= 1) else 0.0

    # CANDIDATE (Aug 2026, being tested): own_barrier, same shape as
    # own_going/own_distance but matched on RELATIVE barrier band (see
    # _barrier_band) instead of going/distance. A flat population-level
    # barrier feature already failed a test (Aug 2026 feature search); this
    # asks a different question (does THIS horse personally draw better or
    # worse from a given relative position), same reasoning as the other
    # own_* terms. 0.0 (no signal) when cur_barrier/cur_field_size are
    # missing or there's no matching-band history.
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
                       cur_barrier=r.get("cur_barrier"))
        for r in runners
    ]
    fallbacks = [f is None for f in feat_dicts]

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
    has_nett = feats.get("wpr_nett") is not None and feats.get("wpr_nett") == feats.get("wpr_nett")
    has_ewm3 = feats.get("ewm3") is not None
    if has_nett and has_ewm3:
        base_txt = "Rated from a blend of TopRate's own pre-race figure and its recent-form average"
    elif has_nett:
        base_txt = "Rated from TopRate's own pre-race figure"
    elif has_ewm3:
        base_txt = "Rated from its recent-form average"
    else:
        base_txt = "Rated from its career figures"
    n_void = feats.get("n_void_excluded", 0)
    if n_void >= 1:
        base_txt += (f", setting aside {n_void} run{'s' if n_void != 1 else ''} "
                     f"discounted for interference or a vet issue")
    sentences.append(base_txt + ".")

    # ── Campaign context: first-up/second-up record, or how deep in the prep ──
    days_since = feats.get("days_since")
    an_days = _a_or_an(days_since) if days_since is not None else "a"
    if feats.get("first_up") == 1:
        n_r, avg_r = feats.get("first_up_record_n", 0), feats.get("first_up_record_avg")
        if n_r >= 1 and avg_r is not None and career_avg is not None:
            sentences.append(f"First-up off {an_days} {days_since}-day break, and it races "
                             f"{_vs(avg_r - career_avg)} its career average first-up "
                             f"({avg_r:.1f} avg from {n_r} run{'s' if n_r != 1 else ''}).")
        else:
            sentences.append(f"First-up off {an_days} {days_since}-day break, with no first-up "
                             f"runs on record to judge it by.")
    elif feats.get("second_up") == 1:
        n_r, avg_r = feats.get("second_up_record_n", 0), feats.get("second_up_record_avg")
        if n_r >= 1 and avg_r is not None and career_avg is not None:
            sentences.append(f"Second-up today, and it races {_vs(avg_r - career_avg)} "
                             f"its career average second-up "
                             f"({avg_r:.1f} avg from {n_r} run{'s' if n_r != 1 else ''}).")
        else:
            sentences.append("Second-up today, with no second-up runs on record to judge it by.")
    else:
        runs_camp = feats.get("runs_this_camp")
        if runs_camp is not None and runs_camp >= 3:
            sentences.append(f"{_ordinal(runs_camp)}-up this campaign.")

    # ── Trip and going record ──
    cur_dist = feats.get("cur_distance")
    dn, davg = feats.get("dist_match_n", 0), feats.get("dist_match_avg")
    gn, gavg = feats.get("going_match_n", 0), feats.get("going_match_avg")
    trip_bits = []
    if dn >= 1 and davg is not None and career_avg is not None and cur_dist is not None:
        trip_bits.append(f"It races {_vs(davg - career_avg)} its career average at "
                         f"{cur_dist:.0f}m ({davg:.1f} avg from {dn} run{'s' if dn != 1 else ''})")
    elif cur_dist is not None:
        trip_bits.append(f"It's untried at {cur_dist:.0f}m")
    if gn >= 1 and gavg is not None and career_avg is not None:
        trip_bits.append(f"{_vs(gavg - career_avg)} its average in this going "
                         f"({gavg:.1f} avg from {gn} run{'s' if gn != 1 else ''})")
    if trip_bits:
        sentences.append(" and ".join(trip_bits) + ".")

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
        sentences.append("It's been racing to a consistent level lately.")
    elif sl5 >= 9:
        sentences.append("Its form has been up and down lately, so this one's less "
                         "certain than usual.")

    # ── The number, and how much to trust it ──
    rank_txt = "top-rated in the race" if wpr_rank == 1 else (
        f"rated {_ordinal(wpr_rank)} in the race" if wpr_rank else "unranked")
    nr = feats.get("n_runs", 0)
    sc = feats.get("std_career", 5)
    if confidence >= 80:
        conf_txt = f"confidence is high on {nr} runs of settled career form"
    elif confidence >= 60:
        conf_txt = f"confidence is moderate on {nr} runs of career form"
    else:
        if sc >= 9:
            why = "its career form has been all over the place"
        elif nr <= 6:
            why = "it doesn't have much form to go on yet"
        else:
            why = "its recent form has been patchy"
        conf_txt = f"confidence is low because {why}"
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
                           cur_field_size=cur.get("field_size"),
                           cur_wpr_nett=cur.get("wpr_nett"),
                           cur_barrier=cur.get("barrier"))
        if f is None:
            continue
        f["target"] = float(cur["wpr"])
        f["date"] = cur["date"]
        # field_size is already a model feature (emitted by build_features).
        # race_id / race_class / run_id are analysis-only (not trained on).
        # run_id lets analysis code join in external per-run signals
        # (wpr_nett, pfm_score, etc.) from toprate_runners.csv by exact key.
        f["race_id"] = cur.get("race_id")
        f["race_class"] = cur.get("race_class")
        f["run_id"] = cur.get("run_id")
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
    # exactly (a 50/50 wpr_nett/ewm3 blend when both are present, else
    # whichever half is available, else avg_last3/career_avg). Computed
    # from RAW values, BEFORE the FEATURES median-fill below - the
    # fallback chain only means anything before a missing value gets
    # silently replaced by the population median. career_avg is guaranteed
    # present once _MIN_RUNS is met, so this should never actually fall
    # through to NaN - the dropna is defensive.
    _both = D["wpr_nett"].notna() & D["ewm3"].notna()
    D["_base"] = np.where(_both, 0.5 * D["wpr_nett"] + 0.5 * D["ewm3"], D["wpr_nett"].fillna(D["ewm3"]))
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
    # complete, shrunk, per-horse +/- computed in build_features (see the
    # SIMPLE ADJUSTMENT MODEL block there / ADJ_TERMS above). No fitting -
    # this is where a Ridge regression used to be, before the rebuild to a
    # fully transparent, per-horse-history design.
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
               "beta": beta, "min_runs": _MIN_RUNS},
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
