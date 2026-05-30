"""
wpr_void.py - shared logic for flagging "void" runs from comments.

A void run is one where the horse did not get a fair chance to show its true
WPR: vet issue, bled, eased when beaten, checked, fell, badly away, etc. These
runs are NOT valid evidence of the model's accuracy and should be excluded from:
  - error-review error stats (they inflate apparent model error)
  - the projection training target (the model should not learn to predict a
    compromised run-day WPR)

ONE definition, imported everywhere, so the adjudication readout, the error
review, and the retrain all agree on what counts as void.

DIRECTION RULE
  An excuse only voids an UNDER-performance. A horse that ran AT or ABOVE its
  projection despite a trouble comment clearly was not stopped by the trouble,
  so that run is kept (and is usually a model-too-low case). is_void() needs the
  miss (actual - projection) to apply this; void_from_comment_only() is the
  weaker comment-only test for when no projection is available.

NO EM DASHES policy: hyphens only.
"""

# Strong markers: the run is compromised enough to void on its own (given an
# underperformance). Health and hard-incident words.
STRONG = ["shin", "vet", "lame", "bled", "blood", "broke down", "fell",
          "checked", "badly hampered", "eased", "tailed off", "severely",
          "pulled up", "lost rider", "fractured"]

# Weak markers: minor trouble. Only voids a LARGE underperformance, since most
# horses overcome these.
WEAK = ["slowly away", "slow out", "bit slow out", "hampered", "held up",
        "crowded", "began awkwardly", "jumped awkwardly", "keen", "raced flat",
        "wide throughout", "interfere", "tightened", "awkwardly"]

# How large an underperformance a weak marker must accompany to count as void.
WEAK_MISS_THRESHOLD = -8.0


def _safe(x):
    """Coerce a possibly-NaN/None/float comment value to a string."""
    if x is None:
        return ""
    try:
        import math
        if isinstance(x, float) and math.isnan(x):
            return ""
    except Exception:
        pass
    return str(x)


def _markers(text):
    t = _safe(text).lower()
    return ([m for m in STRONG if m in t], [m for m in WEAK if m in t])


def is_void(miss, comment_video=None, comment_steward=None):
    """Should this run be excluded as compromised?

    miss = actual - projection (after any offset). Negative = underperformed.
    Returns (bool, reason). Direction rule: excuses only void underperformances.
    """
    if miss is None:
        # No projection to judge direction - fall back to comment-only.
        return void_from_comment_only(comment_video, comment_steward)
    if miss >= 0:
        return (False, "")            # ran at/above projection - not void
    text = _safe(comment_video) + " " + _safe(comment_steward)
    s, w = _markers(text)
    if s:
        return (True, ", ".join(s[:2]))
    if w and miss < WEAK_MISS_THRESHOLD:
        return (True, ", ".join(w[:2]))
    return (False, "")


def void_from_comment_only(comment_video=None, comment_steward=None):
    """Comment-only void test for when no projection/miss is available (e.g.
    deciding whether to keep a run in the training target). Conservative: only
    STRONG health/incident markers void here, since without a miss we cannot
    apply the direction rule and do not want to drop runs a horse overcame.
    """
    text = _safe(comment_video) + " " + _safe(comment_steward)
    s, _ = _markers(text)
    if s:
        return (True, ", ".join(s[:2]))
    return (False, "")
