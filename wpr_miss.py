"""
wpr_miss.py - explains a MATERIAL miss (|actual WPR - projected WPR| >= 4)
once a race result settles.

Reuses wpr_void.py's comment classifier directly for the "projection was too
HIGH" (underperformance) direction - it already encodes the right direction
rule (a trouble comment only excuses an underperformance) and marker
taxonomy, so there is no reason to duplicate it here.

The "projection was too LOW" (overperformance) direction needs different
markers - positive running comments - since a trouble comment cannot explain
a horse running BETTER than expected. wpr_void has no equivalent for this,
so POSITIVE below is this file's own list.

When comments do not explain a material miss, falls back to structural
signals already sitting in toprate_runners.csv: whether the horse ran
beyond its own established level entirely (career peak / recent form - the
cleanest, most honest explanation there is), an untried trip (no own
history at this distance for the projection to have drawn on), and a large
pre-race price move (the market may have known something the rating did
not). If none of those explain it either, the caller is told to fall back
to a manual note - this file never invents a reason that is not actually
there.

NO EM DASHES policy: hyphens only.
"""

from wpr_void import is_void, _safe

MATERIAL_THRESHOLD = 4.0

# Positive running-comment markers - explain OVERperformance (actual >
# projected). The mirror image of wpr_void's STRONG/WEAK trouble markers,
# which only ever explain underperformance.
POSITIVE = ["untroubled", "hard held", "sprinted clear", "too strong",
            "travelled strongly", "travelled well", "impressive", "eased down",
            "easy win", "in a canter", "far too good", "class rise"]

# How far above its own established ceiling (career peak / recent form) an
# actual result has to land to count as genuinely unforeseeable.
_CEILING_MARGIN = 2.0

# A price move smaller than this is normal noise, not a signal worth citing.
_PRICE_MOVE_THRESHOLD = 0.25


def _price_drift_reason(miss, open_price, close_price):
    """A big market move in the SAME direction as the miss is a candidate
    explanation - the market sometimes knows something the rating didn't
    (late scratchings elsewhere, track/gear news, stable confidence)."""
    try:
        op, cp = float(open_price), float(close_price)
    except (TypeError, ValueError):
        return None
    if op <= 0 or cp <= 0:
        return None
    # positive = firmed (shorter, more confident); negative = drifted (longer)
    pct_move = (op - cp) / op
    if abs(pct_move) < _PRICE_MOVE_THRESHOLD:
        return None
    if miss < 0 and pct_move < 0:
        return (f"the market drifted it from ${op:.2f} to ${cp:.2f} before the "
                f"race - it may have known something the rating didn't")
    if miss > 0 and pct_move > 0:
        return (f"the market firmed it from ${op:.2f} to ${cp:.2f} before the "
                f"race - money may have confirmed something the rating missed")
    return None


def explain_miss(actual, proj, comment_video=None, comment_steward=None,
                 starts_at_dist=None, open_price=None, close_price=None,
                 peak_wpr=None, avg_last3=None):
    """Explain a resulted runner's material miss, or say there's none to
    explain.

    actual, proj: the settled actual WPR and the pre-race projected WPR.
    miss = actual - proj. Positive = ran BETTER than projected (understated);
    negative = ran WORSE than projected (overstated).

    Returns (category, text):
      (None, None)              - miss is not material (|miss| < 4), or unknown
      ("ceiling", text)         - ran above its own established level entirely -
                                   genuinely unforeseeable from its own record
      ("comment", text)         - explained by video/steward comments
      ("untried", text)         - first run at this trip, no own history to draw on
      ("price", text)           - a large pre-race price move in the same direction
      ("unexplained", text)     - material, but nothing above explains it -
                                   caller should offer a manual-note fallback
    """
    if actual is None or proj is None:
        return (None, None)
    try:
        actual, proj = float(actual), float(proj)
    except (TypeError, ValueError):
        return (None, None)
    miss = actual - proj
    if abs(miss) < MATERIAL_THRESHOLD:
        return (None, None)
    direction = "Overstated" if miss < 0 else "Understated"

    # Checked first for understatement, ahead of comments: if the horse ran
    # above BOTH its own career peak and its recent form, no amount of
    # condition-matching could have foreseen it - the most honest and
    # specific explanation available, so it should not be shadowed by a
    # weaker comment-based guess.
    if miss > 0:
        ceiling_vals = [float(v) for v in (peak_wpr, avg_last3) if v is not None]
        if ceiling_vals and actual > max(ceiling_vals) + _CEILING_MARGIN:
            return ("ceiling",
                     f"{direction} - ran above its own career-best level entirely; "
                     f"genuinely could not have been foreseen from its record.")

    if miss < 0:
        void, reason = is_void(miss, comment_video, comment_steward)
        if void:
            return ("comment", f"{direction} - {reason} (per the race comments).")
    else:
        text = _safe(comment_video).lower() + " " + _safe(comment_steward).lower()
        hits = [m for m in POSITIVE if m in text]
        if hits:
            return ("comment",
                     f"{direction} - travelled well ({', '.join(hits[:2])}, per the race comments).")

    try:
        if starts_at_dist is not None and float(starts_at_dist) == 0:
            return ("untried",
                     f"{direction} - this was its first run at the trip, so the "
                     f"rating had no history there to draw on.")
    except (TypeError, ValueError):
        pass

    price_reason = _price_drift_reason(miss, open_price, close_price)
    if price_reason:
        return ("price", f"{direction} - {price_reason}.")

    return ("unexplained", "No clear explanation in the available data - worth a manual look.")
