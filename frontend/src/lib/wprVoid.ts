// TS port of wpr_void.py - kept deliberately in sync with the Python module
// (same markers, same direction rule) so the Review tab's void exclusion
// matches what the retrain's training-target filter already does. A void
// run is one where the horse didn't get a fair chance to show its true
// WPR (vet issue, bled, eased when beaten, checked, fell, etc.) - not
// valid evidence of the model's accuracy.
//
// DIRECTION RULE: an excuse only voids an UNDER-performance. A horse that
// ran at or above its projection despite a trouble comment clearly wasn't
// stopped by it, so that run stays in (see wpr_void.py's own docstring).

const STRONG = [
  'shin', 'vet', 'lame', 'bled', 'blood', 'broke down', 'fell',
  'checked', 'badly hampered', 'eased', 'tailed off', 'severely',
  'pulled up', 'lost rider', 'fractured',
]

const WEAK = [
  'slowly away', 'slow out', 'bit slow out', 'hampered', 'held up',
  'crowded', 'began awkwardly', 'jumped awkwardly', 'keen', 'raced flat',
  'wide throughout', 'interfere', 'tightened', 'awkwardly',
]

const WEAK_MISS_THRESHOLD = -8.0

export interface VoidResult {
  isVoid: boolean
  reason: string
}

function findMarkers(text: string): { strong: string[]; weak: string[] } {
  const t = text.toLowerCase()
  return {
    strong: STRONG.filter((m) => t.includes(m)),
    weak: WEAK.filter((m) => t.includes(m)),
  }
}

function combinedText(commentVideo: string | null, commentSteward: string | null): string {
  return `${commentVideo ?? ''} ${commentSteward ?? ''}`
}

/** Should this run be excluded as compromised? miss = actual - predicted;
 * negative = underperformed. Direction rule: excuses only void
 * underperformances. Mirrors wpr_void.py's is_void(). */
export function isVoid(
  miss: number | null,
  commentVideo: string | null,
  commentSteward: string | null
): VoidResult {
  if (miss == null) return voidFromCommentOnly(commentVideo, commentSteward)
  if (miss >= 0) return { isVoid: false, reason: '' }
  const { strong, weak } = findMarkers(combinedText(commentVideo, commentSteward))
  if (strong.length) return { isVoid: true, reason: strong.slice(0, 2).join(', ') }
  if (weak.length && miss < WEAK_MISS_THRESHOLD) {
    return { isVoid: true, reason: weak.slice(0, 2).join(', ') }
  }
  return { isVoid: false, reason: '' }
}

/** Comment-only void test for when no miss is available. Conservative:
 * only STRONG markers void here, since without a miss the direction rule
 * can't be applied. Mirrors wpr_void.py's void_from_comment_only(). */
export function voidFromCommentOnly(
  commentVideo: string | null,
  commentSteward: string | null
): VoidResult {
  const { strong } = findMarkers(combinedText(commentVideo, commentSteward))
  if (strong.length) return { isVoid: true, reason: strong.slice(0, 2).join(', ') }
  return { isVoid: false, reason: '' }
}
