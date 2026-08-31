import type { Runner } from '../types/domain'

// DISABLED (Aug 2026 audit) - jtComboWinPct (jt_combo_win_pct) was found to
// leak the runner's own race result: on combos with only 1-2 recorded rides
// together (most of them - see toprate_daily.py's SIGNALS comment), the
// provider's stat reads ~100% when the horse won and ~0% when it lost,
// i.e. it is not a pre-race trailing window, it reflects today's own
// outcome. Every backtest number this file used to cite (37.9% strike /
// +30.1% ROI etc.) was produced by that leak, not a real edge - see
// jt_combo_win_pct's definition comment in toprate_daily.py for the
// evidence. All three tiers below are hard-disabled (qualifiesHighVolume
// always returns false) until this is replaced by a signal that doesn't
// depend on jt_combo_win_pct. See wpr_projection.py's compute_edge_score
// for the properly-validated (held-out, non-leaky) replacement.

export type StrategyTier = 'high-volume' | 'low-volume' | 'closers'

// Parses a form string like "3-1-7-2" (most recent first) into individual
// results. 'x' (unplaced/no data) and '?' (unknown) are dropped rather than
// treated as a placing or a non-placing - we can't tell which from the raw
// string, so they're excluded from the rate rather than guessed.
function parseFormDigits(formString: string | null): number[] {
  if (!formString) return []
  return formString
    .split('-')
    .map((s) => Number(s))
    .filter((n) => Number.isFinite(n))
}

// Fraction of recent, known-position starts that finished 1st-3rd. null
// when there's no usable form data at all (every entry was 'x'/'?'), since
// "quiet form" can't be claimed without at least some real results.
export function recentTop3Rate(formString: string | null): number | null {
  const digits = parseFormDigits(formString)
  if (digits.length === 0) return null
  return digits.filter((n) => n <= 3).length / digits.length
}

export function qualifiesHighVolume(_runner: Runner): boolean {
  // Hard-disabled - see file header. Was gated on the leaky jtComboWinPct.
  return false
}

export function qualifiesLowVolume(runner: Runner): boolean {
  if (!qualifiesHighVolume(runner)) return false
  const rate = recentTop3Rate(runner.formString)
  return rate != null && rate < 0.4
}

export function qualifiesClosers(runner: Runner): boolean {
  if (!qualifiesHighVolume(runner)) return false
  if (runner.avgSettledPos == null || runner.avgSettledPos <= 6) return false
  const rate = recentTop3Rate(runner.formString)
  return rate != null && rate < 0.4
}

export function qualifiesForTier(runner: Runner, tier: StrategyTier): boolean {
  if (tier === 'high-volume') return qualifiesHighVolume(runner)
  if (tier === 'low-volume') return qualifiesLowVolume(runner)
  return qualifiesClosers(runner)
}
