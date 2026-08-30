import type { Runner } from '../types/domain'

// Backtested (toprate_runners.csv, Apr-Aug 2026, ~50k runners): a runner's
// jockey/trainer combination win% is the one factor that survived a broad
// search for a profitable, high-volume betting signal (see git history for
// the full investigation) - walk-forward validated in both chronological
// directions, not outlier-driven, and broad-based across dozens of
// trainers rather than a handful.
//
// High volume: WPR rank<=3, combo>=25% (min 5 rides together), field<=10 -
// n=1,220 backtested bets, strike 37.9%, ROI +30.1%.
// Low volume: the above, plus a quiet recent form line (see
// recentTop3Rate below) - n=347, strike 37.5%, ROI +53.2%. Counter-
// intuitively, a horse that hasn't been placing lately wins about as often
// within this pool but at a bigger price, since the market discounts the
// visible form line more than the underlying signal warrants.
// Closers: High volume plus a backmarker running style (avgSettledPos>6) -
// n=325, strike 40.0%, ROI +51.6%, walk-forward validated both directions
// (threshold 6 was independently optimal on each half of the sample).
// Within this qualifying pool, horses that settle back and run on
// outperform on-pace types, plausibly because the visible-form-reading
// public undervalues a closer's finishing effort relative to an on-pace
// runner that "looked" competitive throughout.

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

export function qualifiesHighVolume(runner: Runner): boolean {
  return (
    !runner.dataScratched &&
    runner.wprRank != null &&
    runner.wprRank <= 3 &&
    runner.jtComboWinPct != null &&
    runner.jtComboWinPct >= 25 &&
    runner.jtComboRides != null &&
    runner.jtComboRides >= 5 &&
    runner.fieldSize <= 10
  )
}

export function qualifiesLowVolume(runner: Runner): boolean {
  if (!qualifiesHighVolume(runner)) return false
  const rate = recentTop3Rate(runner.formString)
  return rate != null && rate < 0.4
}

export function qualifiesClosers(runner: Runner): boolean {
  if (!qualifiesHighVolume(runner)) return false
  return runner.avgSettledPos != null && runner.avgSettledPos > 6
}

export function qualifiesForTier(runner: Runner, tier: StrategyTier): boolean {
  if (tier === 'high-volume') return qualifiesHighVolume(runner)
  if (tier === 'low-volume') return qualifiesLowVolume(runner)
  return qualifiesClosers(runner)
}
