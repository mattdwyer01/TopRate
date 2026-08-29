import type { Runner } from '../types/domain'

export type ConfidenceTier = 'tight' | 'clear' | 'standout'

export interface RaceConfidence {
  tier: ConfidenceTier
  label: string
  gap: number
}

// Thresholds from a real backtest (Aug 2026): win % for the model's top
// pick, segmented by its projected-WPR gap over the 2nd pick, across
// ~5,000 resulted races - 18.0% under a 0.5 gap, climbing smoothly to
// 41.5% at a 6.0+ gap. Collapsed to 3 tiers for display:
//   tight    (<1.0 gap):  ~18-20% win - the top few are close to a toss-up
//   clear    (1.0-3.5):   ~23-25% win - a real but modest lean
//   standout (3.5+):      ~33-42% win - a genuinely clear favorite
const TIGHT_MAX = 1.0
const STANDOUT_MIN = 3.5

/** How clearly the model's top pick is separated from the 2nd pick in
 * this race, based on their projected WPR gap - not the rank order alone,
 * which by itself carries far less signal (see the backtest above). Null
 * when the race doesn't have at least two projected runners (e.g. very
 * early acceptances, or a field of all first/lightly-raced starters). */
export function computeRaceConfidence(runners: Runner[]): RaceConfidence | null {
  const ranked = runners
    .filter((r) => r.projectedWpr != null && r.wprRank != null)
    .sort((a, b) => a.wprRank! - b.wprRank!)
  if (ranked.length < 2 || ranked[0].wprRank !== 1 || ranked[1].wprRank !== 2) return null

  const gap = ranked[0].projectedWpr! - ranked[1].projectedWpr!
  if (gap < TIGHT_MAX) return { tier: 'tight', label: 'Tight - top picks close', gap }
  if (gap < STANDOUT_MIN) return { tier: 'clear', label: 'Clear lead to 2nd', gap }
  return { tier: 'standout', label: 'Standout favorite', gap }
}
