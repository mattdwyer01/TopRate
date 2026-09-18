import type { Runner } from '../types/domain'
import { compositeScore, type EffectiveRunner } from './raceModel'
import { spellPosition } from './spellPosition'

export type SortKey =
  | 'tab'
  | 'horse'
  | 'jockey'
  | 'trainer'
  | 'barrier'
  | 'peakWpr'
  | 'daysSince'
  | 'baseWpr'
  | 'adjustment'
  | 'projectedWpr'
  | 'compositeScore'
  | 'toprateRating'
  | 'formFactor'
  | 'jockeyWinPct'
  | 'fixedPrice'
  | 'finish'
  | 'actualWpr'

export type SortDirection = 'asc' | 'desc'

// Matches the current dashboard's per-column default sort direction
// (raceSortState / sortGetters, toprate_html_v3.py L8860-8920) - most
// numeric racing columns default to ascending-is-best (lower price/finish
// position = better), while WPR/rating columns default to
// descending-is-best (higher rating = better).
export const DEFAULT_DIRECTION: Record<SortKey, SortDirection> = {
  tab: 'asc',
  horse: 'asc',
  jockey: 'asc',
  trainer: 'asc',
  barrier: 'asc',
  peakWpr: 'desc',
  daysSince: 'asc',
  baseWpr: 'desc',
  adjustment: 'desc',
  projectedWpr: 'desc',
  compositeScore: 'desc',
  toprateRating: 'desc',
  formFactor: 'desc',
  jockeyWinPct: 'desc',
  fixedPrice: 'asc',
  finish: 'asc',
  actualWpr: 'desc',
}

// effective: this runner's override-aware projected WPR / price, when a
// manual adjustment is active (see lib/raceModel.ts). Falls back to the
// raw model figures when there's no override, so sorting always reflects
// what the table actually displays.
function sortValue(
  runner: Runner,
  key: SortKey,
  effective?: EffectiveRunner,
  raceDate?: string,
): number | string {
  switch (key) {
    case 'tab':
      return runner.tabNumber
    case 'horse':
      return runner.horse.toLowerCase()
    case 'jockey':
      return runner.jockey.toLowerCase()
    case 'trainer':
      return runner.trainer.toLowerCase()
    case 'barrier':
      return runner.barrier ?? Infinity
    case 'peakWpr':
      return runner.peakWpr ?? -Infinity
    case 'daysSince':
      return spellPosition(runner.formHistory, raceDate ?? null).daysSince ?? Infinity
    case 'baseWpr':
      return runner.baseWpr ?? -Infinity
    case 'adjustment':
      return runner.wprAdjustment ?? -Infinity
    case 'projectedWpr':
      return effective?.effectiveProjectedWpr ?? runner.projectedWpr ?? -Infinity
    case 'compositeScore':
      return compositeScore(runner, effective?.effectiveProjectedWpr) ?? -Infinity
    case 'toprateRating':
      return runner.toprateRating ?? -Infinity
    case 'formFactor':
      return runner.formFactor ?? -Infinity
    case 'jockeyWinPct':
      return runner.jockeyWinPct90d ?? -Infinity
    case 'fixedPrice':
      return runner.fixedWinPrice ?? Infinity
    case 'finish':
      return runner.finishPosition ?? Infinity
    case 'actualWpr':
      return runner.actualWpr ?? -Infinity
  }
}

export function sortRunners(
  runners: Runner[],
  key: SortKey,
  direction: SortDirection,
  effectiveByRunId?: Record<string, EffectiveRunner>,
  raceDate?: string,
): Runner[] {
  const sorted = [...runners].sort((a, b) => {
    const av = sortValue(a, key, effectiveByRunId?.[a.runId], raceDate)
    const bv = sortValue(b, key, effectiveByRunId?.[b.runId], raceDate)
    if (av < bv) return -1
    if (av > bv) return 1
    return 0
  })
  return direction === 'asc' ? sorted : sorted.reverse()
}
