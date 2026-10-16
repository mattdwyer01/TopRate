import type { Runner } from '../types/domain'
import type { EffectiveRunner } from './raceModel'
import type { CombinedRank } from './combinedRank'
import { spellPosition } from './spellPosition'
import { lastRunsRating } from './formRatings'

export type SortKey =
  | 'tab'
  | 'horse'
  | 'daysSince'
  | 'last3'
  | 'nett'
  | 'baseWpr'
  | 'adjustment'
  | 'speedMapAdj'
  | 'comboRank'
  | 'projectedWpr'
  | 'fixedPrice'
  | 'ratedPrice'
  | 'finish'

export type SortDirection = 'asc' | 'desc'

// Default sort direction per column - most
// numeric racing columns default to ascending-is-best (lower price/finish
// position = better), while WPR/rating columns default to
// descending-is-best (higher rating = better).
export const DEFAULT_DIRECTION: Record<SortKey, SortDirection> = {
  tab: 'asc',
  horse: 'asc',
  daysSince: 'asc',
  last3: 'desc',
  nett: 'desc',
  baseWpr: 'desc',
  adjustment: 'desc',
  speedMapAdj: 'desc',
  comboRank: 'asc',
  projectedWpr: 'desc',
  fixedPrice: 'asc',
  ratedPrice: 'asc',
  finish: 'asc',
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
  combo?: CombinedRank,
): number | string {
  switch (key) {
    case 'tab':
      return runner.tabNumber
    case 'horse':
      return runner.horse.toLowerCase()
    case 'daysSince':
      return spellPosition(runner.formHistory, raceDate ?? null).daysSince ?? Infinity
    case 'last3':
      return lastRunsRating(runner.formHistory, raceDate ?? null, 3)?.avg ?? -Infinity
    case 'nett':
      return runner.nett ?? -Infinity
    case 'baseWpr':
      return runner.baseWpr ?? -Infinity
    case 'adjustment':
      return runner.wprAdjustment ?? -Infinity
    case 'comboRank':
      return combo ? combo.rank + combo.mean / 1000 : Infinity
    case 'speedMapAdj':
      return effective?.speedMapAdj ?? -Infinity
    case 'projectedWpr':
      return effective?.effectiveProjectedWpr ?? runner.projectedWpr ?? -Infinity
    case 'fixedPrice':
      return runner.fixedWinPrice ?? Infinity
    case 'ratedPrice':
      return effective?.effectivePrice ?? Infinity
    case 'finish':
      return runner.finishPosition ?? Infinity
  }
}

export function sortRunners(
  runners: Runner[],
  key: SortKey,
  direction: SortDirection,
  effectiveByRunId?: Record<string, EffectiveRunner>,
  raceDate?: string,
  comboByRunId?: Map<string, CombinedRank>,
): Runner[] {
  const sorted = [...runners].sort((a, b) => {
    const av = sortValue(a, key, effectiveByRunId?.[a.runId], raceDate, comboByRunId?.get(a.runId))
    const bv = sortValue(b, key, effectiveByRunId?.[b.runId], raceDate, comboByRunId?.get(b.runId))
    if (av < bv) return -1
    if (av > bv) return 1
    return 0
  })
  return direction === 'asc' ? sorted : sorted.reverse()
}
