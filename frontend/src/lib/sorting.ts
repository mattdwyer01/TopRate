import type { Runner } from '../types/domain'
import type { EffectiveRunner } from './raceModel'
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
  | 'wprPrice'
  | 'blendPrice'
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
  wprPrice: 'asc',
  blendPrice: 'asc',
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
    case 'wprPrice':
      return effective?.effectivePrice ?? runner.wprPrice ?? Infinity
    case 'blendPrice':
      // Not override-aware - the manual what-if slider adjusts this
      // horse's WPR only, and blendPrice is a blend of several other
      // signals too (speed/form-provider ratings, trailing jockey/trainer
      // form) that a WPR-only override can't meaningfully recompute.
      return runner.blendPrice ?? Infinity
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
