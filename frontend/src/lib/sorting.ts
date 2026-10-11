import type { Runner } from '../types/domain'
import type { EffectiveRunner } from './raceModel'
import { modelPrice, type Signal } from './betSignals'
import { spellPosition } from './spellPosition'

export type SortKey =
  | 'tab'
  | 'horse'
  | 'daysSince'
  | 'baseWpr'
  | 'adjustment'
  | 'projectedWpr'
  | 'fixedPrice'
  | 'modelPrice'
  | 'edge'
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
  baseWpr: 'desc',
  adjustment: 'desc',
  projectedWpr: 'desc',
  fixedPrice: 'asc',
  modelPrice: 'asc',
  edge: 'desc',
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
  signal?: Signal | null,
): number | string {
  switch (key) {
    case 'tab':
      return runner.tabNumber
    case 'horse':
      return runner.horse.toLowerCase()
    case 'daysSince':
      return spellPosition(runner.formHistory, raceDate ?? null).daysSince ?? Infinity
    case 'baseWpr':
      return runner.baseWpr ?? -Infinity
    case 'adjustment':
      return runner.wprAdjustment ?? -Infinity
    case 'projectedWpr':
      return effective?.effectiveProjectedWpr ?? runner.projectedWpr ?? -Infinity
    case 'fixedPrice':
      return runner.fixedWinPrice ?? Infinity
    case 'modelPrice':
      return modelPrice(signal?.m) ?? Infinity
    case 'edge':
      return signal?.e ?? -Infinity
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
  signalByRunId?: Record<string, Signal | null>,
): Runner[] {
  const sorted = [...runners].sort((a, b) => {
    const av = sortValue(a, key, effectiveByRunId?.[a.runId], raceDate, signalByRunId?.[a.runId])
    const bv = sortValue(b, key, effectiveByRunId?.[b.runId], raceDate, signalByRunId?.[b.runId])
    if (av < bv) return -1
    if (av > bv) return 1
    return 0
  })
  return direction === 'asc' ? sorted : sorted.reverse()
}
