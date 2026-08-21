import type { Runner } from '../types/domain'
import { overlayPct } from './format'

export type SortKey =
  | 'tab'
  | 'horse'
  | 'jockey'
  | 'trainer'
  | 'barrier'
  | 'settle'
  | 'peakWpr'
  | 'avgLast3'
  | 'projectedWpr'
  | 'wprPrice'
  | 'fixedPrice'
  | 'overlay'
  | 'finish'

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
  settle: 'asc',
  peakWpr: 'desc',
  avgLast3: 'desc',
  projectedWpr: 'desc',
  wprPrice: 'asc',
  fixedPrice: 'asc',
  overlay: 'desc',
  finish: 'asc',
}

function sortValue(runner: Runner, key: SortKey): number | string {
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
    case 'settle':
      return runner.avgSettledPos ?? Infinity
    case 'peakWpr':
      return runner.peakWpr ?? -Infinity
    case 'avgLast3':
      return runner.wprAvgLast3 ?? -Infinity
    case 'projectedWpr':
      return runner.projectedWpr ?? -Infinity
    case 'wprPrice':
      return runner.wprPrice ?? Infinity
    case 'fixedPrice':
      return runner.fixedWinPrice ?? Infinity
    case 'overlay':
      return overlayPct(runner.fixedWinPrice, runner.wprPrice) ?? -Infinity
    case 'finish':
      return runner.finishPosition ?? Infinity
  }
}

export function sortRunners(
  runners: Runner[],
  key: SortKey,
  direction: SortDirection,
): Runner[] {
  const sorted = [...runners].sort((a, b) => {
    const av = sortValue(a, key)
    const bv = sortValue(b, key)
    if (av < bv) return -1
    if (av > bv) return 1
    return 0
  })
  return direction === 'asc' ? sorted : sorted.reverse()
}
