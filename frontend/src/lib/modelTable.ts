import type { Runner } from '../types/domain'
import type { RMBlend, RMRunner } from './racingModel'
import { spellPosition } from './spellPosition'

// Racing Model view of the race ratings table (RaceDetail + features/race/ModelRunnerRow.tsx): its columns,
// sort values and grid tracks. The tracks are shared by the header rows and ModelRunnerRow so they never drift.

export type ModelSortKey = 'tab' | 'horse' | 'daysSince' | 'r' | 'v' | 'settle' | 'l' | 'pv' | 'model' | 'blend' | 'fixed' | 'edge' | 'finish'

export interface ModelRow {
  runner: Runner
  m: RMRunner | undefined
  b: RMBlend | undefined
  settleRank: number | null
}

export const MODEL_GRID = {
  desktop: 'sm:grid-cols-[44px_36px_1fr_48px_56px_56px_44px_52px_60px_68px_68px_76px_56px_52px]',
  full: 'gap-x-[3px] grid-cols-[40px_minmax(64px,1fr)_28px_16px_28px_42px_42px_30px_18px]',
  compact: 'gap-x-1 grid-cols-[40px_minmax(80px,1fr)_34px_52px_60px_36px_20px]',
}

// label: desktop header; short: mobile header (only columns shown on mobile have one); dir: first-click
// direction (best first); compact: shown in mobile Compact as well as Full.
export const MODEL_COLUMNS: {
  key: ModelSortKey
  label: string
  short?: string
  title: string
  dir: 'asc' | 'desc'
  compact?: boolean
}[] = [
  { key: 'tab', label: '#', title: 'Saddlecloth', dir: 'asc' },
  { key: 'horse', label: 'Horse', short: 'Horse', title: 'Horse', dir: 'asc', compact: true },
  { key: 'daysSince', label: 'RTS', title: 'Runs this spell', dir: 'asc' },
  { key: 'r', label: 'Rating', short: 'Rtg', title: 'Racing Model projected rating (WPR points)', dir: 'desc', compact: true },
  { key: 'v', label: 'vs Field', title: 'Rating vs the field average', dir: 'desc' },
  { key: 'settle', label: 'Settle', short: 'St', title: 'Projected position at the 800m (1 = leader)', dir: 'asc' },
  { key: 'l', label: 'Leads', title: 'Chance of leading', dir: 'desc' },
  { key: 'pv', label: 'Pos Val', short: 'PV', title: 'Position value: WPR points the projected position, width and pace are worth vs the race; ◆ = top 10%', dir: 'desc' },
  { key: 'model', label: 'Model $', title: 'Racing Model alone (no market input)', dir: 'asc' },
  { key: 'blend', label: 'Blend $', short: 'Bld $', title: 'Racing Model blended with the current fixed price', dir: 'asc', compact: true },
  { key: 'fixed', label: 'Fixed $', short: 'Fixed $', title: 'Current TAB fixed price', dir: 'asc', compact: true },
  { key: 'edge', label: 'Edge', short: 'Edge', title: 'Blend probability x fixed price - 1', dir: 'desc', compact: true },
  { key: 'finish', label: 'FP', short: 'FP', title: 'Finish position', dir: 'asc', compact: true },
]

export function modelSortValue(x: ModelRow, key: ModelSortKey, raceDate: string): number | string | null {
  switch (key) {
    case 'tab':
      return x.runner.tabNumber ?? null
    case 'horse':
      return x.runner.horse
    case 'daysSince':
      return spellPosition(x.runner.formHistory, raceDate).daysSince ?? null
    case 'r':
      return x.m?.r ?? null
    case 'v':
      return x.m?.v ?? null
    case 'settle':
      return x.settleRank
    case 'l':
      return x.m?.l ?? null
    case 'pv':
      return x.m?.pv ?? null
    case 'model':
      return x.m?.p ? 1 / x.m.p : null
    case 'blend':
      return x.b?.blendPrice ?? null
    case 'fixed':
      return x.runner.fixedWinPrice ?? null
    case 'edge':
      return x.b?.edge ?? null
    case 'finish':
      return x.runner.finishPosition ?? null
  }
}
