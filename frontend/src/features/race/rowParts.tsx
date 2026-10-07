import type { Runner } from '../../types/domain'
import type { EffectiveRunner } from '../../lib/raceModel'
import { SPEED_MAP_TINT_THRESHOLD } from '../../lib/raceModel'
import { fmtPrice } from '../../lib/format'
import { computePriceMove, MOVE_DISPLAY_THRESHOLD_PCT } from '../../lib/priceMove'
import { spellPosition } from '../../lib/spellPosition'

// Pieces shared by the desktop table row and the mobile card, so both read the same way.

export function fmtAdj(v: number | null | undefined): string {
  if (v == null) return '-'
  const f = v.toFixed(1)
  return v > 0 ? `+${f}` : f
}

export function adjClass(v: number | null | undefined): string {
  return v != null && v > 0.05 ? 'text-emerald-deep' : v != null && v < -0.05 ? 'text-rose' : 'text-ink-mute'
}

export function smClass(v: number | null | undefined): string {
  return v != null && v >= SPEED_MAP_TINT_THRESHOLD ? 'text-emerald-deep' : v != null && v <= -SPEED_MAP_TINT_THRESHOLD ? 'text-rose' : 'text-ink-mute'
}

export function ratingSuffix(v: number | null): string {
  return v == null ? '' : ` (${Math.round(v)})`
}

export function useRowFacts(runner: Runner, raceDate: string, effective?: EffectiveRunner) {
  const spell = spellPosition(runner.formHistory, raceDate)
  const move = computePriceMove(runner.openFixedPrice, runner.fixedWinPrice)
  const showMove = move != null && move.pctChange >= MOVE_DISPLAY_THRESHOLD_PCT
  const rtsClass = spell.label === 'FU' ? 'font-semibold text-amber' : spell.label === 'FS' ? 'font-semibold text-indigo' : 'text-ink-mute'
  const rtsTitle = spell.label === 'FS' ? 'First starter - no prior race starts' : spell.daysSince != null ? `${spell.daysSince} days since last run` : undefined
  const scratched = effective?.scratched ?? false
  const proj = scratched ? null : (effective?.effectiveProjectedWpr ?? runner.projectedWpr)
  // proj is already at the weight carried today (ATW, see computeEffectiveRace), the scale of the form table and the runner page.
  const off = effective?.atwOff ?? 0
  return { spell, move, showMove, rtsClass, rtsTitle, scratched, proj, atwOff: off, overridden: effective?.hasOverride ?? false }
}

export function PriceCell({ runner, scratched, move, showMove }: { runner: Runner; scratched: boolean; move: ReturnType<typeof computePriceMove>; showMove: boolean }) {
  return (
    <span className="inline-flex items-center justify-end font-mono">
      <span>{scratched ? 'SCR' : fmtPrice(runner.fixedWinPrice)}</span>
      <span
        className={`ml-1 w-2.5 flex-none text-center text-[10px] leading-none ${
          !scratched && showMove && move ? (move.direction === 'firmed' ? 'text-emerald-deep' : 'text-rose') : 'invisible'
        }`}
        title={!scratched && showMove && move ? `Opened ${fmtPrice(runner.openFixedPrice)}, ${move.direction} ${move.pctChange.toFixed(0)}%` : undefined}
      >
        {!scratched && showMove && move ? (move.direction === 'firmed' ? '▼' : '▲') : '▲'}
      </span>
    </span>
  )
}

export function FinishBadge({ pos }: { pos: number | null }) {
  if (pos == null) return null
  return (
    <span
      className={`inline-flex h-5 w-5 items-center justify-center rounded-full font-mono text-xs ${
        pos === 1 ? 'border border-amber-line bg-amber-bg font-semibold text-amber' : 'text-ink-mute'
      }`}
    >
      {pos}
    </span>
  )
}

export const BAND_BORDER: Record<'core' | 'inner' | 'outer' | 'none', string> = {
  core: 'border-l-emerald-deep',
  inner: 'border-l-emerald',
  outer: 'border-l-amber',
  none: 'border-l-transparent',
}

// 'FU' -> 'first-up', '2U' -> '2nd-up', 'FS' -> 'first start' for the runner row's detail line.
export function spellWord(label: string): string {
  if (label === 'FU') return 'first-up'
  if (label === 'FS') return 'first start'
  const m = /^(\d+)U$/.exec(label)
  if (!m) return label
  const n = Number(m[1])
  const suffix = n % 100 >= 11 && n % 100 <= 13 ? 'th' : ({ 1: 'st', 2: 'nd', 3: 'rd' } as Record<number, string>)[n % 10] ?? 'th'
  return `${n}${suffix}-up`
}
