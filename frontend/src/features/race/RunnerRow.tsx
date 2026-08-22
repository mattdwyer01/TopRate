import type { Runner } from '../../types/domain'
import type { EffectiveRunner } from '../../lib/raceModel'
import { fmtInt, fmtPrice, fmtWpr } from '../../lib/format'

interface RunnerRowProps {
  runner: Runner
  compact: boolean
  selected: boolean
  effective?: EffectiveRunner
  onClick: () => void
}

function fmtAdj(v: number | null): string {
  if (v == null) return '—'
  const f = v.toFixed(1)
  return v > 0 ? `+${f}` : f
}

// A single responsive row - NOT a separate desktop-table/mobile-card pair
// (the current dashboard dual-renders every data grid; this is the
// consolidation the rebuild plan calls for). The grid's column template
// itself changes at the sm breakpoint via Tailwind classes, so the same
// DOM/children just reflow rather than existing twice.
export function RunnerRow({ runner, compact, selected, effective, onClick }: RunnerRowProps) {
  const rowPadding = compact ? 'py-1.5' : 'py-2.5'
  const displayProj = effective?.effectiveProjectedWpr ?? runner.projectedWpr
  const displayPrice = effective?.effectivePrice ?? runner.wprPrice
  const overridden = effective?.hasOverride ?? false

  return (
    <button
      type="button"
      onClick={onClick}
      className={`grid w-full grid-cols-[40px_1fr_60px_56px_56px] items-center gap-x-2 gap-y-0.5 border-b border-line-soft px-2 text-left text-sm transition-colors sm:grid-cols-[44px_36px_1fr_48px_56px_56px_56px_56px_60px_56px_56px_48px] ${rowPadding} ${
        selected ? 'bg-emerald-bg' : 'hover:bg-bg'
      }`}
    >
      {runner.silkUrl ? (
        <img src={runner.silkUrl} alt="" className="h-9 w-9 rounded-sm object-contain" />
      ) : (
        <span />
      )}
      <span className="hidden font-mono text-ink-mute sm:inline">{runner.tabNumber}</span>
      <span className="min-w-0">
        <span className="block truncate font-medium text-ink">
          <span className="font-mono text-ink-mute sm:hidden">{runner.tabNumber}. </span>
          {runner.horse}
        </span>
        {!compact && (
          <span className="block truncate text-xs text-ink-faint">
            {runner.jockey} / {runner.trainer}
          </span>
        )}
      </span>
      <span className="hidden text-right font-mono text-ink-mute sm:inline">
        {fmtInt(runner.barrier)}
      </span>
      <span className="hidden text-right font-mono text-ink-mute sm:inline">
        {fmtWpr(runner.peakWpr)}
      </span>
      <span className="hidden text-right font-mono text-ink-mute sm:inline">
        {fmtWpr(runner.wprAvgLast3)}
      </span>
      <span className="hidden text-right font-mono text-ink-mute sm:inline">
        {fmtWpr(runner.baseWpr)}
      </span>
      <span
        className={`hidden text-right font-mono sm:inline ${
          runner.wprAdjustment != null && runner.wprAdjustment > 0
            ? 'text-emerald-deep'
            : runner.wprAdjustment != null && runner.wprAdjustment < 0
              ? 'text-rose'
              : 'text-ink-mute'
        }`}
      >
        {fmtAdj(runner.wprAdjustment)}
      </span>
      <span className="text-right font-mono font-semibold text-emerald-deep">
        {fmtWpr(displayProj)}
        {overridden && (
          <span className="ml-0.5 text-amber" title="Manually adjusted">
            *
          </span>
        )}
        {runner.projectionConfidence !== null && !compact && (
          <span className="ml-1 text-xs font-normal text-ink-faint">
            {fmtInt(runner.projectionConfidence)}%
          </span>
        )}
      </span>
      <span className="text-right font-mono text-ink-mute">
        {fmtPrice(displayPrice)}
      </span>
      <span className="text-right font-mono text-ink-mute">
        {fmtPrice(runner.fixedWinPrice)}
      </span>
      <span className="hidden text-right font-mono text-ink-mute sm:inline">
        {runner.finishPosition !== null ? fmtInt(runner.finishPosition) : ''}
      </span>
    </button>
  )
}
