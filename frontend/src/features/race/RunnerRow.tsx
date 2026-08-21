import type { Runner } from '../../types/domain'
import { fmtInt, fmtPct, fmtPrice, fmtWpr, overlayPct } from '../../lib/format'

interface RunnerRowProps {
  runner: Runner
  compact: boolean
  selected: boolean
  onClick: () => void
}

// A single responsive row - NOT a separate desktop-table/mobile-card pair
// (the current dashboard dual-renders every data grid; this is the
// consolidation the rebuild plan calls for). The grid's column template
// itself changes at the sm breakpoint via Tailwind classes, so the same
// DOM/children just reflow rather than existing twice.
export function RunnerRow({ runner, compact, selected, onClick }: RunnerRowProps) {
  const overlay = overlayPct(runner.fixedWinPrice, runner.wprPrice)
  const rowPadding = compact ? 'py-1.5' : 'py-2.5'

  return (
    <button
      type="button"
      onClick={onClick}
      className={`grid w-full grid-cols-[28px_1fr_repeat(3,56px)] items-center gap-x-2 gap-y-0.5 border-b border-line-soft px-2 text-left text-sm transition-colors sm:grid-cols-[28px_36px_1fr_48px_48px_56px_56px_60px_56px_56px_56px_48px] ${rowPadding} ${
        selected ? 'bg-emerald-bg' : 'hover:bg-bg'
      }`}
    >
      {runner.silkUrl ? (
        <img src={runner.silkUrl} alt="" className="h-5 w-5 rounded-sm object-contain" />
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
        {fmtWpr(runner.avgSettledPos)}
      </span>
      <span className="hidden text-right font-mono text-ink-mute sm:inline">
        {fmtWpr(runner.peakWpr)}
      </span>
      <span className="hidden text-right font-mono text-ink-mute sm:inline">
        {fmtWpr(runner.wprAvgLast3)}
      </span>
      <span className="text-right font-mono font-semibold text-emerald-deep">
        {fmtWpr(runner.projectedWpr)}
        {runner.projectionConfidence !== null && !compact && (
          <span className="ml-1 text-xs font-normal text-ink-faint">
            {fmtInt(runner.projectionConfidence)}%
          </span>
        )}
      </span>
      <span className="hidden text-right font-mono text-ink-mute sm:inline">
        {fmtPrice(runner.wprPrice)}
      </span>
      <span className="hidden text-right font-mono text-ink-mute sm:inline">
        {fmtPrice(runner.fixedWinPrice)}
      </span>
      <span
        className="hidden text-right font-mono text-ink-mute sm:inline"
        title="Overlay% is shown as information only - a past backtest on this project found it is not predictive on its own, so it is not styled as a buy signal."
      >
        {fmtPct(overlay)}
      </span>
      <span className="hidden text-right font-mono text-ink-mute sm:inline">
        {runner.finishPosition !== null ? fmtInt(runner.finishPosition) : ''}
      </span>
    </button>
  )
}
