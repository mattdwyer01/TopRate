import type { Race, Runner } from '../../types/domain'
import { fmtPrice } from '../../lib/format'
import { RecentRunsTable } from './RecentRunsTable'
import { ComparisonGrid } from './ComparisonGrid'

interface RunnerDetailPanelProps {
  runner: Runner
  race: Race
}

function ActualVsProjected({ runner }: { runner: Runner }) {
  if (runner.actualWpr == null) return null

  if (runner.projectedWpr == null) {
    return (
      <div className="rounded-lg border border-line bg-panel p-2.5 text-sm">
        <span className="font-mono text-lg font-semibold text-ink">{runner.actualWpr.toFixed(1)}</span>
        <span className="ml-2 text-ink-mute">actual WPR &middot; no projection was made for this runner</span>
      </div>
    )
  }

  const miss = runner.actualWpr - runner.projectedWpr
  const missAbs = Math.abs(miss)
  const missClass = missAbs >= 8 ? 'text-rose' : missAbs >= 4 ? 'text-amber' : 'text-emerald-deep'

  let rankText = ''
  if (runner.wprRank != null && runner.actualWprRank != null) {
    const rd = runner.actualWprRank - runner.wprRank
    rankText =
      rd === 0
        ? ' (exact)'
        : rd > 0
          ? ` (finished ${rd} lower)`
          : ` (finished ${-rd} higher)`
  }

  return (
    <div className="rounded-lg border border-line bg-panel p-2.5 text-sm">
      <span className="font-mono text-lg font-semibold text-ink">{runner.actualWpr.toFixed(1)}</span>
      <span className="ml-2 text-ink-mute">
        actual WPR &middot; projection missed by{' '}
        <span className={`font-mono font-medium ${missClass}`}>
          {miss > 0 ? '+' : ''}
          {miss.toFixed(1)}
        </span>
        {runner.wprRank != null && runner.actualWprRank != null && (
          <>
            {' '}
            &middot; rank predicted {runner.wprRank}, actual {runner.actualWprRank}
            {rankText}
          </>
        )}
      </span>
    </div>
  )
}

// Display-only projection diagnostics + evidence panel, shown when a runner
// row is clicked. Interactive controls (manual rating override, tempo
// override) are Phase 2 - this panel reflects the model's own numbers only.
export function RunnerDetailPanel({ runner, race }: RunnerDetailPanelProps) {
  const priceBits: string[] = []
  if (runner.wprPrice != null) priceBits.push(`WPR ${fmtPrice(runner.wprPrice)}`)
  if (runner.fixedWinPrice != null) priceBits.push(`Fixed ${fmtPrice(runner.fixedWinPrice)}`)
  if (runner.topratePrice != null) priceBits.push(`TR ${fmtPrice(runner.topratePrice)}`)
  priceBits.push(runner.startingPrice != null ? `SP ${fmtPrice(runner.startingPrice)}` : 'SP post-race')

  return (
    <div className="flex flex-col gap-3 rounded-lg border border-line bg-panel p-3 shadow-[var(--shadow-1)]">
      {runner.projectedWpr == null && (
        <div className="rounded-lg border border-amber-line bg-amber-bg p-2.5 text-sm text-amber">
          No projection for this runner.{' '}
          {runner.projectionDescription || 'Insufficient form history (under 3 prior runs).'}
        </div>
      )}

      <ActualVsProjected runner={runner} />

      {runner.projectionDescription && runner.projectedWpr != null && (
        <div className="rounded-lg bg-bg p-2.5 text-sm text-ink-soft">{runner.projectionDescription}</div>
      )}

      <RecentRunsTable runs={runner.recentRuns} peakRun={runner.peakRun} />

      <ComparisonGrid runner={runner} race={race} allRunners={race.runners} />

      <div className="text-sm text-ink-soft">
        <span className="mr-1.5 font-semibold text-ink">Price</span>
        {priceBits.join('  ·  ')}
      </div>

      <div className="border-t border-line-soft pt-2 text-xs text-ink-faint">
        Jockey {runner.jockey || '—'}
        {runner.jockeyRating != null ? ` (rt ${Math.round(runner.jockeyRating)})` : ''}
        {'  ·  '}
        Trainer {runner.trainer || '—'}
        {runner.trainerRating != null ? ` (rt ${Math.round(runner.trainerRating)})` : ''}
        {'  ·  '}
        Barrier {runner.barrier ?? '—'}
        <span className="ml-1.5 italic">(not used by the projection)</span>
      </div>
    </div>
  )
}
