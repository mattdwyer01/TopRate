import { useEffect } from 'react'
import type { Race, Runner } from '../../types/domain'
import type { EffectiveRunner } from '../../lib/raceModel'
import { fmtPrice, fmtWpr } from '../../lib/format'
import { RecentRunsTable } from './RecentRunsTable'
import { ComparisonGrid } from './ComparisonGrid'

interface RunnerDetailModalProps {
  runner: Runner
  race: Race
  effective?: EffectiveRunner
  deltaValue: number | null
  baseValue: number | null
  onSetDelta: (v: number | null) => void
  onSetBase: (v: number | null) => void
  onClose: () => void
  onPrev: () => void
  onNext: () => void
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
    rankText = rd === 0 ? ' (exact)' : rd > 0 ? ` (finished ${rd} lower)` : ` (finished ${-rd} higher)`
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

// Full-screen overlay for a runner's projection detail. Replaces the old
// inline-below-table panel so it doesn't push the rest of the table around,
// and adds prev/next navigation plus the manual-override controls
// (adjustment delta always; a base-WPR entry when the model has no
// projection at all). Both write through to lib/wprOverrides and feed
// lib/raceModel's field-wide effective recompute, so a change here
// immediately shows up in every other runner's price too.
export function RunnerDetailModal({
  runner,
  race,
  effective,
  deltaValue,
  baseValue,
  onSetDelta,
  onSetBase,
  onClose,
  onPrev,
  onNext,
}: RunnerDetailModalProps) {
  useEffect(() => {
    function onKey(e: KeyboardEvent) {
      if (e.key === 'Escape') onClose()
      else if (e.key === 'ArrowLeft') onPrev()
      else if (e.key === 'ArrowRight') onNext()
    }
    window.addEventListener('keydown', onKey)
    return () => window.removeEventListener('keydown', onKey)
  }, [onClose, onPrev, onNext])

  const priceBits: string[] = []
  const effectivePrice = effective?.effectivePrice ?? runner.wprPrice
  if (effectivePrice != null) priceBits.push(`WPR ${fmtPrice(effectivePrice)}`)
  if (runner.fixedWinPrice != null) priceBits.push(`Fixed ${fmtPrice(runner.fixedWinPrice)}`)
  if (runner.topratePrice != null) priceBits.push(`TR ${fmtPrice(runner.topratePrice)}`)
  priceBits.push(runner.startingPrice != null ? `SP ${fmtPrice(runner.startingPrice)}` : 'SP post-race')

  const effectiveWpr = effective?.effectiveProjectedWpr ?? runner.projectedWpr
  const hasOverride = effective?.hasOverride ?? false

  return (
    <div
      className="fixed inset-0 z-40 flex items-start justify-center overflow-y-auto bg-ink/60 p-3 sm:items-center sm:p-6"
      onClick={onClose}
    >
      <div
        className="flex max-h-full w-full max-w-3xl flex-col overflow-y-auto rounded-lg bg-panel shadow-[var(--shadow-2)]"
        onClick={(e) => e.stopPropagation()}
      >
        <div className="sticky top-0 z-10 flex items-center gap-2 border-b border-line bg-panel px-3 py-2.5">
          <button
            type="button"
            onClick={onPrev}
            className="flex h-8 w-8 shrink-0 items-center justify-center rounded-md border border-line text-ink-mute transition-colors hover:bg-bg hover:text-ink"
            aria-label="Previous runner"
          >
            ‹
          </button>
          <div className="min-w-0 flex-1">
            <div className="truncate text-base font-semibold text-ink">
              {runner.tabNumber}. {runner.horse}
            </div>
            <div className="truncate text-xs text-ink-faint">
              {runner.jockey} / {runner.trainer}
            </div>
          </div>
          <button
            type="button"
            onClick={onNext}
            className="flex h-8 w-8 shrink-0 items-center justify-center rounded-md border border-line text-ink-mute transition-colors hover:bg-bg hover:text-ink"
            aria-label="Next runner"
          >
            ›
          </button>
          <button
            type="button"
            onClick={onClose}
            className="ml-1 flex h-8 w-8 shrink-0 items-center justify-center rounded-md text-ink-mute transition-colors hover:bg-bg hover:text-ink"
            aria-label="Close"
          >
            ✕
          </button>
        </div>

        <div className="flex flex-col gap-3 p-3">
          {runner.projectedWpr == null && (
            <div className="rounded-lg border border-amber-line bg-amber-bg p-2.5 text-sm text-amber">
              No projection for this runner.{' '}
              {runner.projectionDescription || 'Insufficient form history (under 3 prior runs).'}
            </div>
          )}

          <div className="rounded-lg bg-bg p-2.5">
            <div className="flex flex-wrap items-baseline gap-x-3 gap-y-1">
              <span className="font-mono text-2xl font-bold text-emerald-deep">{fmtWpr(effectiveWpr)}</span>
              <span className="text-xs text-ink-mute">effective WPR</span>
              {hasOverride && (
                <span className="rounded-full bg-amber/15 px-2 py-0.5 text-xs font-medium text-amber">
                  manually adjusted
                </span>
              )}
            </div>
            {hasOverride && (
              <div className="mt-1 text-xs text-ink-mute">
                model {fmtWpr(runner.projectedWpr ?? baseValue)}
                {deltaValue != null && deltaValue !== 0 && (
                  <>
                    {' '}
                    {deltaValue > 0 ? '+' : ''}
                    {deltaValue.toFixed(1)} your adjustment
                  </>
                )}
              </div>
            )}

            {runner.projectedWpr == null && (
              <label className="mt-2 flex items-center gap-2 text-sm text-ink-soft">
                Base WPR
                <input
                  type="number"
                  step="0.1"
                  value={baseValue ?? ''}
                  onChange={(e) => onSetBase(e.target.value === '' ? null : Number(e.target.value))}
                  placeholder="e.g. 72.0"
                  className="w-24 rounded-md border border-line bg-panel px-2 py-1 font-mono text-sm"
                />
                <span className="text-xs text-ink-faint">no model projection - enter your own to rate this horse</span>
              </label>
            )}

            <label className="mt-2 flex items-center gap-2 text-sm text-ink-soft">
              Your adjustment
              <input
                type="number"
                step="0.1"
                value={deltaValue ?? ''}
                onChange={(e) => onSetDelta(e.target.value === '' ? null : Number(e.target.value))}
                placeholder="0.0"
                className="w-24 rounded-md border border-line bg-panel px-2 py-1 font-mono text-sm"
              />
              {(deltaValue != null || baseValue != null) && (
                <button
                  type="button"
                  onClick={() => {
                    onSetDelta(null)
                    onSetBase(null)
                  }}
                  className="text-xs text-ink-mute underline hover:text-ink"
                >
                  Clear
                </button>
              )}
            </label>
          </div>

          <ActualVsProjected runner={runner} />

          {runner.projectionDescription && runner.projectedWpr != null && (
            <div className="rounded-lg bg-bg p-2.5 text-sm text-ink-soft">{runner.projectionDescription}</div>
          )}

          <div className="grid grid-cols-2 gap-2 text-sm sm:grid-cols-4">
            <div className="rounded-lg border border-line p-2">
              <div className="text-xs text-ink-faint">Base</div>
              <div className="font-mono font-semibold text-ink">{fmtWpr(runner.baseWpr)}</div>
            </div>
            <div className="rounded-lg border border-line p-2">
              <div className="text-xs text-ink-faint">Adjustment</div>
              <div className="font-mono font-semibold text-ink">
                {runner.wprAdjustment != null
                  ? `${runner.wprAdjustment > 0 ? '+' : ''}${runner.wprAdjustment.toFixed(1)}`
                  : '—'}
              </div>
            </div>
            <div className="rounded-lg border border-line p-2">
              <div className="text-xs text-ink-faint">Model projection</div>
              <div className="font-mono font-semibold text-ink">{fmtWpr(runner.projectedWpr)}</div>
            </div>
            <div className="rounded-lg border border-line p-2">
              <div className="text-xs text-ink-faint">Confidence</div>
              <div className="font-mono font-semibold text-ink">
                {runner.projectionConfidence != null ? `${runner.projectionConfidence}%` : '—'}
              </div>
            </div>
          </div>

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
      </div>
    </div>
  )
}
