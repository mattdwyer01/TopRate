import { useEffect, useRef, useState } from 'react'
import type { Race, Runner } from '../../types/domain'
import type { EffectiveRunner } from '../../lib/raceModel'
import { fmtPrice, fmtWpr } from '../../lib/format'
import { computePriceMove } from '../../lib/priceMove'
import { useBodyScrollLock, useFocusTrap } from '../../lib/modalA11y'
import { RecentRunsTable } from './RecentRunsTable'
import { ComparisonGrid } from './ComparisonGrid'
import { CareerStats } from './CareerStats'
import { ResultVsProjection } from './ResultVsProjection'

interface RunnerDetailModalProps {
  runner: Runner
  race: Race
  effective?: EffectiveRunner
  deltaValue: number | null
  baseValue: number | null
  onSetDelta: (v: number | null) => void
  onSetBase: (v: number | null) => void
  onToggleScratch: () => void
  onClose: () => void
  onPrev: () => void
  onNext: () => void
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
  onToggleScratch,
  onClose,
  onPrev,
  onNext,
}: RunnerDetailModalProps) {
  const scratched = effective?.scratched ?? false
  const [scrolled, setScrolled] = useState(false)
  const scrollRef = useRef<HTMLDivElement>(null)

  useBodyScrollLock()
  useFocusTrap(scrollRef)

  useEffect(() => {
    function onKey(e: KeyboardEvent) {
      if (e.key === 'Escape') onClose()
      else if (e.key === 'ArrowLeft') onPrev()
      else if (e.key === 'ArrowRight') onNext()
    }
    window.addEventListener('keydown', onKey)
    return () => window.removeEventListener('keydown', onKey)
  }, [onClose, onPrev, onNext])

  // Reset scroll position (and the mini-header state riding on it) when
  // navigating to a different runner - the scrollable panel element
  // persists across prev/next, so without this a scrolled-down view would
  // carry over to the next horse.
  useEffect(() => {
    scrollRef.current?.scrollTo({ top: 0 })
    setScrolled(false)
  }, [runner.runId])

  // Scratched: force both to null rather than falling back to the model's
  // raw (pre-scratch) values - same reasoning as RunnerRow's displayProj/
  // displayPrice (effective.effectiveProjectedWpr is explicitly null once
  // scratched, and ?? would otherwise treat that the same as "no override").
  const effectivePrice = scratched ? null : (effective?.effectivePrice ?? runner.wprPrice)
  const priceBitsBefore: string[] = []
  if (effectivePrice != null) priceBitsBefore.push(`WPR ${fmtPrice(effectivePrice)}`)
  const priceBitsAfter: string[] = []
  if (runner.topratePrice != null) priceBitsAfter.push(`TR ${fmtPrice(runner.topratePrice)}`)
  priceBitsAfter.push(runner.startingPrice != null ? `SP ${fmtPrice(runner.startingPrice)}` : 'SP post-race')
  // Fixed price gets its own bit below (not folded into the plain-text
  // arrays above) so the raceday move vs open_price can be colour-coded.
  const fixedMove = computePriceMove(runner.openFixedPrice, runner.fixedWinPrice)

  const effectiveWpr = scratched ? null : (effective?.effectiveProjectedWpr ?? runner.projectedWpr)
  const hasOverride = effective?.hasOverride ?? false

  return (
    <div
      className="fixed inset-0 z-40 flex items-start justify-center overflow-y-auto bg-ink/60 p-3 sm:items-center sm:p-6"
      onClick={onClose}
    >
      <div
        ref={scrollRef}
        role="dialog"
        aria-modal="true"
        aria-label={`${runner.horse} detail`}
        tabIndex={-1}
        className="flex max-h-full w-full max-w-6xl flex-col overflow-y-auto rounded-lg bg-panel shadow-[var(--shadow-2)] outline-none"
        onClick={(e) => e.stopPropagation()}
        onScroll={(e) => setScrolled(e.currentTarget.scrollTop > 120)}
      >
        <div className="sticky top-0 z-10 flex items-center gap-2.5 border-b border-line bg-panel px-3 py-2.5">
          {runner.silkUrl ? (
            <img src={runner.silkUrl} alt="" className="h-10 w-10 shrink-0 rounded-sm object-contain" />
          ) : (
            <div className="h-10 w-10 shrink-0 rounded-sm bg-bg" />
          )}
          <div className="min-w-0 flex-1">
            <div className={`truncate text-base font-semibold text-ink ${scratched ? 'line-through' : ''}`}>
              {runner.tabNumber}. {runner.horse}
            </div>
            {scrolled ? (
              <div className="flex items-center gap-2 truncate text-xs">
                <span className="font-mono font-bold text-emerald-deep">{fmtWpr(effectiveWpr)}</span>
                <span className="text-ink-faint">effective WPR</span>
                {effectivePrice != null && (
                  <span className="font-mono text-ink-mute">{fmtPrice(effectivePrice)}</span>
                )}
              </div>
            ) : (
              <div className="truncate text-xs text-ink-faint">
                {runner.jockey} / {runner.trainer}
              </div>
            )}
          </div>
          <div className="flex shrink-0 items-center gap-1">
            <button
              type="button"
              onClick={onToggleScratch}
              className={`rounded-md border px-2 text-xs font-semibold transition-colors ${
                scratched
                  ? 'border-rose-line bg-rose-bg text-rose'
                  : 'border-line text-ink-mute hover:bg-bg hover:text-ink'
              }`}
            >
              {scratched ? 'Scratched' : 'Scratch'}
            </button>
            <button
              type="button"
              onClick={onPrev}
              className="flex h-8 w-8 items-center justify-center rounded-md border border-line text-ink-mute transition-colors hover:bg-bg hover:text-ink"
              aria-label="Previous runner"
            >
              ‹
            </button>
            <button
              type="button"
              onClick={onNext}
              className="flex h-8 w-8 items-center justify-center rounded-md border border-line text-ink-mute transition-colors hover:bg-bg hover:text-ink"
              aria-label="Next runner"
            >
              ›
            </button>
            <button
              type="button"
              onClick={onClose}
              className="ml-1 flex h-8 w-8 items-center justify-center rounded-md text-ink-mute transition-colors hover:bg-bg hover:text-ink"
              aria-label="Close"
            >
              ✕
            </button>
          </div>
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
              {scratched ? (
                <span className="font-mono text-2xl font-bold text-rose">SCR</span>
              ) : (
                <span className="font-mono text-2xl font-bold text-emerald-deep">{fmtWpr(effectiveWpr)}</span>
              )}
              <span className="text-xs text-ink-mute">
                {scratched ? 'scratched - out of the field pricing' : 'effective WPR'}
              </span>
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

            {/* One line instead of 4 boxed tiles - Base+Adjustment=Model
                projection is simple arithmetic that doesn't need a box each,
                and "Model projection" duplicated the big headline number
                above whenever there's no manual override (the common case;
                the hasOverride block above already surfaces the model's own
                number separately for the case where it doesn't). */}
            <div className="mt-2 flex flex-wrap items-center gap-x-3 gap-y-0.5 text-xs text-ink-mute">
              <span>
                <span className="font-mono font-semibold text-ink">{fmtWpr(runner.baseWpr)}</span> base
              </span>
              {runner.wprAdjustment != null && (
                <span>
                  <span className="font-mono font-semibold text-ink">
                    {runner.wprAdjustment > 0 ? '+' : ''}
                    {runner.wprAdjustment.toFixed(1)}
                  </span>{' '}
                  adjustment
                </span>
              )}
              {runner.projectionConfidence != null && (
                <span>
                  <span className="font-mono font-semibold text-ink">{runner.projectionConfidence}%</span>{' '}
                  confidence
                </span>
              )}
            </div>
            {runner.projectionDescription && runner.projectedWpr != null && (
              <p className="mt-2 border-t border-line-soft pt-2 text-sm text-ink-soft">
                {runner.projectionDescription}
              </p>
            )}
          </div>

          {/* CareerStats keeps a natural (not stretched) table width, so a
              second panel rides alongside it on wide screens instead of
              leaving the rest of the row empty. Once the runner has actually
              raced, "how did the projection do" (ResultVsProjection) is the
              more useful question than the pre-race "does today's shape suit
              it" one (ComparisonGrid) - swap rather than stack both, and
              fold the old inline actual-vs-projected summary line into it so
              that comparison isn't shown twice. */}
          <div className="flex flex-wrap items-start gap-3">
            <div className="min-w-[280px] flex-1">
              <CareerStats runner={runner} race={race} />
            </div>
            <div className="min-w-[280px] flex-[1.4]">
              {runner.actualWpr != null ? (
                // Price folds in here for a resulted runner - "what the
                // market actually paid" pairs naturally with "what actually
                // happened", and it fills out this card's height (shorter
                // than CareerStats otherwise) instead of leaving it blank.
                <ResultVsProjection
                  runner={runner}
                  priceBitsBefore={priceBitsBefore}
                  priceBitsAfter={priceBitsAfter}
                  fixedMove={fixedMove}
                />
              ) : (
                <ComparisonGrid runner={runner} race={race} allRunners={race.runners} />
              )}
            </div>
          </div>

          <RecentRunsTable runs={runner.recentRuns} peakRun={runner.peakRun} />

          {runner.actualWpr == null && (
            <div className="text-sm text-ink-soft">
              <span className="mr-1.5 font-semibold text-ink">Price</span>
              {priceBitsBefore.length > 0 && `${priceBitsBefore.join('  ·  ')}  ·  `}
              {runner.fixedWinPrice != null && (
                <>
                  Fixed {fmtPrice(runner.fixedWinPrice)}
                  {fixedMove && (
                    <span className={fixedMove.direction === 'firmed' ? 'text-emerald-deep' : 'text-rose'}>
                      {' '}
                      ({fixedMove.direction} {fixedMove.pctChange.toFixed(0)}% from{' '}
                      {fmtPrice(runner.openFixedPrice)} at open)
                    </span>
                  )}
                  {'  ·  '}
                </>
              )}
              {priceBitsAfter.join('  ·  ')}
            </div>
          )}

          {/* Jockey/trainer names are already in the header subtitle - only
              their ratings and barrier are new information here. */}
          <div className="border-t border-line-soft pt-2 text-xs text-ink-faint">
            Jockey rating {runner.jockeyRating != null ? Math.round(runner.jockeyRating) : '—'}
            {'  ·  '}
            Trainer rating {runner.trainerRating != null ? Math.round(runner.trainerRating) : '—'}
            {'  ·  '}
            Barrier {runner.barrier ?? '—'}
            <span className="ml-1.5 italic">(not used by the projection)</span>
          </div>
        </div>
      </div>
    </div>
  )
}
