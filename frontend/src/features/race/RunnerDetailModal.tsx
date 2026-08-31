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
import { PriceMovementChart } from './PriceMovementChart'

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
  priceBitsAfter.push(runner.startingPrice != null ? `SP ${fmtPrice(runner.startingPrice)}` : 'SP post-race')
  // Fixed price gets its own bit below (not folded into the plain-text
  // arrays above) so the raceday move vs open_price can be colour-coded.
  const fixedMove = computePriceMove(runner.openFixedPrice, runner.fixedWinPrice)

  const effectiveWpr = scratched ? null : (effective?.effectiveProjectedWpr ?? runner.projectedWpr)
  const hasOverride = effective?.hasOverride ?? false
  const hasPriceInfo =
    runner.priceSeries.length >= 2 ||
    runner.fixedWinPrice != null ||
    effectivePrice != null ||
    runner.topratePrice != null ||
    runner.startingPrice != null

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
                <span className="font-mono font-bold text-emerald-deep">{fmtPrice(runner.blendPrice)}</span>
                <span className="text-ink-faint">Model $</span>
                {runner.edgeScore != null && runner.edgeScore >= 0.08 && (
                  <span className="rounded bg-emerald px-1 font-mono text-[10px] font-semibold text-white">
                    +{(runner.edgeScore * 100).toFixed(0)}% EDGE
                  </span>
                )}
              </div>
            ) : (
              <div className="truncate text-xs text-ink-faint">
                {runner.jockey}
                {runner.jockeyRating != null ? ` (${Math.round(runner.jockeyRating)})` : ''} / {runner.trainer}
                {runner.trainerRating != null ? ` (${Math.round(runner.trainerRating)})` : ''}
              </div>
            )}
          </div>
          <div className="flex shrink-0 items-center gap-1">
            {runner.dataScratched ? (
              // Real, data-confirmed scratch - not a toggle (nothing to
              // undo here, see RaceDetail's effectiveScratched), solid fill
              // so it reads as a fact rather than the manual what-if toggle.
              <span
                title="Scratched (confirmed by TopRate)"
                className="rounded-md bg-rose px-2 py-1 text-xs font-semibold text-white"
              >
                Scratched
              </span>
            ) : (
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
            )}
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
          {runner.blendProb == null && (
            <div className="rounded-lg border border-amber-line bg-amber-bg p-2.5 text-sm text-amber">
              No model estimate for this runner. Insufficient form/speed/rating history to blend a probability.
            </div>
          )}

          {/* PRIMARY: the blend score (Model $ / win probability / rank) -
              promoted here Aug 2026 after a held-out backtest found it beats
              WPR-alone ranking on both strike rate and ROI (see
              wpr_projection.compute_edge_scores). The WPR-points breakdown
              this used to lead with (base/adjustment/projection, plus the
              manual override controls) moved to "WPR rating detail" below -
              still there, just no longer the headline. */}
          <div className="rounded-lg bg-bg p-2.5">
            <div className="flex flex-wrap items-center justify-between gap-x-4 gap-y-1.5">
              <div className="flex flex-wrap items-baseline gap-x-3 gap-y-1">
                {scratched ? (
                  <span className="font-mono text-2xl font-bold text-rose">SCR</span>
                ) : (
                  <span className="font-mono text-2xl font-bold text-emerald-deep">{fmtPrice(runner.blendPrice)}</span>
                )}
                <span className="text-xs text-ink-mute">
                  {scratched
                    ? runner.dataScratched
                      ? 'confirmed scratched - out of the field pricing'
                      : 'manually scratched - out of the field pricing'
                    : 'Model $'}
                </span>
                {!scratched && runner.blendProb != null && (
                  <span className="text-xs text-ink-mute">
                    <span className="font-mono font-semibold text-ink">{(runner.blendProb * 100).toFixed(0)}%</span>{' '}
                    win chance
                  </span>
                )}
                {!scratched && runner.blendRank != null && (
                  <span className="text-xs text-ink-mute">
                    rank <span className="font-mono font-semibold text-ink">{runner.blendRank}</span>
                  </span>
                )}
              </div>
              <div className="flex flex-wrap items-center gap-x-3 gap-y-1 text-xs text-ink-mute">
                {runner.fixedWinPrice != null && (
                  <span>
                    <span className="font-mono font-semibold text-ink">{fmtPrice(runner.fixedWinPrice)}</span> fixed
                  </span>
                )}
                <span>
                  <span className="font-mono font-semibold text-ink">
                    {runner.startingPrice != null ? fmtPrice(runner.startingPrice) : '—'}
                  </span>{' '}
                  SP
                </span>
              </div>
            </div>
            {runner.edgeScore != null && (
              <div
                className={`mt-2 flex items-center gap-2 rounded-md border px-2 py-1.5 text-xs ${
                  runner.edgeScore >= 0.08
                    ? 'border-emerald-line bg-emerald-bg/40 text-ink'
                    : 'border-line-soft text-ink-mute'
                }`}
              >
                <span
                  className={`font-mono font-semibold ${runner.edgeScore >= 0.08 ? 'text-emerald-deep' : 'text-ink'}`}
                >
                  {runner.edgeScore >= 0 ? '+' : ''}
                  {(runner.edgeScore * 100).toFixed(1)}% edge
                </span>
                <span>
                  ({(runner.edgeModelProb! * 100).toFixed(0)}% model vs {(runner.edgeMarketProb! * 100).toFixed(0)}%
                  market implied win chance){runner.edgeScore >= 0.08 ? ' - crosses the 8%+ overlay cutoff' : ''}. An
                  experimental signal - a walk-forward check (30 daily refits, Aug 2026) came back statistically
                  indistinguishable from break-even (ROI 95% CI roughly -19% to +22%), not proven profitable.
                </span>
              </div>
            )}
          </div>

          {/* SECONDARY: the WPR-only rating (projection/base/adjustment,
              confidence, description) and the manual override controls.
              Collapsed by default via <details> - a manual override here
              only ever adjusts WPR, it does NOT recompute Model $ above
              (which blends several other signals too), so this section is
              explicitly scoped as "WPR" throughout to avoid implying it does. */}
          <details className="rounded-lg border border-line-soft bg-panel">
            <summary className="cursor-pointer select-none px-2.5 py-2 text-sm font-medium text-ink-mute hover:text-ink">
              WPR rating detail{hasOverride ? ' (manually adjusted)' : ''}
            </summary>
            <div className="border-t border-line-soft p-2.5">
              <div className="flex flex-wrap items-center justify-between gap-x-4 gap-y-1.5">
                <div className="flex flex-wrap items-baseline gap-x-3 gap-y-1">
                  <span className="font-mono text-lg font-bold text-ink">{fmtWpr(effectiveWpr)}</span>
                  <span className="text-xs text-ink-mute">effective WPR</span>
                  {hasOverride && (
                    <span className="rounded-full bg-amber/15 px-2 py-0.5 text-xs font-medium text-amber">
                      manually adjusted
                    </span>
                  )}
                </div>
                <div className="flex flex-wrap items-center gap-x-3 gap-y-1">
                  <label className="flex items-center gap-2 text-sm text-ink-soft">
                    Your adjustment
                    <input
                      type="number"
                      step="0.1"
                      value={deltaValue ?? ''}
                      onChange={(e) => onSetDelta(e.target.value === '' ? null : Number(e.target.value))}
                      placeholder="0.0"
                      className="w-20 rounded-md border border-line bg-panel px-2 py-1 font-mono text-sm"
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
                  {effectivePrice != null && (
                    <span className="text-xs text-ink-mute">
                      <span className="font-mono font-semibold text-ink">{fmtPrice(effectivePrice)}</span> WPR $
                    </span>
                  )}
                  {runner.wprRank != null && (
                    <span className="text-xs text-ink-mute">
                      WPR rank <span className="font-mono font-semibold text-ink">{runner.wprRank}</span>
                    </span>
                  )}
                </div>
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
                  {' - note this only feeds the WPR figures on this line, not Model $ above'}
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
          </details>

          {/* ResultVsProjection and/or PriceMovementChart ride alongside
              CareerStats from the sm breakpoint up (fills the space that
              would otherwise sit blank beside CareerStats's natural,
              not-stretched table width). Below sm (every phone - even a
              430px-wide one has only ~380px left here after modal/card
              padding), CareerStats goes full-width on its own row:
              its 6-column table needs ~300px+ to show Peak/Avg/vs Career/
              Adj/Trend without squeezing, which doesn't fit next to
              Price/Result on a phone however thin those two are shrunk.
              Price and Result, in contrast, have no such width floor
              (a price figure, a slider, a predicted/actual pair - all
              shrink cleanly), so they share ONE row 50/50 on mobile
              instead of each also going full-width and stacking - full
              stacking for all three burned too much vertical scroll
              (user feedback, Aug 2026) for two cards that don't need it.
              The `sm:contents` wrapper drops its own box at sm and up so
              its children rejoin CareerStats in a single flex row, same
              as before.
              ResultVsProjection is now always rendered (not conditional on
              having a result) - it shows its own empty/placeholder state
              pre-race, so this row's layout doesn't reflow once a race
              results (user feedback: pre-race and post-race should look
              the same). PriceMovementChart is the ONE place a runner's
              price information lives (folds in WPR $/TR $/SP too) - no
              more separate Price line further down, pre-race or post-race.
              ComparisonGrid always lives under Recent runs now (moved
              there per feedback), not paired up here, so its position
              doesn't move around depending on whether the race has
              resulted. */}
          <div className="flex flex-wrap items-start gap-3">
            <div className="w-full sm:min-w-[320px] sm:w-auto sm:flex-1">
              <CareerStats runner={runner} race={race} />
            </div>
            <div className="flex w-full gap-3 sm:contents">
              {hasPriceInfo && (
                <div className="min-w-0 flex-1 sm:min-w-[220px] sm:w-auto sm:flex-1">
                  <PriceMovementChart
                    runner={runner}
                    priceBitsBefore={priceBitsBefore}
                    priceBitsAfter={priceBitsAfter}
                    fixedMove={fixedMove}
                  />
                </div>
              )}
              <div className="min-w-0 flex-1 sm:min-w-[220px] sm:w-auto sm:flex-1">
                <ResultVsProjection runner={runner} />
              </div>
            </div>
          </div>

          <RecentRunsTable
            horseName={runner.horse}
            runs={runner.recentRuns}
            peakRun={runner.peakRun}
            formHistory={runner.formHistory}
            raceDistance={race.distance}
            raceGoing={race.going}
          />

          <ComparisonGrid runner={runner} race={race} allRunners={race.runners} />

          {/* Jockey/trainer names and their ratings are already in the
              header subtitle - only barrier is new information here. */}
          <div className="border-t border-line-soft pt-2 text-xs text-ink-faint">
            Barrier {runner.barrier ?? '—'}
            <span className="ml-1.5 italic">(not used by the projection)</span>
          </div>
        </div>
      </div>
    </div>
  )
}
