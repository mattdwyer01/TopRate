import { useEffect, useRef, useState } from 'react'
import type { Race, Runner } from '../../types/domain'
import type { TripRunner } from '../../lib/tripMap'
import type { EffectiveRunner } from '../../lib/raceModel'
import { fmtPrice, fmtWpr } from '../../lib/format'
import { computePriceMove } from '../../lib/priceMove'
import { useBodyScrollLock, useFocusTrap } from '../../lib/modalA11y'
import { spellPosition } from '../../lib/spellPosition'
import { RecentRunsTable } from './RecentRunsTable'
import { CareerStats } from './CareerStats'
import { ResultVsProjection } from './ResultVsProjection'
import { ratingSuffix } from './rowParts'
import { typicalSd } from './raceFacts'
import { ConditionsScorecard, HorseHero, PriceVsFair, ProjectionWaterfall, ResultCard, RunTimeline, TimelineLegend } from './horseParts'

interface RunnerDetailModalProps {
  runner: Runner
  race: Race
  effective?: EffectiveRunner
  rank: number | null
  fieldSize: number
  fieldTop: number | null
  fieldLow: number | null
  expectedWinWpr: number | null
  tripRunner: TripRunner | null
  tripKind: 'avg' | '800m' | 'est' | null
  deltaValue: number | null
  baseValue: number | null
  onSetDelta: (v: number | null) => void
  onSetBase: (v: number | null) => void
  onToggleScratch: () => void
  onClose: () => void
  onPrev: () => void
  onNext: () => void
}

function Card({ title, note, children, className = '' }: { title: string; note?: string; children: React.ReactNode; className?: string }) {
  return (
    <section className={`rounded-lg border border-line bg-panel p-3 sm:p-3.5 ${className}`}>
      <div className="mb-2 flex flex-wrap items-baseline justify-between gap-x-3">
        <h3 className="text-sm font-semibold text-ink">{title}</h3>
        {note && <span className="text-[11px] text-ink-faint">{note}</span>}
      </div>
      {children}
    </section>
  )
}

function AdjustmentToggle({ active, children }: { active: boolean; children: React.ReactNode }) {
  const [open, setOpen] = useState(active)
  return (
    <div>
      <button type="button" onClick={() => setOpen((o) => !o)} aria-expanded={open} className="flex w-full items-center justify-between text-left text-sm text-ink-soft">
        <span>{open ? '▾' : '▸'} Your adjustment</span>
        {active && <span className="text-xs text-amber">set</span>}
      </button>
      {open && <div className="mt-2">{children}</div>}
    </div>
  )
}

// The runner's page. Top: the projection and what it rests on. Then why (base, adjustment, form line), where the horse is expected to
// be in the run, how it goes in today's conditions, the market, and the full form. Prev/next and arrow keys move through the field;
// the manual adjustment writes through lib/wprOverrides and re-prices the whole field.
export function RunnerDetailModal({
  runner,
  race,
  effective,
  rank,
  fieldSize,
  fieldTop,
  fieldLow,
  expectedWinWpr,
  tripRunner,
  tripKind,
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
      const el = e.target as HTMLElement | null
      if (el && (el.tagName === 'INPUT' || el.tagName === 'TEXTAREA')) return
      if (e.key === 'Escape') onClose()
      else if (e.key === 'ArrowLeft') onPrev()
      else if (e.key === 'ArrowRight') onNext()
    }
    window.addEventListener('keydown', onKey)
    return () => window.removeEventListener('keydown', onKey)
  }, [onClose, onPrev, onNext])

  // The scrollable panel persists across prev/next, so reset it for the next horse.
  useEffect(() => {
    scrollRef.current?.scrollTo({ top: 0 })
    setScrolled(false)
  }, [runner.runId])

  const effectiveWpr = scratched ? null : (effective?.effectiveProjectedWpr ?? runner.projectedWpr)
  // The panel shows the projection at today's weight (ATW, as the Recent runs table does): the model's rating plus this horse's own offset. Ranking,
  // the range bar and the gap to the top stay on the model's rating, which is what the gap lines and fair prices were validated on.
  // The payload carries the offset the projection was made with (frozen in the projection log), or the horse's latest for a race still to run.
  const atwOff = runner.atwOffset != null && Math.abs(runner.atwOffset) >= 0.05 ? runner.atwOffset : null
  const projAtw = effectiveWpr != null && atwOff != null ? effectiveWpr + atwOff : null
  const hasOverride = effective?.hasOverride ?? false
  const spell = spellPosition(runner.formHistory, race.date)
  const fixedMove = computePriceMove(runner.openFixedPrice, runner.fixedWinPrice)
  const fair = effective?.effectivePrice ?? null
  const market = runner.fixedWinPrice
  const hasPriceInfo = runner.priceSeries.length >= 2 || market != null || runner.topratePrice != null || runner.startingPrice != null

  return (
    <div className="fixed inset-0 z-40 flex items-start justify-center overflow-y-auto bg-ink/60 p-0 sm:items-center sm:p-6" onClick={onClose}>
      <div
        ref={scrollRef}
        role="dialog"
        aria-modal="true"
        aria-label={`${runner.horse} detail`}
        tabIndex={-1}
        className="flex h-full max-h-full w-full max-w-6xl flex-col overflow-y-auto bg-bg shadow-[var(--shadow-2)] outline-none sm:h-auto sm:rounded-lg"
        onClick={(e) => e.stopPropagation()}
        onScroll={(e) => setScrolled(e.currentTarget.scrollTop > 110)}
      >
        <div className="sticky top-0 z-10 flex items-center gap-2.5 border-b border-line bg-panel px-3 py-2.5">
          {runner.silkUrl ? <img src={runner.silkUrl} alt="" className="h-11 w-11 shrink-0 rounded-sm object-contain" /> : <div className="h-11 w-11 shrink-0 rounded-sm bg-bg" />}
          <div className="min-w-0 flex-1">
            <div className={`truncate text-base font-semibold text-ink ${scratched ? 'line-through' : ''}`}>
              {runner.tabNumber}. {runner.horse}
            </div>
            {scrolled ? (
              <div className="flex items-center gap-2 truncate text-xs">
                <span className="font-mono font-bold text-emerald-deep">{fmtWpr(projAtw ?? effectiveWpr)}</span>
                <span className="text-ink-faint">projected WPR</span>
                {market != null && <span className="font-mono text-ink-soft">{fmtPrice(market)}</span>}
              </div>
            ) : (
              <div className="truncate text-xs text-ink-mute">
                {race.venue} R{race.raceNumber} &middot; {runner.jockey}
                {ratingSuffix(runner.jockeyRating)} / {runner.trainer}
                {ratingSuffix(runner.trainerRating)}
              </div>
            )}
          </div>
          <div className="flex shrink-0 items-center gap-1">
            {runner.dataScratched ? (
              <span title="Scratched (confirmed by TopRate)" className="rounded-md bg-rose px-2 py-1 text-xs font-semibold text-white">
                Scratched
              </span>
            ) : (
              <button
                type="button"
                onClick={onToggleScratch}
                className={`rounded-md border px-2 py-1 text-xs font-semibold transition-colors ${scratched ? 'border-rose-line bg-rose-bg text-rose' : 'border-line text-ink-mute hover:bg-bg hover:text-ink'}`}
              >
                {scratched ? 'Scratched' : 'Scratch'}
              </button>
            )}
            <button type="button" onClick={onPrev} className="flex h-8 w-8 items-center justify-center rounded-md border border-line text-ink-mute transition-colors hover:bg-bg hover:text-ink" aria-label="Previous runner">
              &lsaquo;
            </button>
            <button type="button" onClick={onNext} className="flex h-8 w-8 items-center justify-center rounded-md border border-line text-ink-mute transition-colors hover:bg-bg hover:text-ink" aria-label="Next runner">
              &rsaquo;
            </button>
            <button type="button" onClick={onClose} className="ml-1 flex h-8 w-8 items-center justify-center rounded-md text-ink-mute transition-colors hover:bg-bg hover:text-ink" aria-label="Close">
              &#10005;
            </button>
          </div>
        </div>

        <div className="flex flex-col gap-2 p-2 sm:gap-3 sm:p-4">
          {runner.projectedWpr == null && baseValue == null && (
            <div className="rounded-lg border border-amber-line bg-amber-bg p-3 text-sm text-amber">
              No projection for this runner. {runner.projectionDescription || (tripRunner && tripRunner.nHist >= 3 ? 'It has plenty of form, but is entered in another race before this one has run, so its latest rating is not known yet. The projection appears once that run is rated; enter your own base WPR below to rate it meanwhile.' : 'There is not enough form history to project it; enter your own base WPR below to rate it.')}
            </div>
          )}

          <HorseHero
            runner={runner}
            race={race}
            proj={effectiveWpr}
            scratched={scratched}
            rank={rank}
            fieldSize={fieldSize}
            fieldTop={fieldTop}
            fieldLow={fieldLow}
            fair={fair}
            market={market}
            fixedMove={fixedMove}
            hasOverride={hasOverride}
            spellLabel={spell.label}
            daysSince={spell.daysSince}
            projAtw={projAtw}
          />

          {(runner.resultKnown || runner.finishPosition != null) && (
            <div className="rounded-lg border border-line bg-panel p-3 sm:hidden">
              <ResultCard runner={runner} />
            </div>
          )}

          {/* Manual adjustment: a rarely used control, so a phone gets it as a one-line toggle (open when a value is set) */}
          <div className="rounded-lg border border-line bg-panel px-3 py-2 sm:hidden">
            <AdjustmentToggle active={deltaValue != null || baseValue != null}>
          <div className="flex flex-wrap items-center gap-x-4 gap-y-2">
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
            </label>
            {runner.projectedWpr == null && (
              <label className="flex items-center gap-2 text-sm text-ink-soft">
                Base WPR
                <input
                  type="number"
                  step="0.1"
                  value={baseValue ?? ''}
                  onChange={(e) => onSetBase(e.target.value === '' ? null : Number(e.target.value))}
                  placeholder="e.g. 72.0"
                  className="w-24 rounded-md border border-line bg-panel px-2 py-1 font-mono text-sm"
                />
              </label>
            )}
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
            <span className="text-xs text-ink-faint">Moves this horse and re-prices the whole field. Saved on this device.</span>
          </div>

            </AdjustmentToggle>
          </div>
          <div className="hidden sm:block">
          <div className="flex flex-wrap items-center gap-x-4 gap-y-2 rounded-lg border border-line bg-panel px-3 py-2">
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
            </label>
            {runner.projectedWpr == null && (
              <label className="flex items-center gap-2 text-sm text-ink-soft">
                Base WPR
                <input
                  type="number"
                  step="0.1"
                  value={baseValue ?? ''}
                  onChange={(e) => onSetBase(e.target.value === '' ? null : Number(e.target.value))}
                  placeholder="e.g. 72.0"
                  className="w-24 rounded-md border border-line bg-panel px-2 py-1 font-mono text-sm"
                />
              </label>
            )}
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
            <span className="text-xs text-ink-faint">Moves this horse and re-prices the whole field. Saved on this device.</span>
          </div>

          </div>

          <Card title="Why this projection" note={runner.projectionModel === 'light' ? 'light-history model' : 'main model'}>
            <div className="grid gap-x-8 gap-y-3 md:grid-cols-[minmax(0,1.5fr)_minmax(0,1fr)]">
              <ProjectionWaterfall runner={runner} proj={effectiveWpr} deltaValue={deltaValue} atwOffset={atwOff} weightKg={runner.weightCarried ?? null} />
              <div className="flex flex-col gap-2 md:border-l md:border-line-soft md:pl-6">
                <div className="text-[11px] font-semibold uppercase tracking-wide text-ink-faint">
                  Expected run <span className="font-normal normal-case">{tripKind === '800m' || tripKind === 'est' ? '(about 800m from home)' : ''}</span>
                </div>
                <div className="grid grid-cols-[auto_minmax(0,1fr)] gap-x-4 gap-y-1 text-sm">
                  <span className="text-ink-mute">Settling</span>
                  <span className="text-right font-mono text-ink">{runner.predictedSettlingBand ?? '-'}</span>
                  {tripRunner && tripRunner.gap != null && (
                    <>
                      <span className="text-ink-mute">Behind leader</span>
                      <span className="text-right font-mono text-ink">{tripRunner.gap.toFixed(1)}L</span>
                      <span className="text-ink-mute">{tripKind === 'est' ? 'Off rail at 800m (est.)' : tripKind === '800m' ? 'Off rail at 800m' : 'Off rail (avg)'}</span>
                      <span className="text-right font-mono text-ink">{tripRunner.lane.toFixed(1)}m</span>
                    </>
                  )}
                </div>
                <p className="text-xs text-ink-faint">
                  {tripRunner
                    ? tripRunner.last
                      ? `${tripKind === 'est' ? 'Result history' : 'GPS history'}: ${tripRunner.nHist} run${tripRunner.nHist === 1 ? '' : 's'}, last ${tripRunner.last.track} ${tripRunner.last.date}`
                      : 'No GPS history, forecast from barrier and track.'
                    : 'No trip forecast for this course.'}
                </p>
                {atwOff != null && effectiveWpr != null && (
                  <p className="hidden border-t border-line-soft pt-2 text-sm text-ink-soft sm:block">
                    Projected {fmtWpr(effectiveWpr + atwOff)} at {runner.weightCarried != null ? `${runner.weightCarried}kg` : "today's weight"}, the scale of the Recent runs table. Typical error about {typicalSd(runner, effectiveWpr)?.toFixed(1) ?? '-'}.
                  </p>
                )}
                {runner.projectionDescription && !(atwOff != null && effectiveWpr != null) && <p className="hidden border-t border-line-soft pt-2 text-sm text-ink-soft sm:block">{runner.projectionDescription}</p>}
              </div>
            </div>
          </Card>

          <Card title="Form and record" note="timeline, then today's conditions, then every run">
            <RunTimeline runner={runner} proj={effectiveWpr} raceDate={race.date} expectedWin={scratched ? null : expectedWinWpr} atwOffset={atwOff} />
            <TimelineLegend atwOffset={atwOff} weightKg={runner.weightCarried ?? null} />
            <h4 className="mb-1.5 mt-4 text-xs font-semibold uppercase tracking-wide text-ink-faint">Today's conditions against this horse's record</h4>
            <ConditionsScorecard runner={runner} race={race} />
            <details className="mt-2 text-sm">
              <summary className="cursor-pointer text-xs text-ink-mute hover:text-ink">Full condition table</summary>
              <div className="mt-2">
                <CareerStats runner={runner} race={race} breakdown={null} />
              </div>
            </details>
            <h4 className="mb-1.5 mt-4 text-xs font-semibold uppercase tracking-wide text-ink-faint">Every run, newest first</h4>
            <RecentRunsTable
              horseName={runner.horse}
              runs={runner.recentRuns}
              peakRun={runner.peakRun}
              formHistory={runner.formHistory}
              raceDistance={race.distance}
              raceGoing={race.going}
              raceDate={race.date}
              raceVenue={race.venue}
            />
          </Card>

          <div className="grid gap-3 lg:grid-cols-2">
            <Card title="Market" note="price against the model's fair price">
              {hasPriceInfo ? <PriceVsFair runner={runner} fair={scratched ? null : fair} /> : <p className="text-xs text-ink-faint">No price information yet.</p>}
            </Card>

            <Card title="Result against projection" className="hidden sm:block">
              <ResultCard runner={runner} />
              {runner.missCategory === 'unexplained' && (
                <div className="mt-2 border-t border-line-soft pt-2">
                  <ResultVsProjection runner={runner} />
                </div>
              )}
            </Card>
          </div>
        </div>
      </div>
    </div>
  )
}
