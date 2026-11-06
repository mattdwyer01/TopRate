import { useEffect, useRef, useState } from 'react'
import type { Race, Runner } from '../../types/domain'
import type { TripRunner } from '../../lib/tripMap'
import { pureProj, type EffectiveRunner } from '../../lib/raceModel'
import { fmtPrice, fmtWpr } from '../../lib/format'
import { formatTimeOfDay } from '../../lib/countdown'
import { computePriceMove } from '../../lib/priceMove'
import { useBodyScrollLock, useFocusTrap } from '../../lib/modalA11y'
import { RecentRunsTable } from './RecentRunsTable'
import { CareerStats } from './CareerStats'
import { ConditionsScorecard, HeroBand, PriceVsFair, ResultCard, RunTimeline, TimelineLegend } from './horseParts'

interface RunnerDetailModalProps {
  runner: Runner
  race: Race
  effective?: EffectiveRunner
  rating?: number | null // the race table's combined Rating (Proj, Nett and Spd blend); falls back to the Proj when the runner has none
  rank: number | null
  fieldSize: number
  fieldTop: number | null
  tripRunner: TripRunner | null
  tripKind: 'avg' | '800m' | 'est' | null
  deltaValue: number | null
  baseValue: number | null
  onSetDelta: (v: number | null) => void
  onSetBase: (v: number | null) => void
  onToggleScratch: () => void
  onClose: () => void
  position?: { index: number; total: number }
  ranks?: (number | null)[] | null
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
  rating = null,
  rank,
  fieldSize,
  fieldTop,
  tripRunner,
  tripKind,
  deltaValue,
  baseValue,
  onSetDelta,
  onSetBase,
  onToggleScratch,
  onClose,
  position,
  ranks = null,
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

  // The projection at today's weight (ATW).
  const effectiveWpr = scratched ? null : (effective?.effectiveProjectedWpr ?? runner.projectedWpr)
  const ratingValue = scratched ? null : (rating ?? effectiveWpr)
  const atwOff = effective != null && Math.abs(effective.atwOff) >= 0.05 ? effective.atwOff : null
  const hasOverride = effective?.hasOverride ?? false
  const fixedMove = computePriceMove(runner.openFixedPrice, runner.fixedWinPrice)
  const fair = scratched ? null : (effective?.effectivePrice ?? null)
  const market = runner.fixedWinPrice
  const hasPriceInfo = runner.priceSeries.length >= 2 || market != null || runner.startingPrice != null
  const resulted = runner.resultKnown || runner.finishPosition != null
  const noProjection = runner.projectedWpr == null && baseValue == null
  const noJockey = !scratched && runner.jockey === '' && runner.projectedWpr != null && !resulted
  const noGoing = !scratched && !race.going && runner.projectedWpr != null && !resulted

  return (
    <div className="fixed inset-0 z-40 flex items-start justify-center overflow-y-auto bg-ink/60 p-0 sm:items-center sm:p-6" onClick={onClose}>
      <div
        ref={scrollRef}
        role="dialog"
        aria-modal="true"
        aria-label={`${runner.horse} detail`}
        tabIndex={-1}
        className="flex h-full max-h-full w-full max-w-[1400px] flex-col overflow-y-auto bg-bg shadow-[var(--shadow-2)] outline-none sm:h-auto sm:rounded-lg"
        onClick={(e) => e.stopPropagation()}
        onScroll={(e) => setScrolled(e.currentTarget.scrollTop > 110)}
      >
        {/* One dark header (6 Nov 2026): silk, name, connections and the race line together, with scratch and prev / next on the right. */}
        <div className="sticky top-0 z-10 bg-[#0B3B2A] text-white shadow-[var(--shadow-1)]">
          <div className="flex items-center gap-2 px-2 py-2 sm:gap-3 sm:px-4 sm:py-3">
            <div className="flex h-11 w-11 shrink-0 items-center justify-center rounded-lg bg-white sm:h-14 sm:w-14">
              {runner.silkUrl ? <img src={runner.silkUrl} alt="" className="h-9 w-9 object-contain sm:h-12 sm:w-12" /> : <span className="font-mono text-lg font-bold text-[#0B3B2A]">{runner.tabNumber}</span>}
            </div>
            <div className="min-w-0 flex-1">
              <div className={`flex min-w-0 items-baseline gap-2 ${scratched ? 'line-through decoration-white/60' : ''}`}>
                <span className="flex-none font-mono text-sm font-semibold text-[#A9CDBB] sm:text-base">{runner.tabNumber}</span>
                <span className="truncate text-base font-semibold leading-tight sm:text-xl">{runner.horse}</span>
                {scrolled && (
                  <span className="hidden flex-none items-baseline gap-1.5 text-xs sm:flex">
                    <span className="font-mono text-base font-bold text-[#6EE7B7]">{fmtWpr(ratingValue)}</span>
                    {market != null && <span className="font-mono text-white/80">{fmtPrice(market)}</span>}
                  </span>
                )}
              </div>
              <div className="truncate text-xs text-[#A9CDBB]">
                {scrolled ? (
                  <span className="sm:hidden">
                    <b className="font-mono text-[#6EE7B7]">{fmtWpr(ratingValue)}</b> rating{market != null ? ` \u00b7 ${fmtPrice(market)}` : ''} &middot;{' '}
                  </span>
                ) : null}
                {runner.jockey || 'Jockey TBC'} / {runner.trainer}
              </div>
              <div className="truncate text-[11px] text-white/70">
                {race.venue} R{race.raceNumber} &middot; {race.distance}m &middot; {race.going || 'going TBC'}
                <span className="hidden sm:inline">{race.rail ? ` · Rail ${race.rail}` : ''}</span> &middot; {formatTimeOfDay(race.startTime) || 'TBC'}
                {position ? <span> &middot; {position.index} of {position.total}</span> : null}
              </div>
            </div>
            <div className="flex shrink-0 items-center gap-1">
              {runner.dataScratched ? (
                <span title="Scratched" className="rounded-md bg-rose px-2 py-1 text-xs font-semibold text-white">
                  SCR
                </span>
              ) : (
                <button
                  type="button"
                  onClick={onToggleScratch}
                  title={scratched ? 'Un-scratch on this device' : 'Scratch on this device'}
                  className={`hidden rounded-md border px-2 py-1 text-xs font-semibold transition-colors sm:block ${scratched ? 'border-rose bg-rose text-white' : 'border-white/25 text-white/80 hover:bg-white/10 hover:text-white'}`}
                >
                  {scratched ? 'Scratched' : 'Scratch'}
                </button>
              )}
              <button type="button" onClick={onPrev} className="flex h-10 w-9 items-center justify-center rounded-md bg-white/10 text-lg text-white transition-colors hover:bg-white/20 sm:h-9 sm:w-9" aria-label="Previous runner">
                &lsaquo;
              </button>
              <button type="button" onClick={onNext} className="flex h-10 w-9 items-center justify-center rounded-md bg-white/10 text-lg text-white transition-colors hover:bg-white/20 sm:h-9 sm:w-9" aria-label="Next runner">
                &rsaquo;
              </button>
              <button type="button" onClick={onClose} className="ml-0.5 flex h-10 w-9 items-center justify-center rounded-md text-white/80 transition-colors hover:bg-white/10 hover:text-white sm:h-9 sm:w-9" aria-label="Close">
                &#10005;
              </button>
            </div>
          </div>
        </div>

        {/* Phones: one column in reading order (summary, result, recent runs, expected run, form, market, adjustment). From lg: summary across the top,
            the recent runs table full width, then the form chart (7 of 12) beside a column with the expected run, market, result and adjustment (5 of 12). */}
        <div className="flex flex-col gap-2.5 p-2 sm:gap-3 sm:p-4 lg:grid lg:grid-cols-12 lg:items-start lg:gap-4 lg:p-5">
          <div className="order-1 lg:col-span-12">
            <HeroBand
              runner={runner}
              race={race}
              proj={ratingValue}
              wr={pureProj(runner, effective)}
              scratched={scratched}
              rank={rank}
              fieldSize={fieldSize}
              fieldTop={fieldTop}
              fair={fair}
              market={market}
              fixedMove={fixedMove}
              hasOverride={hasOverride}
              ranks={ranks}
            />
          </div>

          {(noProjection || noJockey || noGoing) && (
            <div className="order-2 flex flex-col gap-2 lg:col-span-12">
              {noProjection && (
                <div className="rounded-lg border border-amber-line bg-amber-bg p-3 text-sm text-amber">
                  No projection for this runner. {runner.projectionDescription || (tripRunner && tripRunner.nHist >= 3 ? 'It has plenty of form, but is entered in another race before this one has run, so its latest rating is not known yet. The projection appears once that run is rated; enter your own base WPR below to rate it meanwhile.' : 'There is not enough form history to project it; enter your own base WPR below to rate it.')}
                </div>
              )}
              {noJockey && (
                <div className="rounded-lg border border-line bg-panel px-3 py-2 text-sm text-ink-soft" role="note">
                  Jockey not declared yet. The projection assumes an average jockey and moves when the rider is named.
                </div>
              )}
              {noGoing && (
                <div className="rounded-lg border border-line bg-panel px-3 py-2 text-sm text-ink-soft" role="note">
                  Going not known yet. The projection assumes Good 4 and updates when the track is rated.
                </div>
              )}
            </div>
          )}

          {resulted && (
            <Card title="Result" className="order-3 lg:hidden">
              <ResultCard runner={runner} />
            </Card>
          )}

          <section className="order-4 min-w-0 rounded-lg border border-line bg-panel p-3 empty:hidden sm:p-3.5 lg:col-span-12">
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
          </section>

          <Card className="order-6 min-w-0 lg:order-5 lg:col-span-7" title="Form and record" note="timeline, then today's conditions">
            <RunTimeline runner={runner} raceDate={race.date} />
            <TimelineLegend atwOffset={atwOff} weightKg={runner.weightCarried ?? null} />
            <h4 className="mb-1.5 mt-4 text-xs font-semibold uppercase tracking-wide text-ink-faint">Today's conditions against this horse's record</h4>
            <ConditionsScorecard runner={runner} race={race} />
            <details className="mt-2 text-sm">
              <summary className="cursor-pointer text-xs text-ink-mute hover:text-ink">Full condition table</summary>
              <div className="mt-2">
                <CareerStats runner={runner} race={race} breakdown={null} />
              </div>
            </details>
          </Card>

          {/* display: contents on phones so these cards join the single column in their own order; a stacked column from lg */}
          <div className="contents lg:order-6 lg:col-span-5 lg:flex lg:min-w-0 lg:flex-col lg:gap-4">
            <Card className="order-5 lg:order-none" title="Expected run" note={tripKind === '800m' || tripKind === 'est' ? 'about 800m from home' : undefined}>
              <div className="grid grid-cols-3 gap-2">
                <div className="rounded-lg bg-bg px-2.5 py-2">
                  <div className="text-[10px] font-semibold uppercase tracking-wide text-ink-faint">Settling</div>
                  <div className="truncate font-mono text-base font-medium text-ink">{runner.predictedSettlingBand ?? '-'}</div>
                </div>
                <div className="rounded-lg bg-bg px-2.5 py-2">
                  <div className="text-[10px] font-semibold uppercase tracking-wide text-ink-faint">Behind leader</div>
                  <div className="font-mono text-base font-medium text-ink">{tripRunner?.gap != null ? `${tripRunner.gap.toFixed(1)}L` : '-'}</div>
                </div>
                <div className="rounded-lg bg-bg px-2.5 py-2" title={tripKind === 'est' ? 'Off rail at 800m (estimated)' : tripKind === '800m' ? 'Off rail at 800m' : 'Off rail (average)'}>
                  <div className="text-[10px] font-semibold uppercase tracking-wide text-ink-faint">Off rail{tripKind === 'est' ? ' (est.)' : ''}</div>
                  <div className="font-mono text-base font-medium text-ink">{tripRunner && tripRunner.gap != null ? `${tripRunner.lane.toFixed(1)}m` : '-'}</div>
                </div>
              </div>
              <p className="mt-2 text-xs text-ink-faint">
                {tripRunner
                  ? tripRunner.last
                    ? `${tripKind === 'est' ? 'Result history' : 'GPS history'}: ${tripRunner.nHist} run${tripRunner.nHist === 1 ? '' : 's'}, last ${tripRunner.last.track} ${tripRunner.last.date}`
                    : 'No GPS history, forecast from barrier and track.'
                  : 'No trip forecast for this course.'}
              </p>
            </Card>

            <Card className="order-7 lg:order-none" title="Market" note="price against the rated price">
              {hasPriceInfo ? <PriceVsFair runner={runner} fair={scratched ? null : fair} placeFair={scratched ? null : (effective?.effectivePlacePrice ?? null)} /> : <p className="text-xs text-ink-faint">No price information yet.</p>}
            </Card>

            {resulted && (
              <Card title="Result" className="hidden lg:block">
                <ResultCard runner={runner} />
              </Card>
            )}

            <div className="order-8 rounded-lg border border-line bg-panel px-3 py-2 lg:order-none">
              <AdjustmentToggle active={deltaValue != null || baseValue != null}>
              <div className="flex flex-wrap items-center gap-x-4 gap-y-2">
                <label className="flex items-center gap-2 text-sm text-ink-soft">
                  Adjust by
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
              {!runner.dataScratched && (
                <button
                  type="button"
                  onClick={onToggleScratch}
                  className={`mt-2 rounded-md border px-2 py-1 text-xs font-semibold sm:hidden ${scratched ? 'border-rose-line bg-rose-bg text-rose' : 'border-line text-ink-mute'}`}
                >
                  {scratched ? 'Un-scratch (this device)' : 'Scratch on this device'}
                </button>
              )}
            </div>
          </div>
        </div>
      </div>
    </div>
  )
}
