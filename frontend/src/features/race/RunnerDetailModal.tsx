import { useEffect, useRef, useState } from 'react'
import type { Race, Runner } from '../../types/domain'
import type { TripRunner } from '../../lib/tripMap'
import type { EffectiveRunner } from '../../lib/raceModel'
import { fmtInt, fmtPrice, fmtWpr } from '../../lib/format'
import { computePriceMove } from '../../lib/priceMove'
import { useBodyScrollLock, useFocusTrap } from '../../lib/modalA11y'
import { spellPosition } from '../../lib/spellPosition'
import { RecentRunsTable } from './RecentRunsTable'
import { ComparisonGrid } from './ComparisonGrid'
import { CareerStats } from './CareerStats'
import { ResultVsProjection } from './ResultVsProjection'
import { PriceMovementChart } from './PriceMovementChart'
import { FormLine } from './FormLine'
import { adjClass, fmtAdj, ratingSuffix } from './rowParts'

interface RunnerDetailModalProps {
  runner: Runner
  race: Race
  effective?: EffectiveRunner
  rank: number | null
  fieldSize: number
  gapFromTop: number | null
  tripRunner: TripRunner | null
  tripKind: 'avg' | '800m' | null
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
    <section className={`rounded-lg border border-line bg-panel p-3.5 ${className}`}>
      <div className="mb-2 flex flex-wrap items-baseline justify-between gap-x-3">
        <h3 className="text-sm font-semibold text-ink">{title}</h3>
        {note && <span className="text-[11px] text-ink-faint">{note}</span>}
      </div>
      {children}
    </section>
  )
}

function Tile({ label, children, sub, className = '' }: { label: string; children: React.ReactNode; sub?: React.ReactNode; className?: string }) {
  return (
    <div className={`min-w-0 rounded-lg bg-bg p-3 ${className}`}>
      <div className="text-[11px] font-semibold uppercase tracking-wide text-ink-faint">{label}</div>
      <div className="mt-1">{children}</div>
      {sub && <div className="mt-1 text-xs text-ink-mute">{sub}</div>}
    </div>
  )
}

function Row({ label, value, className = '' }: { label: string; value: React.ReactNode; className?: string }) {
  return (
    <div className="flex items-baseline justify-between gap-3 border-b border-line-soft py-1.5 text-sm last:border-0">
      <span className="text-ink-mute">{label}</span>
      <span className={`font-mono text-ink ${className}`}>{value}</span>
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
  gapFromTop,
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
  const hasOverride = effective?.hasOverride ?? false
  const spell = spellPosition(runner.formHistory, race.date)
  const fixedMove = computePriceMove(runner.openFixedPrice, runner.fixedWinPrice)
  const fair = effective?.effectivePrice ?? null
  const market = runner.fixedWinPrice
  const valuePct = fair != null && market != null && fair > 0 ? (market / fair - 1) * 100 : null
  const sd = runner.projectionSd
  const hasPriceInfo = runner.priceSeries.length >= 2 || market != null || runner.topratePrice != null || runner.startingPrice != null
  const priceBitsAfter = [runner.startingPrice != null ? `SP ${fmtPrice(runner.startingPrice)}` : 'SP post-race']

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
                <span className="font-mono font-bold text-emerald-deep">{fmtWpr(effectiveWpr)}</span>
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

        <div className="flex flex-col gap-3 p-3 sm:p-4">
          {runner.projectedWpr == null && baseValue == null && (
            <div className="rounded-lg border border-amber-line bg-amber-bg p-3 text-sm text-amber">
              No projection for this runner. {runner.projectionDescription || 'There is not enough form history to project it; enter your own base WPR below to rate it.'}
            </div>
          )}

          {/* Headline numbers */}
          <div className="grid grid-cols-2 gap-2 md:grid-cols-4">
            <Tile
              label="Projected WPR"
              className="col-span-2 md:col-span-1"
              sub={
                scratched ? (
                  runner.dataScratched ? 'confirmed scratched' : 'manually scratched'
                ) : (
                  <>
                    {sd != null && <span>&plusmn;{sd.toFixed(1)} typical error</span>}
                    {runner.projectionModel === 'light' && <span> &middot; light-history model</span>}
                    {hasOverride && <span className="text-amber"> &middot; manually adjusted</span>}
                  </>
                )
              }
            >
              {scratched ? (
                <span className="font-mono text-3xl font-bold text-rose">SCR</span>
              ) : (
                <span className="font-mono text-3xl font-bold text-emerald-deep">{fmtWpr(effectiveWpr)}</span>
              )}
              {!scratched && rank != null && (
                <div className="mt-1 text-xs text-ink-soft">
                  <span className="font-semibold">Rank {rank}</span> of {fieldSize}
                  {gapFromTop != null && gapFromTop > 0 ? <span className="text-ink-mute"> &middot; {gapFromTop.toFixed(1)} behind the top</span> : <span className="text-emerald-deep"> &middot; top rated</span>}
                </div>
              )}
            </Tile>
            <Tile
              label="Market"
              sub={
                fixedMove ? (
                  <span className={fixedMove.direction === 'firmed' ? 'text-emerald-deep' : 'text-rose'}>
                    {fixedMove.direction} {fixedMove.pctChange.toFixed(0)}% from {fmtPrice(runner.openFixedPrice)}
                  </span>
                ) : (
                  'no move since open'
                )
              }
            >
              <span className="font-mono text-2xl font-semibold text-ink">{fmtPrice(market)}</span>
              {fair != null && !scratched && (
                <div className="mt-1 text-xs text-ink-soft">
                  fair <span className="font-mono">{fmtPrice(fair)}</span>
                  {valuePct != null && (
                    <span className={valuePct >= 0 ? 'text-emerald-deep' : 'text-ink-mute'}>
                      {' '}
                      &middot; {valuePct >= 0 ? 'overlay' : 'underlay'} {Math.abs(Math.round(valuePct))}%
                    </span>
                  )}
                </div>
              )}
            </Tile>
            <Tile label="Ratings" sub="TopRate / Form / Nett">
              <span className="font-mono text-lg font-semibold text-ink-soft">
                {fmtInt(runner.toprateRating)} <span className="text-ink-faint">/</span> {fmtInt(runner.formFactor)} <span className="text-ink-faint">/</span> {fmtInt(runner.wprNett)}
              </span>
            </Tile>
            <Tile label="Today" sub={spell.daysSince != null ? `${spell.daysSince} days since last run` : 'no previous run'}>
              <span className="text-sm text-ink">
                <span className="font-semibold">Barrier {runner.barrier ?? '-'}</span>
                {runner.weightCarried != null && <span> &middot; {runner.weightCarried}kg</span>}
                <span className="font-mono text-amber"> &middot; {spell.label === 'FS' ? 'first start' : spell.label}</span>
              </span>
            </Tile>
          </div>

          {/* Manual adjustment */}
          <div className="flex flex-wrap items-center gap-x-4 gap-y-2 rounded-lg border border-line bg-panel px-3.5 py-2.5">
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

          <div className="grid gap-3 lg:grid-cols-2">
            <Card title="Why this projection" note={runner.projectionModel === 'light' ? 'light-history model' : 'main model'}>
              <div className="mb-3">
                <Row label="Base (form, conditions, connections)" value={fmtWpr(runner.baseWpr)} />
                <Row label="Suitability adjustment" value={fmtAdj(runner.wprAdjustment)} className={adjClass(runner.wprAdjustment)} />
                {deltaValue != null && deltaValue !== 0 && <Row label="Your adjustment" value={fmtAdj(deltaValue)} className="text-amber" />}
                <Row label="Projected WPR" value={<span className="font-semibold text-emerald-deep">{fmtWpr(effectiveWpr)}</span>} />
              </div>
              <FormLine runs={runner.recentRuns} projected={effectiveWpr} sd={sd} />
              {runner.projectionDescription && <p className="mt-2 border-t border-line-soft pt-2 text-sm text-ink-soft">{runner.projectionDescription}</p>}
            </Card>

            <Card title="Expected run" note="where it is likely to be about 800m from home">
              {tripRunner && tripRunner.gap != null ? (
                <div className="mb-2 grid grid-cols-2 gap-2">
                  <div className="rounded-md bg-bg p-2.5">
                    <div className="text-[11px] uppercase tracking-wide text-ink-faint">Behind the leader</div>
                    <div className="font-mono text-xl font-semibold text-ink">{tripRunner.gap.toFixed(1)}L</div>
                  </div>
                  <div className="rounded-md bg-bg p-2.5">
                    <div className="text-[11px] uppercase tracking-wide text-ink-faint">{tripKind === '800m' ? 'Off the rail at 800m' : 'Average off the rail'}</div>
                    <div className="font-mono text-xl font-semibold text-ink">{tripRunner.lane.toFixed(1)}m</div>
                  </div>
                </div>
              ) : null}
              <Row label="Settling position" value={runner.predictedSettlingBand ?? '-'} />
              {runner.againstShapeTendency && <Row label="Against the expected shape" value={runner.againstShapeTendency} />}
              {tripRunner && (
                <Row
                  label="GPS history"
                  value={tripRunner.last ? `${tripRunner.nHist} run${tripRunner.nHist === 1 ? '' : 's'}, last ${tripRunner.last.track} ${tripRunner.last.date}` : 'none (forecast from barrier and track)'}
                />
              )}
              {!tripRunner && <p className="mt-1 text-xs text-ink-faint">No trip forecast for this course (needs a VIC, SA or QLD GPS course with barriers declared).</p>}
            </Card>

            <Card title="Conditions and record" className="lg:col-span-2">
              <CareerStats runner={runner} race={race} breakdown={null} />
            </Card>

            <Card title="Market">
              {hasPriceInfo ? (
                <PriceMovementChart runner={runner} priceBitsBefore={[]} priceBitsAfter={priceBitsAfter} fixedMove={fixedMove} />
              ) : (
                <p className="text-xs text-ink-faint">No price information yet.</p>
              )}
            </Card>

            <Card title="Result against projection">
              <ResultVsProjection runner={runner} />
            </Card>
          </div>

          <Card title="Form" note="newest first">
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
            <div className="mt-3">
              <ComparisonGrid runner={runner} race={race} allRunners={race.runners} />
            </div>
          </Card>
        </div>
      </div>
    </div>
  )
}
