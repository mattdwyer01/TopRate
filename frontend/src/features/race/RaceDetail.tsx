import { Fragment, useMemo, useRef, useState } from 'react'
import type { Race } from '../../types/domain'
import { Pill } from '../../components/Pill'
import { useShowScratched } from '../../lib/scratchedVisibility'
import { computeCompositeGaps, computeEffectiveRace, COMPOSITE_INNER_GAP_FROM_TOP, COMPOSITE_MAX_GAP_FROM_TOP } from '../../lib/raceModel'
import { DEFAULT_DIRECTION, sortRunners, type SortDirection, type SortKey } from '../../lib/sorting'
import { useTripMap } from '../../lib/tripMap'
import { raceStatus, STATUS_PILL_TONE } from '../../lib/raceStatus'
import { RaceHeader, RaceMiniBar } from './RaceHeader'
import { RaceLadder } from './RaceGlance'
import { RunnerRow, rowGrid } from './RunnerRow'
import { RunnerDetailModal } from './RunnerDetailModal'
import { SpeedMap } from './SpeedMap'
import { SpeedMapGrid } from './SpeedMapGrid'
import { TripMap } from './TripMap'
import { PaceStrip } from './PaceStrip'
import { expectedWinningWpr, rankField, typicalSd } from './raceFacts'

interface RaceDetailProps {
  race: Race
  allRaces: Race[]
  priceBeta: number | null
  deltas: Record<string, number>
  bases: Record<string, number>
  scratched: Set<string>
  setDelta: (runId: string, value: number | null) => void
  setBase: (runId: string, value: number | null) => void
  setScratched: (runId: string, value: boolean) => void
  // A runner to pre-select on mount (search, Review-tab cross-linking). Only read once: App.tsx keys RaceDetail on race.raceId.
  initialRunId?: string | null
  onBack: () => void
  onSelectRace: (raceId: string, date: string) => void
}

// Column headers (lgOnly ones drop out below lg), in the same order as RunnerRow's grid (ROW_GRID). The first (silk) cell is blank.
const COLUMNS: { key: SortKey | null; label: string; align: 'left' | 'right'; title?: string; lgOnly?: boolean }[] = [
  { key: null, label: '', align: 'left' },
  { key: 'tab', label: '#', align: 'left' },
  { key: 'horse', label: 'Horse', align: 'left' },
  { key: 'daysSince', label: 'RTS', align: 'right', title: 'Runs this spell (FU first-up, 2U second-up...)', lgOnly: true },
  { key: 'baseWpr', label: 'Base', align: 'right', title: 'Model projection before the suitability and weight adjustments', lgOnly: true },
  { key: 'adjustment', label: 'Adj', align: 'right', title: 'Suitability adjustment (comments, day-of bias, finishing profile, jockey/trainer)' },
  { key: 'compositeScore', label: 'Proj', align: 'right', title: 'Projected WPR (new model)' },
  { key: 'speedMapAdj', label: 'SM', align: 'right', title: 'Speed-map adjustment vs this field' },
  { key: 'ratedPrice', label: 'Rated $', align: 'right', title: "Fair price from the projection: what the model would pay the field at, not a market price", lgOnly: true },
  { key: 'fixedPrice', label: 'Fixed $', align: 'right' },
  { key: 'finish', label: 'FP', align: 'right', title: 'Finishing position' },
]

function LineDivider({ kind, n }: { kind: 'inner' | 'outer'; n: number }) {
  return kind === 'inner' ? (
    <div className="flex w-full items-center gap-2 bg-emerald-bg px-2 py-0.5" aria-hidden="true">
      <span className="h-0 flex-1 border-t-2 border-dotted border-emerald" />
      <span className="flex-none font-mono text-[10px] font-semibold uppercase tracking-wide text-emerald-deep">{n} WPR from top</span>
      <span className="h-0 flex-1 border-t-2 border-dotted border-emerald" />
    </div>
  ) : (
    <div className="flex w-full items-center gap-2 bg-amber-bg px-2 py-0.5" aria-hidden="true">
      <span className="h-[2px] flex-1 bg-amber-line" />
      <span className="flex-none font-mono text-[10px] font-semibold uppercase tracking-wide text-amber">{n} WPR from top</span>
      <span className="h-[2px] flex-1 bg-amber-line" />
    </div>
  )
}

export function RaceDetail({
  race,
  allRaces,
  priceBeta,
  deltas,
  bases,
  scratched,
  setDelta,
  setBase,
  setScratched,
  initialRunId,
  onBack,
  onSelectRace,
}: RaceDetailProps) {
  const { showScratched, setShowScratched } = useShowScratched()
  const [sortKey, setSortKey] = useState<SortKey>('compositeScore')
  const [sortDir, setSortDir] = useState<SortDirection>(DEFAULT_DIRECTION.compositeScore)
  const [selectedRunId, setSelectedRunId] = useState<string | null>(initialRunId ?? null)
  const [speedMapChoice, setSpeedMapView] = useState<'grid' | 'bar' | 'trip' | null>(null)
  const headerRef = useRef<HTMLDivElement>(null)
  const tripMap = useTripMap()
  const tripRace = tripMap?.races[race.raceId] ?? null
  // The to-scale trip map is the default view when this race has one; the column speed map otherwise.
  const speedMapView = speedMapChoice ?? (tripRace ? 'trip' : 'grid')

  // scratched (prop) is the manual, this-device-only toggle set; merge in each runner's real data-driven scratch so a late scratch the
  // pipeline detected takes effect here too. Toggling in the UI still only writes to the manual set (setScratched).
  const effectiveScratched = useMemo(() => {
    const merged = new Set(scratched)
    for (const r of race.runners) if (r.dataScratched) merged.add(r.runId)
    return merged
  }, [race.runners, scratched])

  const effectiveByRunId = useMemo(
    () => computeEffectiveRace(race.runners, deltas, bases, priceBeta, effectiveScratched),
    [race.runners, deltas, bases, priceBeta, effectiveScratched],
  )
  const compositeGapByRunId = useMemo(() => computeCompositeGaps(race.runners, effectiveByRunId, effectiveScratched), [race.runners, effectiveByRunId, effectiveScratched])

  // Only this race's runners count against the (global) scratched set.
  const scratchedInRace = race.runners.filter((r) => effectiveScratched.has(r.runId)).length
  const hasAnyResult = race.runners.some((r) => r.finishPosition !== null)
  const activeRunners = useMemo(() => race.runners.filter((r) => !effectiveScratched.has(r.runId)), [race.runners, effectiveScratched])

  const ranked = useMemo(
    () => rankField(race.runners, effectiveByRunId, effectiveScratched, COMPOSITE_INNER_GAP_FROM_TOP, COMPOSITE_MAX_GAP_FROM_TOP),
    [race.runners, effectiveByRunId, effectiveScratched],
  )
  const expectedWinWpr = useMemo(() => expectedWinningWpr(ranked.map((r) => ({ proj: r.proj, sd: typicalSd(r.runner, r.proj) ?? 9 }))), [ranked])
  const bandOf = useMemo(() => {
    const m = new Map<string, { band: 'inner' | 'outer' | 'none' }>()
    for (const r of ranked) m.set(r.runner.runId, { band: r.inner ? 'inner' : r.outer ? 'outer' : 'none' })
    return m
  }, [ranked])

  // Scratched runners always sort to the bottom: a horse that can no longer win shouldn't sit at the top of a Proj-sorted list.
  const sortedRunners = useMemo(() => {
    const sorted = sortRunners(race.runners, sortKey, sortDir, effectiveByRunId, race.date)
    const active = sorted.filter((r) => !effectiveScratched.has(r.runId))
    if (!showScratched) return active
    return [...active, ...sorted.filter((r) => effectiveScratched.has(r.runId))]
  }, [race.runners, race.date, sortKey, sortDir, effectiveByRunId, effectiveScratched, showScratched])

  const selectedIndex = sortedRunners.findIndex((r) => r.runId === selectedRunId)
  const selectedRunner = selectedIndex >= 0 ? sortedRunners[selectedIndex] : null

  // The two gap lines are only meaningful while the list is sorted best-projection-first.
  const lines = useMemo(() => {
    const none = { inner: -1, outer: -1 }
    if (!((sortKey === 'compositeScore' || sortKey === 'projectedWpr') && sortDir === 'desc')) return none
    let inner = -1
    let outer = -1
    sortedRunners.forEach((r, i) => {
      const g = compositeGapByRunId[r.runId]
      if (g == null) return
      if (g <= COMPOSITE_INNER_GAP_FROM_TOP) inner = i
      if (g <= COMPOSITE_MAX_GAP_FROM_TOP) outer = i
    })
    const last = sortedRunners.reduce((l, r, i) => (compositeGapByRunId[r.runId] != null ? i : l), -1)
    return { inner: inner < last ? inner : -1, outer: outer < last && outer !== inner ? outer : -1 }
  }, [sortedRunners, compositeGapByRunId, sortKey, sortDir])

  const meetingRaces = useMemo(
    () => allRaces.filter((r) => r.venue === race.venue && r.date === race.date).sort((a, b) => a.raceNumber - b.raceNumber),
    [allRaces, race.venue, race.date],
  )

  function onSort(key: SortKey) {
    if (key === sortKey) setSortDir((d) => (d === 'asc' ? 'desc' : 'asc'))
    else {
      setSortKey(key)
      setSortDir(DEFAULT_DIRECTION[key])
    }
  }

  function step(delta: number) {
    if (selectedIndex < 0) return
    setSelectedRunId(sortedRunners[(selectedIndex + delta + sortedRunners.length) % sortedRunners.length].runId)
  }

  function rowProps(runner: Race['runners'][number]) {
    const b = bandOf.get(runner.runId)
    return {
      runner,
      raceDate: race.date,
      selected: runner.runId === selectedRunId,
      effective: effectiveByRunId[runner.runId],
      band: b?.band ?? ('none' as const),
      showFp: hasAnyResult,
      onClick: () => setSelectedRunId(runner.runId === selectedRunId ? null : runner.runId),
    }
  }

  return (
    <div className="flex flex-col gap-4">
      <div className="flex flex-wrap items-center justify-between gap-2">
        <button type="button" onClick={onBack} className="w-fit text-sm text-emerald hover:underline">
          &larr; Back to meetings
        </button>
        <div className="flex flex-wrap gap-1.5">
          {meetingRaces.map((r) => (
            <Pill key={r.raceId} active={r.raceId === race.raceId} tone={STATUS_PILL_TONE[raceStatus(r, Date.now())]} onClick={() => onSelectRace(r.raceId, r.date)}>
              R{r.raceNumber}
            </Pill>
          ))}
        </div>
      </div>

      <div ref={headerRef}>
        <RaceHeader race={race} meeting={meetingRaces} scratchedInRace={scratchedInRace} hasAnyResult={hasAnyResult} activeRunners={activeRunners} />
      </div>
      <RaceMiniBar race={race} meeting={meetingRaces} activeRunners={activeRunners} anchorRef={headerRef} onSelectRace={onSelectRace} />

      <section className="flex flex-col gap-2">
        <div className="flex flex-wrap items-center justify-between gap-2">
          <h3 className="text-sm font-semibold text-ink">Runners</h3>
          <div className="flex flex-wrap items-center gap-2">
            {scratchedInRace > 0 && <Pill active={!showScratched} onClick={() => setShowScratched(!showScratched)}>{showScratched ? 'Hide scratched' : 'Show scratched'}</Pill>}
          </div>
        </div>

        <div className="overflow-hidden rounded-lg border border-line bg-panel">
          <div className={`grid min-w-full gap-x-1.5 border-b border-l-4 border-b-line border-l-transparent bg-bg px-2 py-1.5 text-[11px] font-medium text-ink-mute lg:gap-x-2 lg:text-xs ${rowGrid(hasAnyResult)}`}>
            {COLUMNS.map((c, i) =>
              c.key == null ? (
                <span key={i} />
              ) : (
                <button
                  key={c.key}
                  type="button"
                  title={c.title}
                  onClick={() => onSort(c.key as SortKey)}
                  className={`transition-colors hover:text-ink ${c.lgOnly || (c.key === 'finish' && !hasAnyResult) ? 'hidden lg:block ' : ''}${c.align === 'right' ? 'text-right' : 'text-left'} ${sortKey === c.key ? 'text-emerald-deep' : ''}`}
                >
                  {c.label}
                  {sortKey === c.key && (sortDir === 'asc' ? ' ↑' : ' ↓')}
                </button>
              ),
            )}
          </div>
          {sortedRunners.map((r, i) => (
            <Fragment key={r.runId}>
              <RunnerRow {...rowProps(r)} />
              {i === lines.inner && <LineDivider kind="inner" n={COMPOSITE_INNER_GAP_FROM_TOP} />}
              {i === lines.outer && <LineDivider kind="outer" n={COMPOSITE_MAX_GAP_FROM_TOP} />}
            </Fragment>
          ))}
        </div>
      </section>

      <section className="flex flex-col gap-2">
        <div className="flex flex-wrap items-center justify-between gap-2">
          <h3 className="text-sm font-semibold text-ink">Race shape</h3>
          {/* Scratched runners are left off, not just dimmed: the map shows who is actually going to run. */}
          <div className="flex flex-wrap items-center gap-1.5">
            {tripRace && (
              <Pill active={speedMapView === 'trip'} onClick={() => setSpeedMapView('trip')}>
                Trip map
              </Pill>
            )}
            <Pill active={speedMapView === 'grid' || (speedMapView === 'trip' && !tripRace)} onClick={() => setSpeedMapView('grid')}>
              Speed map
            </Pill>
            <Pill active={speedMapView === 'bar'} onClick={() => setSpeedMapView('bar')}>
              Bars
            </Pill>
          </div>
        </div>
        <PaceStrip race={race} ranked={ranked} active={activeRunners} trip={tripRace} />
        {speedMapView === 'trip' && tripRace && tripMap ? (
          <TripMap trip={tripRace} excluded={effectiveScratched} runners={race.runners} generated={tripMap.generated} />
        ) : speedMapView === 'bar' ? (
          <SpeedMap race={race} runners={activeRunners} />
        ) : (
          <SpeedMapGrid race={race} runners={activeRunners} />
        )}
      </section>

      <RaceLadder ranked={ranked} innerGap={COMPOSITE_INNER_GAP_FROM_TOP} outerGap={COMPOSITE_MAX_GAP_FROM_TOP} onSelect={setSelectedRunId} />

      {selectedRunner && (
        <RunnerDetailModal
          runner={selectedRunner}
          race={race}
          effective={effectiveByRunId[selectedRunner.runId]}
          rank={ranked.findIndex((x) => x.runner.runId === selectedRunner.runId) + 1 || null}
          fieldSize={ranked.length}
          fieldTop={ranked.length ? ranked[0].proj : null}
          fieldLow={ranked.length ? ranked[ranked.length - 1].proj : null}
          expectedWinWpr={expectedWinWpr}
          tripRunner={tripRace?.runners.find((t) => t.rid === selectedRunner.runId) ?? null}
          tripKind={tripRace?.laneKind ?? null}
          deltaValue={deltas[selectedRunner.runId] ?? null}
          baseValue={bases[selectedRunner.runId] ?? null}
          onSetDelta={(v) => setDelta(selectedRunner.runId, v)}
          onSetBase={(v) => setBase(selectedRunner.runId, v)}
          onToggleScratch={() => setScratched(selectedRunner.runId, !scratched.has(selectedRunner.runId))}
          onClose={() => setSelectedRunId(null)}
          onPrev={() => step(-1)}
          onNext={() => step(1)}
        />
      )}
    </div>
  )
}
