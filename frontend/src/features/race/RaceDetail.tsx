import { Fragment, useMemo, useRef, useState } from 'react'
import type { Race } from '../../types/domain'
import { Pill } from '../../components/Pill'
import { useShowScratched } from '../../lib/scratchedVisibility'
import { computeGapsFromTop, computeEffectiveRace, INNER_GAP_FROM_TOP, OUTER_GAP_FROM_TOP, CORE_GAP_FROM_TOP } from '../../lib/raceModel'
import { DEFAULT_DIRECTION, sortRunners, type SortDirection, type SortKey } from '../../lib/sorting'
import { useTripMap } from '../../lib/tripMap'
import { raceStatus, STATUS_PILL_TONE } from '../../lib/raceStatus'
import { RaceHeader, RaceMiniBar } from './RaceHeader'
import { BiasNote } from './BiasNote'
import { MIN_BIAS_RACES, racesRunBefore } from '../../lib/bias'
import { RaceLadder } from './RaceGlance'
import { RunnerCompare } from './RunnerCompare'
import { RunnerRow, rowGrid } from './RunnerRow'
import { RunnerDetailModal } from './RunnerDetailModal'
import { SpeedMap } from './SpeedMap'
import { SpeedMapGrid } from './SpeedMapGrid'
import { TripMap } from './TripMap'
import { PaceStrip } from './PaceStrip'
import { fmtStake, signalsForRace, TIER_UNITS, type BetSignals } from '../../lib/betSignals'
import { MIN_WINNING_STANDARD_OFFSET, expectedWinningWpr, rankField } from './raceFacts'

interface RaceDetailProps {
  race: Race
  allRaces: Race[]
  // Bet signals (experimental, lib/betSignals.ts); null when the file is missing.
  signals?: BetSignals | null
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
  onSelectRace: (raceId: string, date: string, runId?: string) => void
}

const MAX_COMPARE = 6

// Column headers (lgOnly ones drop out below lg), in the same order as RunnerRow's grid (ROW_GRID). The first (silk) cell is blank.
const COLUMNS: { key: SortKey | null; label: string; align: 'left' | 'right'; title?: string; lgOnly?: boolean }[] = [
  { key: null, label: '', align: 'left' },
  { key: 'tab', label: '#', align: 'left' },
  { key: 'horse', label: 'Horse', align: 'left' },
  { key: 'daysSince', label: 'RTS', align: 'right', title: 'Runs this spell (FU first-up, 2U second-up...)', lgOnly: true },
  { key: 'projectedWpr', label: 'Rating', align: 'right', title: "Rating at the weight carried today (the scale of the form table). From the bet-signal model where the race has signals (market informed, moves with the price), otherwise the WPR projection." },
  { key: 'speedMapAdj', label: 'SM', align: 'right', title: "Suitability adjustment relative to this field (part of the WPR projection, not of the bet-signal rating). Positive means a favourable map; runners at +0.5 or better won more often in testing, but the market already prices it." },
  { key: 'modelPrice', label: 'Model $', align: 'right', title: 'Bet-signal model price: 1 / its win chance. It starts from the market price, so it moves with it. Experimental.' },
  { key: 'edge', label: 'Edge', align: 'right', title: 'Model win chance x current price, minus 1. Select and Volume tiers are flagged on the runner.', lgOnly: true },
  { key: 'fixedPrice', label: 'Fixed $', align: 'right' },
  { key: 'finish', label: 'FP', align: 'right', title: 'Finishing position' },
]

// A hairline under the last runner inside each gap line, in the same colour as the row's left band.
// No tinted bar: the band already colours the rows, so this only has to say where each group ends.
const LINE_STYLE: Record<'core' | 'inner' | 'outer', { line: string; text: string }> = {
  core: { line: 'bg-blue', text: 'text-blue-deep' },
  inner: { line: 'bg-emerald', text: 'text-emerald-deep' },
  outer: { line: 'bg-amber-line', text: 'text-amber' },
}

function LineDivider({ kind, n }: { kind: 'core' | 'inner' | 'outer'; n: number }) {
  const st = LINE_STYLE[kind]
  return (
    <div className="relative h-0 w-full" aria-hidden="true">
      <span className={`absolute inset-x-0 top-0 h-px ${st.line}`} />
      <span className={`absolute right-2 top-0 z-10 -translate-y-1/2 rounded-full border border-line bg-panel px-1.5 font-mono text-[9px] font-semibold leading-4 ${st.text}`}>
        {'≤'}{n} from top
      </span>
    </div>
  )
}

export function RaceDetail({
  race,
  allRaces,
  signals = null,
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
  const [sortKey, setSortKey] = useState<SortKey>('projectedWpr')
  const [sortDir, setSortDir] = useState<SortDirection>(DEFAULT_DIRECTION.projectedWpr)
  const [selectedRunId, setSelectedRunId] = useState<string | null>(initialRunId ?? null)
  // Compare mode: clicking rows picks up to 6 runners for a side-by-side table instead of opening the detail panel.
  // Compare mode is remembered for the browser session, so stepping through a meeting's races keeps it on.
  const [compareMode, setCompareModeState] = useState(() => {
    try {
      return window.sessionStorage.getItem('toprate_compare_mode') === '1'
    } catch {
      return false
    }
  })
  function setCompareMode(on: boolean) {
    setCompareModeState(on)
    try {
      window.sessionStorage.setItem('toprate_compare_mode', on ? '1' : '0')
    } catch {
      // Session storage can be blocked; the mode just will not carry over.
    }
  }
  const [compareIds, setCompareIds] = useState<string[]>([])
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

  // Bet signals for this race: the live pass before the jump, the frozen pre-jump pass once it has run. They also set the rating (below).
  const signalByRunId = useMemo(() => signalsForRace(race, signals), [race, signals])
  const effectiveByRunId = useMemo(
    () => computeEffectiveRace(race.runners, deltas, bases, priceBeta, effectiveScratched, signalByRunId),
    [race.runners, deltas, bases, priceBeta, effectiveScratched, signalByRunId],
  )
  const gapByRunId = useMemo(() => computeGapsFromTop(race.runners, effectiveByRunId, effectiveScratched), [race.runners, effectiveByRunId, effectiveScratched])

  // Only this race's runners count against the (global) scratched set.
  const scratchedInRace = race.runners.filter((r) => effectiveScratched.has(r.runId)).length
  const hasAnyResult = race.runners.some((r) => r.finishPosition !== null)
  const activeRunners = useMemo(() => race.runners.filter((r) => !effectiveScratched.has(r.runId)), [race.runners, effectiveScratched])

  const ranked = useMemo(
    () => rankField(race.runners, effectiveByRunId, effectiveScratched, INNER_GAP_FROM_TOP, OUTER_GAP_FROM_TOP),
    [race.runners, effectiveByRunId, effectiveScratched],
  )
  // The things that explain the WPR projection (typical winning rating, the track-bias note) stay on the projection, which is what they were fitted on.
  const rankedProjection = useMemo(
    () => rankField(race.runners, effectiveByRunId, effectiveScratched, INNER_GAP_FROM_TOP, OUTER_GAP_FROM_TOP, CORE_GAP_FROM_TOP, 'projection'),
    [race.runners, effectiveByRunId, effectiveScratched],
  )
  const expectedWinWpr = useMemo(() => {
    const typical = expectedWinningWpr(rankedProjection.map((r) => r.proj - (r.eff?.atwOff ?? 0)))
    return typical == null ? null : typical - MIN_WINNING_STANDARD_OFFSET
  }, [rankedProjection])
  const ratingFromBets = useMemo(() => Object.values(effectiveByRunId).some((e) => e.ratingSource === 'bet'), [effectiveByRunId])
  const bandOf = useMemo(() => {
    const m = new Map<string, { band: 'core' | 'inner' | 'outer' | 'none' }>()
    for (const r of ranked) m.set(r.runner.runId, { band: r.core ? 'core' : r.inner ? 'inner' : r.outer ? 'outer' : 'none' })
    return m
  }, [ranked])

  const tierCounts = useMemo(() => {
    let s = 0
    let v = 0
    for (const r of race.runners) {
      if (effectiveScratched.has(r.runId)) continue
      const t = signalByRunId[r.runId]?.t
      if (t === 'S') s++
      else if (t === 'V') v++
    }
    return { s, v }
  }, [race.runners, signalByRunId, effectiveScratched])

  // Scratched runners always sort to the bottom: a horse that can no longer win shouldn't sit at the top of a Proj-sorted list.
  const sortedRunners = useMemo(() => {
    const sorted = sortRunners(race.runners, sortKey, sortDir, effectiveByRunId, race.date, signalByRunId)
    const active = sorted.filter((r) => !effectiveScratched.has(r.runId))
    if (!showScratched) return active
    return [...active, ...sorted.filter((r) => effectiveScratched.has(r.runId))]
  }, [race.runners, race.date, sortKey, sortDir, effectiveByRunId, signalByRunId, effectiveScratched, showScratched])

  const selectedIndex = sortedRunners.findIndex((r) => r.runId === selectedRunId)
  const selectedRunner = selectedIndex >= 0 ? sortedRunners[selectedIndex] : null

  // The two gap lines are only meaningful while the list is sorted best-projection-first.
  const lines = useMemo(() => {
    const none = { core: -1, inner: -1, outer: -1 }
    if (!(sortKey === 'projectedWpr' && sortDir === 'desc')) return none
    let core = -1
    let inner = -1
    let outer = -1
    sortedRunners.forEach((r, i) => {
      const g = gapByRunId[r.runId]
      if (g == null) return
      if (g <= CORE_GAP_FROM_TOP) core = i
      if (g <= INNER_GAP_FROM_TOP) inner = i
      if (g <= OUTER_GAP_FROM_TOP) outer = i
    })
    const last = sortedRunners.reduce((l, r, i) => (gapByRunId[r.runId] != null ? i : l), -1)
    return { core: core < last ? core : -1, inner: inner < last ? inner : -1, outer: outer < last && outer !== inner ? outer : -1 }
  }, [sortedRunners, gapByRunId, sortKey, sortDir])

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

  const showBias = racesRunBefore(race, allRaces) >= MIN_BIAS_RACES
  function rowProps(runner: Race['runners'][number]) {
    const b = bandOf.get(runner.runId)
    return {
      runner,
      raceDate: race.date,
      selected: compareMode ? compareIds.includes(runner.runId) : runner.runId === selectedRunId,
      effective: effectiveByRunId[runner.runId],
      signal: signalByRunId[runner.runId] ?? null,
      band: b?.band ?? ('none' as const),
      showFp: hasAnyResult,
      showBias,
      onClick: compareMode
        ? () => setCompareIds((ids) => (ids.includes(runner.runId) ? ids.filter((x) => x !== runner.runId) : ids.length >= MAX_COMPARE ? ids : [...ids, runner.runId]))
        : () => setSelectedRunId(runner.runId === selectedRunId ? null : runner.runId),
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

      <BiasNote ranked={rankedProjection} race={race} allRaces={allRaces} />

      <section className="flex flex-col gap-2">
        <div className="flex flex-wrap items-center justify-between gap-2">
          <h3 className="text-sm font-semibold text-ink">Runners</h3>
          <div className="flex flex-wrap items-center gap-2">
            <Pill
              active={compareMode}
              onClick={() => {
                setCompareMode(!compareMode)
                setSelectedRunId(null)
              }}
            >
              {compareMode ? `Comparing (${compareIds.length}/${MAX_COMPARE})` : 'Compare runners'}
            </Pill>
            {scratchedInRace > 0 && <Pill active={!showScratched} onClick={() => setShowScratched(!showScratched)}>{showScratched ? 'Hide scratched' : 'Show scratched'}</Pill>}
          </div>
        </div>

        <p className="text-[11px] text-ink-faint" data-testid="rating-source">
          {ratingFromBets
            ? 'Rating: bet-signal model on the ATW scale (win chances from the market price and form, so it moves with the price). Under it the WPR projection still explains each horse.'
            : 'Rating: WPR projection. No bet-signal rating for this race yet (it needs the full field drawn and priced).'}
        </p>
        {(tierCounts.s > 0 || tierCounts.v > 0) && (
          <div className="flex flex-wrap items-center gap-x-3 gap-y-1 rounded-md border border-emerald-line bg-emerald-bg px-3 py-1.5 text-xs text-emerald-deep">
            <span className="font-semibold">Bet signals (experimental)</span>
            {tierCounts.s > 0 && <span>{tierCounts.s} Select, {TIER_UNITS.S}u ({fmtStake(TIER_UNITS.S)})</span>}
            {tierCounts.v > 0 && <span>{tierCounts.v} Volume, {TIER_UNITS.V}u ({fmtStake(TIER_UNITS.V)})</span>}
            <span className="text-ink-mute">Edge is the model against the current price, not a tip.</span>
          </div>
        )}

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
                  aria-sort={sortKey === c.key ? (sortDir === 'asc' ? 'ascending' : 'descending') : undefined}
                  onClick={() => onSort(c.key as SortKey)}
                  className={`transition-colors hover:text-ink ${c.lgOnly || (c.key === 'finish' && !hasAnyResult) ? 'hidden lg:block ' : ''}${c.align === 'right' ? 'text-right' : 'text-left'} ${sortKey === c.key ? 'text-emerald-deep' : ''}`}
                >
                  {c.key === 'projectedWpr' ? (
                    <>
                      <span className="lg:hidden">Rtg</span>
                      <span className="hidden lg:inline">Rating</span>
                    </>
                  ) : (
                    c.label
                  )}
                  {sortKey === c.key && (sortDir === 'asc' ? ' ↑' : ' ↓')}
                </button>
              ),
            )}
          </div>
          {sortedRunners.map((r, i) => (
            <Fragment key={r.runId}>
              <RunnerRow {...rowProps(r)} />
              {i === lines.core && <LineDivider kind="core" n={CORE_GAP_FROM_TOP} />}
              {i === lines.inner && <LineDivider kind="inner" n={INNER_GAP_FROM_TOP} />}
              {i === lines.outer && <LineDivider kind="outer" n={OUTER_GAP_FROM_TOP} />}
            </Fragment>
          ))}
        </div>
        {compareMode && (
          <div className="flex flex-wrap items-center gap-1.5 text-xs text-ink-faint">
            <span>{compareIds.length < 2 ? 'Tap 2 to 6 runners above, or use a shortcut:' : 'Shortcuts:'}</span>
            <Pill active={false} onClick={() => setCompareIds(ranked.slice(0, 4).map((r) => r.runner.runId))}>
              Top 4
            </Pill>
            <Pill active={false} onClick={() => setCompareIds(ranked.filter((r) => r.core).slice(0, MAX_COMPARE).map((r) => r.runner.runId))}>
              Inside {CORE_GAP_FROM_TOP} line
            </Pill>
            <Pill active={false} onClick={() => setCompareIds(ranked.filter((r) => r.inner).slice(0, MAX_COMPARE).map((r) => r.runner.runId))}>
              Inside {INNER_GAP_FROM_TOP} line
            </Pill>
            <Pill active={false} onClick={() => setCompareIds(ranked.filter((r) => r.inner || r.outer).slice(0, MAX_COMPARE).map((r) => r.runner.runId))}>
              Inside {OUTER_GAP_FROM_TOP} line
            </Pill>
          </div>
        )}
      </section>

      {compareMode && compareIds.length >= 2 && (
        <RunnerCompare
          signalByRunId={signalByRunId}
          race={race}
          runners={compareIds.map((id) => race.runners.find((r) => r.runId === id)).filter((r): r is Race['runners'][number] => r != null)}
          effectiveByRunId={effectiveByRunId}
          gapByRunId={gapByRunId}
          onRemove={(id) => setCompareIds((ids) => ids.filter((x) => x !== id))}
          onOpen={(id) => {
            setCompareMode(false)
            setSelectedRunId(id)
          }}
          onClear={() => setCompareIds([])}
        />
      )}

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

      <RaceLadder ranked={ranked} coreGap={CORE_GAP_FROM_TOP} innerGap={INNER_GAP_FROM_TOP} outerGap={OUTER_GAP_FROM_TOP} onSelect={setSelectedRunId} />

      {selectedRunner && (
        <RunnerDetailModal
          runner={selectedRunner}
          race={race}
          effective={effectiveByRunId[selectedRunner.runId]}
          signal={signalByRunId[selectedRunner.runId] ?? null}
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
