import { useMemo, useRef, useState } from 'react'
import { useNow } from '../../hooks/useNow'
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
import { RunnerCompare } from './RunnerCompare'
import { RaceResult } from './RaceResult'
import { RunnerRow, rowGrid, silkFrom } from './RunnerRow'
import { computeCombinedRank } from '../../lib/combinedRank'
import { RunnerDetailModal } from './RunnerDetailModal'
import { SpeedMapGrid } from './SpeedMapGrid'
import { TripMap } from './TripMap'
import { PaceStrip } from './PaceStrip'
import { ReplayCard } from './ReplayCard'
import { useMinWidth } from '../../hooks/useMinWidth'
import { rankField } from './raceFacts'

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
  onSelectRace: (raceId: string, date: string, runId?: string) => void
}

const MAX_COMPARE = 6

// Column headers (lgOnly ones drop out below lg), in the same order as RunnerRow's grid (ROW_GRID). The first (silk) cell is blank.
const COLUMNS: { key: SortKey | null; label: string; align: 'left' | 'right'; title?: string; lgOnly?: boolean; phoneOnly?: boolean; label2?: string }[] = [
  { key: null, label: '', align: 'left' },
  { key: 'tab', label: '#', align: 'left' },
  { key: 'horse', label: 'Horse', align: 'left' },
  { key: 'daysSince', label: 'RTS', align: 'right', title: 'Runs this spell (FU first-up, 2U second-up...)', lgOnly: true },
  { key: 'speed', label: 'Spd', align: 'right', title: "Pre-race speed rating: recency-weighted mean of the horse's earlier time-based speed figures, in lengths against par (higher is faster). Needs two earlier figures." },
  { key: 'nett', label: 'Nett', align: 'right', title: "TopRate's own forward rating (wpr_nett). Weight adjusted to today's weight. Shown beside Proj, not blended into it." },
  { key: 'projectedWpr', label: 'Proj', align: 'right', title: "WPR projection at the weight carried today (the scale of the form table)." },
  { key: 'comboRank', label: 'Rank', align: 'right', title: "Combined rank: a weighted blend of each runner's standing in the field on Proj (65%), Nett (25%) and Spd (10%) (small squares under it show each signal's rank, in that column order Spd, Nett, Proj). A runner needs two of the three. It shows where the signals agree; it is not a better winner picker, the market already prices the agreement." },
  { key: 'fixedPrice', label: 'Fixed $', align: 'right' },
  { key: 'finish', label: 'FP', align: 'right', title: 'Finishing position' },
]

// Compare runners hidden at the user's request (11 Oct 2026); the feature is intact. Set true to show the pill again.
const SHOW_COMPARE = false

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
  const now = useNow(30_000)
  // Sorted by the combined Rank (best first) unless the user picks another column.
  const [sortKey, setSortKey] = useState<SortKey>('comboRank')
  const [sortDir, setSortDir] = useState<SortDirection>(DEFAULT_DIRECTION.comboRank)
  const [selectedRunId, setSelectedRunId] = useState<string | null>(initialRunId ?? null)
  // Compare mode: clicking rows picks up to 6 runners for a side-by-side table instead of opening the detail panel.
  // Compare mode is remembered for the browser session, so stepping through a meeting's races keeps it on.
  const [compareMode, setCompareModeState] = useState(() => {
    try {
      return SHOW_COMPARE && window.sessionStorage.getItem('toprate_compare_mode') === '1'
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
  const headerRef = useRef<HTMLDivElement>(null)
  const tripMap = useTripMap()
  const tripRace = tripMap?.races[race.raceId] ?? null
  // From xl the maps sit in a narrow column beside the runners, so the speed map uses its compact layout there.
  const wide = useMinWidth(1280)
  const [shapeChoice, setShapeChoice] = useState<'trip' | 'speed' | null>(null)
  const hasTrip = tripRace != null && tripMap != null
  const shapeView = shapeChoice ?? (hasTrip ? 'trip' : 'speed')

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
  const gapByRunId = useMemo(() => computeGapsFromTop(race.runners, effectiveByRunId, effectiveScratched), [race.runners, effectiveByRunId, effectiveScratched])

  // Only this race's runners count against the (global) scratched set.
  const comboByRunId = useMemo(() => computeCombinedRank(race.runners, effectiveByRunId, effectiveScratched), [race.runners, effectiveByRunId, effectiveScratched])
  const scratchedInRace = race.runners.filter((r) => effectiveScratched.has(r.runId)).length
  const hasAnyResult = race.runners.some((r) => r.finishPosition !== null)
  const hasAnyPrice = race.runners.some((r) => r.fixedWinPrice != null)
  const activeRunners = useMemo(() => race.runners.filter((r) => !effectiveScratched.has(r.runId)), [race.runners, effectiveScratched])

  const ranked = useMemo(
    () => rankField(race.runners, effectiveByRunId, effectiveScratched, INNER_GAP_FROM_TOP, OUTER_GAP_FROM_TOP),
    [race.runners, effectiveByRunId, effectiveScratched],
  )
  // The track-bias note stays on the WPR projection, which is what the bias adjustment lives in.
  const rankedProjection = useMemo(
    () => rankField(race.runners, effectiveByRunId, effectiveScratched, INNER_GAP_FROM_TOP, OUTER_GAP_FROM_TOP, CORE_GAP_FROM_TOP, 'projection'),
    [race.runners, effectiveByRunId, effectiveScratched],
  )
  // Scratched runners always sort to the bottom: a horse that can no longer win shouldn't sit at the top of a Proj-sorted list.
  const sortedRunners = useMemo(() => {
    const sorted = sortRunners(race.runners, sortKey, sortDir, effectiveByRunId, race.date, comboByRunId)
    const active = sorted.filter((r) => !effectiveScratched.has(r.runId))
    if (!showScratched) return active
    return [...active, ...sorted.filter((r) => effectiveScratched.has(r.runId))]
  }, [race.runners, race.date, sortKey, sortDir, effectiveByRunId, comboByRunId, effectiveScratched, showScratched])

  const selectedIndex = sortedRunners.findIndex((r) => r.runId === selectedRunId)
  const selectedRunner = selectedIndex >= 0 ? sortedRunners[selectedIndex] : null

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
  const projVals = ranked.map((x) => x.proj).filter((v): v is number => typeof v === 'number')
  const projSpan = projVals.length > 1 ? { min: Math.min(...projVals), max: Math.max(...projVals) } : undefined
  function rowProps(runner: Race['runners'][number]) {
    return {
      runner,
      raceDate: race.date,
      selected: compareMode ? compareIds.includes(runner.runId) : runner.runId === selectedRunId,
      effective: effectiveByRunId[runner.runId],
      combo: comboByRunId.get(runner.runId),
      showFp: hasAnyResult,
      showPrice: hasAnyPrice,
      showBias,
      projSpan,
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
        <div className="-mx-1 flex max-w-full flex-nowrap gap-1.5 overflow-x-auto px-1 pb-0.5 sm:mx-0 sm:flex-wrap sm:overflow-visible sm:px-0 sm:pb-0">
          {meetingRaces.map((r) => (
            <Pill key={r.raceId} active={r.raceId === race.raceId} tone={STATUS_PILL_TONE[raceStatus(r, now)]} onClick={() => onSelectRace(r.raceId, r.date)}>
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

      {hasAnyResult && (
        <div className="grid gap-4 xl:grid-cols-[minmax(0,3fr)_minmax(0,1fr)] xl:items-stretch">
          <RaceResult race={race} combo={comboByRunId} effective={effectiveByRunId} scratched={effectiveScratched} onSelectRunner={setSelectedRunId} />
          <div className="hidden xl:block"><ReplayCard venue={race.venue} date={race.date} raceNumber={race.raceNumber} /></div>
        </div>
      )}

      {/* From xl: runners (left) beside a sticky column with the pace strip and ladder (right); the Result panel stays full width above; the race shape stays full width underneath because the
          speed map and trip map need the room. Below xl one column: result, runners, shape, ladder. */}
      <div className="grid gap-4 xl:grid-cols-[minmax(0,3fr)_minmax(0,2fr)] xl:items-start">
        <div className="flex min-w-0 flex-col gap-4 xl:order-1">
        <section className="flex flex-col gap-2">
          <div className="flex flex-wrap items-center justify-between gap-2">
            <h3 className="text-sm font-semibold text-ink">Runners{!hasAnyPrice && <span className="ml-2 text-xs font-normal text-ink-faint lg:hidden">Prices not out yet</span>}</h3>
            <div className="flex flex-wrap items-center gap-2">
              {SHOW_COMPARE && <Pill
                active={compareMode}
                onClick={() => {
                  setCompareMode(!compareMode)
                  setSelectedRunId(null)
                }}
              >
                {compareMode ? `Comparing (${compareIds.length}/${MAX_COMPARE})` : 'Compare runners'}
              </Pill>}
              {scratchedInRace > 0 && <Pill active={!showScratched} onClick={() => setShowScratched(!showScratched)}>{showScratched ? 'Hide scratched' : `Show ${scratchedInRace} scratched`}</Pill>}
            </div>
          </div>

          <div className="overflow-hidden rounded-lg border border-line bg-panel">
            <div className={`grid min-w-full gap-x-1 border-b border-l-4 border-b-line border-l-transparent bg-bg px-2 py-1.5 text-[11px] font-medium text-ink-mute lg:gap-x-2 lg:text-xs ${rowGrid(hasAnyResult, hasAnyPrice)}`}>
              {COLUMNS.map((c, i) =>
                c.key == null ? (
                  <span key={i} className={`hidden ${silkFrom(hasAnyResult, hasAnyPrice)}`} />
                ) : (
                  <button
                    key={c.key + (c.phoneOnly ? '-phone' : '')}
                    type="button"
                    title={c.title}
                    aria-sort={sortKey === c.key ? (sortDir === 'asc' ? 'ascending' : 'descending') : undefined}
                    onClick={() => onSort(c.key as SortKey)}
                    className={`transition-colors hover:text-ink ${c.phoneOnly ? 'lg:hidden ' : c.lgOnly || (c.key === 'finish' && !hasAnyResult) || (c.key === 'fixedPrice' && !hasAnyPrice) ? 'hidden lg:block ' : ''}${c.align === 'right' ? 'text-right' : 'text-left'} ${sortKey === c.key ? 'text-emerald-deep' : ''}`}
                  >
                    {c.label}
                    {sortKey === c.key && (sortDir === 'asc' ? ' ↑' : ' ↓')}
                    {c.label2 && <span className="block font-normal text-ink-faint">{c.label2}</span>}
                  </button>
                ),
              )}
            </div>
            {sortedRunners.map((r) => (
              <RunnerRow key={r.runId} {...rowProps(r)} />
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
            </div>
          )}
        </section>

        {compareMode && compareIds.length >= 2 && (
          <RunnerCompare
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

        </div>
        {/* Right column from xl (below it, after the runners): pace, trip map and speed map, no inner scrolling. Scratched runners are left off the maps, not just dimmed. */}
        <div className="order-2 flex min-w-0 flex-col gap-4">
          <PaceStrip race={race} ranked={ranked} active={activeRunners} trip={tripRace} />
          {/* One map at a time: the to-scale trip map (default when this race has one) or the column speed map. */}
          {hasTrip && (
            <div className="flex items-center gap-1.5">
              <Pill active={shapeView === 'trip'} onClick={() => setShapeChoice('trip')}>
                Trip map
              </Pill>
              <Pill active={shapeView === 'speed'} onClick={() => setShapeChoice('speed')}>
                Speed map
              </Pill>
            </div>
          )}
          {shapeView === 'trip' && tripRace && tripMap ? (
            <TripMap trip={tripRace} excluded={effectiveScratched} runners={race.runners} compact={wide} smByRunId={Object.fromEntries(Object.entries(effectiveByRunId).map(([k, v]) => [k, v.speedMapAdj]))} />
          ) : (
            <SpeedMapGrid race={race} runners={activeRunners} narrow={wide} />
          )}
        </div>
      </div>

      {selectedRunner && (
        <RunnerDetailModal
          runner={selectedRunner}
          race={race}
          effective={effectiveByRunId[selectedRunner.runId]}
          rank={ranked.findIndex((x) => x.runner.runId === selectedRunner.runId) + 1 || null}
          fieldSize={ranked.length}
          fieldTop={ranked.length ? ranked[0].proj : null}
          tripRunner={tripRace?.runners.find((t) => t.rid === selectedRunner.runId) ?? null}
          tripKind={tripRace?.laneKind ?? null}
          deltaValue={deltas[selectedRunner.runId] ?? null}
          baseValue={bases[selectedRunner.runId] ?? null}
          onSetDelta={(v) => setDelta(selectedRunner.runId, v)}
          onSetBase={(v) => setBase(selectedRunner.runId, v)}
          onToggleScratch={() => setScratched(selectedRunner.runId, !scratched.has(selectedRunner.runId))}
          onClose={() => setSelectedRunId(null)}
          position={{ index: selectedIndex + 1, total: sortedRunners.length }}
          ranks={comboByRunId.get(selectedRunner.runId)?.ranks ?? null}
          onPrev={() => step(-1)}
          onNext={() => step(1)}
        />
      )}
    </div>
  )
}
