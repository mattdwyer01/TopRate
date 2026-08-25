import { useMemo, useState } from 'react'
import type { Race } from '../../types/domain'
import { Pill } from '../../components/Pill'
import { useTableDensity } from '../../lib/density'
import { computeEffectiveRace } from '../../lib/raceModel'
import { sortRunners, DEFAULT_DIRECTION, type SortKey, type SortDirection } from '../../lib/sorting'
import { RunnerRow } from './RunnerRow'
import { RunnerDetailModal } from './RunnerDetailModal'
import { SpeedMap } from './SpeedMap'
import { formatCountdown } from '../../lib/countdown'

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
  onBack: () => void
  onSelectRace: (raceId: string, date: string) => void
}

// RTS ("runs this spell" - the spellPosition label: FU/2U/3U/.../nU) sits
// right after Horse and is always visible (mobile included, not just
// desktop's Full density) - user request, Aug 2026. Bar(rier) dropped
// entirely per the same request. Order here drives both header rows'
// column order below and RunnerRow's matching grid-template order - keep
// all three in sync if this ever changes again.
const COLUMN_LABELS: { key: SortKey; label: string; showCompact?: boolean }[] = [
  { key: 'tab', label: '#' },
  { key: 'horse', label: 'Horse', showCompact: true },
  { key: 'daysSince', label: 'RTS', showCompact: true },
  { key: 'peakWpr', label: 'Peak' },
  { key: 'baseWpr', label: 'Base' },
  { key: 'adjustment', label: 'Adj' },
  { key: 'projectedWpr', label: 'Proj', showCompact: true },
  { key: 'wprPrice', label: 'WPR $' },
  { key: 'fixedPrice', label: 'Fixed $' },
  { key: 'finish', label: 'FP' },
  { key: 'actualWpr', label: 'Actual' },
]

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
  onBack,
  onSelectRace,
}: RaceDetailProps) {
  const { compact, setCompact } = useTableDensity()
  const [sortKey, setSortKey] = useState<SortKey>('projectedWpr')
  const [sortDir, setSortDir] = useState<SortDirection>(DEFAULT_DIRECTION.projectedWpr)
  const [selectedRunId, setSelectedRunId] = useState<string | null>(null)

  const effectiveByRunId = useMemo(
    () => computeEffectiveRace(race.runners, deltas, bases, priceBeta, scratched),
    [race.runners, deltas, bases, priceBeta, scratched],
  )
  // scratched is a global (all-races) set - count only this race's runners
  // in it for the header, rather than the whole set's size.
  const scratchedInRace = race.runners.filter((r) => scratched.has(r.runId)).length

  // Scratched runners sort to the bottom regardless of the chosen sort key -
  // they're out of the race, cluttering the top of a Proj-sorted list with
  // a horse that can no longer win is worse than losing strict sort order
  // for the (rare, temporary) scratched few.
  const sortedRunners = useMemo(() => {
    const sorted = sortRunners(race.runners, sortKey, sortDir, effectiveByRunId, race.date)
    const active = sorted.filter((r) => !scratched.has(r.runId))
    const scratchedRunners = sorted.filter((r) => scratched.has(r.runId))
    return [...active, ...scratchedRunners]
  }, [race.runners, race.date, sortKey, sortDir, effectiveByRunId, scratched])
  const selectedIndex = sortedRunners.findIndex((r) => r.runId === selectedRunId)
  const selectedRunner = selectedIndex >= 0 ? sortedRunners[selectedIndex] : null

  const meetingRaces = useMemo(
    () =>
      allRaces
        .filter((r) => r.venue === race.venue && r.date === race.date)
        .sort((a, b) => a.raceNumber - b.raceNumber),
    [allRaces, race.venue, race.date],
  )

  function onSort(key: SortKey) {
    if (key === sortKey) {
      setSortDir((d) => (d === 'asc' ? 'desc' : 'asc'))
    } else {
      setSortKey(key)
      setSortDir(DEFAULT_DIRECTION[key])
    }
  }

  function step(delta: number) {
    if (selectedIndex < 0) return
    const next = (selectedIndex + delta + sortedRunners.length) % sortedRunners.length
    setSelectedRunId(sortedRunners[next].runId)
  }

  return (
    <div className="flex flex-col gap-3">
      <button type="button" onClick={onBack} className="w-fit text-sm text-emerald hover:underline">
        &larr; Back to meetings
      </button>

      <div className="flex flex-wrap gap-1.5">
        {meetingRaces.map((r) => (
          <Pill key={r.raceId} active={r.raceId === race.raceId} onClick={() => onSelectRace(r.raceId, r.date)}>
            R{r.raceNumber}
          </Pill>
        ))}
      </div>

      <div className="rounded-lg border border-line bg-panel p-3 shadow-[var(--shadow-1)]">
        <div className="flex flex-wrap items-baseline justify-between gap-2">
          <h2 className="text-lg font-semibold text-ink">
            {race.venue} R{race.raceNumber} &middot; {race.raceName}
          </h2>
          {race.allResulted ? (
            <span className="rounded-full border border-emerald-line bg-emerald-bg px-2 py-0.5 font-mono text-xs font-semibold text-emerald-deep">
              Resulted
            </span>
          ) : (
            <span className="font-mono text-sm text-ink-mute">{formatCountdown(race.startTime)}</span>
          )}
        </div>
        <div className="mt-1 flex flex-wrap gap-x-4 gap-y-1 text-xs text-ink-mute">
          <span>{race.distance}m</span>
          <span>{race.going}</span>
          <span>
            {race.fieldSize} runners
            {scratchedInRace > 0 && (
              <span className="text-rose"> ({scratchedInRace} scratched)</span>
            )}
          </span>
          {race.hasFirstStarter && <span className="text-amber">First starter in field</span>}
        </div>
      </div>

      <div className="flex flex-wrap items-center justify-between gap-2">
        <div className="flex gap-1">
          <Pill active={compact} onClick={() => setCompact(true)}>Compact</Pill>
          <Pill active={!compact} onClick={() => setCompact(false)}>Full</Pill>
        </div>
        {/* The full column-header row (with its own sort buttons) is desktop-
            only (hidden below sm - see the grid below), so mobile needs its
            own way to change sort - otherwise it's stuck on whatever was
            last set, with no visible way to change it. */}
        <div className="flex items-center gap-1.5 sm:hidden">
          <select
            value={sortKey}
            onChange={(e) => onSort(e.target.value as SortKey)}
            aria-label="Sort by"
            className="rounded-md border border-line bg-panel px-2 py-1 text-xs"
          >
            {COLUMN_LABELS.map((col) => (
              <option key={col.key} value={col.key}>
                Sort: {col.label}
              </option>
            ))}
          </select>
          <button
            type="button"
            onClick={() => setSortDir((d) => (d === 'asc' ? 'desc' : 'asc'))}
            aria-label={sortDir === 'asc' ? 'Sort ascending' : 'Sort descending'}
            className="flex h-6 w-6 items-center justify-center rounded-md border border-line text-ink-mute transition-colors hover:bg-bg hover:text-ink"
          >
            {sortDir === 'asc' ? '↑' : '↓'}
          </button>
        </div>
      </div>

      <div className="overflow-x-auto rounded-lg border border-line bg-panel">
        {/* Mobile header: mirrors RunnerRow's mobile grid-cols exactly
            (silk/horse/RTS/proj/wprPrice/fixedPrice) so labels land above
            the right column - the desktop header below covers every column
            but is hidden below sm since most of them aren't shown there. */}
        <div className="grid grid-cols-[40px_1fr_44px_60px_56px_56px] gap-x-2 border-b border-line bg-bg px-2 py-1 text-[10px] font-medium text-ink-mute sm:hidden">
          <span />
          <button
            type="button"
            onClick={() => onSort('horse')}
            className={`text-left transition-colors hover:text-ink ${sortKey === 'horse' ? 'text-emerald-deep' : ''}`}
          >
            Horse
          </button>
          <button
            type="button"
            onClick={() => onSort('daysSince')}
            className={`text-right transition-colors hover:text-ink ${sortKey === 'daysSince' ? 'text-emerald-deep' : ''}`}
          >
            RTS
          </button>
          <button
            type="button"
            onClick={() => onSort('projectedWpr')}
            className={`text-right transition-colors hover:text-ink ${sortKey === 'projectedWpr' ? 'text-emerald-deep' : ''}`}
          >
            Proj
          </button>
          <button
            type="button"
            onClick={() => onSort('wprPrice')}
            className={`text-right transition-colors hover:text-ink ${sortKey === 'wprPrice' ? 'text-emerald-deep' : ''}`}
          >
            WPR $
          </button>
          <button
            type="button"
            onClick={() => onSort('fixedPrice')}
            className={`text-right transition-colors hover:text-ink ${sortKey === 'fixedPrice' ? 'text-emerald-deep' : ''}`}
          >
            Fixed $
          </button>
        </div>
        <div className="hidden min-w-full grid-cols-[44px_36px_1fr_56px_56px_56px_56px_60px_56px_56px_48px_52px] gap-x-2 border-b border-line bg-bg px-2 py-1.5 text-xs font-medium text-ink-mute sm:grid">
          <span />
          {COLUMN_LABELS.map((col) => {
            const align = col.key === 'horse' || col.key === 'tab' ? 'text-left' : 'text-center'
            return (
              <button
                key={col.key}
                type="button"
                onClick={() => onSort(col.key)}
                className={`${align} transition-colors hover:text-ink ${sortKey === col.key ? 'text-emerald-deep' : ''}`}
              >
                {col.label}
                {sortKey === col.key && (sortDir === 'asc' ? ' ↑' : ' ↓')}
              </button>
            )
          })}
        </div>
        {sortedRunners.map((runner) => (
          <RunnerRow
            key={runner.runId}
            runner={runner}
            raceDate={race.date}
            compact={compact}
            selected={runner.runId === selectedRunId}
            effective={effectiveByRunId[runner.runId]}
            onClick={() => setSelectedRunId(runner.runId === selectedRunId ? null : runner.runId)}
            onToggleScratch={() => setScratched(runner.runId, !scratched.has(runner.runId))}
          />
        ))}
      </div>

      {/* Scratched runners are excluded, not just visually - the speed map
          plots who's actually going to run, not the original field. */}
      <SpeedMap race={race} runners={race.runners.filter((r) => !scratched.has(r.runId))} />

      {selectedRunner && (
        <RunnerDetailModal
          runner={selectedRunner}
          race={race}
          effective={effectiveByRunId[selectedRunner.runId]}
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
