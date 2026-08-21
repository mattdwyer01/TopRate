import { useMemo, useState } from 'react'
import type { Race } from '../../types/domain'
import { Pill } from '../../components/Pill'
import { useTableDensity } from '../../lib/density'
import { sortRunners, DEFAULT_DIRECTION, type SortKey, type SortDirection } from '../../lib/sorting'
import { RunnerRow } from './RunnerRow'
import { RunnerDetailPanel } from './RunnerDetailPanel'
import { SpeedMap } from './SpeedMap'
import { formatCountdown } from '../../lib/countdown'

interface RaceDetailProps {
  race: Race
  allRaces: Race[]
  onBack: () => void
  onSelectRace: (raceId: string, date: string) => void
}

const COLUMN_LABELS: { key: SortKey; label: string; showCompact?: boolean }[] = [
  { key: 'tab', label: '#' },
  { key: 'horse', label: 'Horse', showCompact: true },
  { key: 'barrier', label: 'Bar' },
  { key: 'settle', label: 'Settle' },
  { key: 'peakWpr', label: 'Peak' },
  { key: 'avgLast3', label: 'L3' },
  { key: 'projectedWpr', label: 'Proj', showCompact: true },
  { key: 'wprPrice', label: 'WPR $' },
  { key: 'fixedPrice', label: 'Fixed $' },
  { key: 'overlay', label: 'Overlay' },
  { key: 'finish', label: 'FP' },
]

export function RaceDetail({ race, allRaces, onBack, onSelectRace }: RaceDetailProps) {
  const { compact, setCompact } = useTableDensity()
  const [sortKey, setSortKey] = useState<SortKey>('projectedWpr')
  const [sortDir, setSortDir] = useState<SortDirection>(DEFAULT_DIRECTION.projectedWpr)
  const [selectedRunId, setSelectedRunId] = useState<string | null>(null)

  const sortedRunners = useMemo(
    () => sortRunners(race.runners, sortKey, sortDir),
    [race.runners, sortKey, sortDir],
  )
  const selectedRunner = sortedRunners.find((r) => r.runId === selectedRunId) ?? null

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
          <span className="font-mono text-sm text-ink-mute">
            {race.allResulted ? 'Resulted' : formatCountdown(race.startTime)}
          </span>
        </div>
        <div className="mt-1 flex flex-wrap gap-x-4 gap-y-1 text-xs text-ink-mute">
          <span>{race.distance}m</span>
          <span>{race.going}</span>
          <span>{race.fieldSize} runners</span>
          {race.hasFirstStarter && <span className="text-amber">First starter in field</span>}
        </div>
      </div>

      <SpeedMap race={race} runners={race.runners} />

      <div className="flex items-center justify-between">
        <div className="flex gap-1">
          <Pill active={compact} onClick={() => setCompact(true)}>Compact</Pill>
          <Pill active={!compact} onClick={() => setCompact(false)}>Full</Pill>
        </div>
      </div>

      <div className="overflow-x-auto rounded-lg border border-line bg-panel">
        <div className="hidden min-w-full grid-cols-[28px_36px_1fr_48px_48px_56px_56px_60px_56px_56px_56px_48px] gap-x-2 border-b border-line bg-bg px-2 py-1.5 text-xs font-medium text-ink-mute sm:grid">
          <span />
          {COLUMN_LABELS.map((col) => (
            <button
              key={col.key}
              type="button"
              onClick={() => onSort(col.key)}
              className={`text-right transition-colors hover:text-ink ${col.key === 'horse' ? 'text-left' : ''} ${sortKey === col.key ? 'text-emerald-deep' : ''}`}
            >
              {col.label}
              {sortKey === col.key && (sortDir === 'asc' ? ' ↑' : ' ↓')}
            </button>
          ))}
        </div>
        {sortedRunners.map((runner) => (
          <RunnerRow
            key={runner.runId}
            runner={runner}
            compact={compact}
            selected={runner.runId === selectedRunId}
            onClick={() => setSelectedRunId(runner.runId === selectedRunId ? null : runner.runId)}
          />
        ))}
      </div>

      {selectedRunner && <RunnerDetailPanel runner={selectedRunner} race={race} />}
    </div>
  )
}
