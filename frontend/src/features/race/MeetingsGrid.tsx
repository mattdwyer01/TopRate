import { useMemo, useState } from 'react'
import type { Race } from '../../types/domain'
import { Pill } from '../../components/Pill'
import { EmptyState } from '../../components/EmptyState'
import {
  groupIntoMeetings,
  isBushMeeting,
  todayIso,
} from '../../lib/meetings'
import { formatTimeOfDay } from '../../lib/countdown'

interface MeetingsGridProps {
  races: Race[]
  onSelectRace: (raceId: string, date: string) => void
  initialDate?: string | null
}

const DATE_QUICK_BUTTONS: { label: string; offset: number }[] = [
  { label: 'Yesterday', offset: -1 },
  { label: 'Today', offset: 0 },
  { label: 'Tomorrow', offset: 1 },
]

// A race within this many minutes of jumping gets the "soon" highlight.
const SOON_THRESHOLD_MS = 15 * 60_000

export function MeetingsGrid({ races, onSelectRace, initialDate }: MeetingsGridProps) {
  const [date, setDate] = useState(() => initialDate ?? todayIso())
  const [showBush, setShowBush] = useState(false)

  const meetings = useMemo(() => groupIntoMeetings(races, date), [races, date])
  const visibleMeetings = showBush ? meetings : meetings.filter((m) => !isBushMeeting(m))
  const hiddenCount = meetings.length - visibleMeetings.length

  // Columns run R1..the highest race number anywhere in view, so every
  // meeting's races line up under the same column regardless of how many
  // races it carries - a venue with 9 races just leaves R10+ blank.
  const maxRaceNumber = useMemo(
    () =>
      visibleMeetings.reduce(
        (max, m) => Math.max(max, ...m.races.map((r) => r.raceNumber)),
        0,
      ),
    [visibleMeetings],
  )
  const raceNumbers = useMemo(
    () => Array.from({ length: maxRaceNumber }, (_, i) => i + 1),
    [maxRaceNumber],
  )
  const now = Date.now()

  return (
    <div className="flex flex-col gap-4">
      <div className="flex flex-wrap items-center gap-2">
        {DATE_QUICK_BUTTONS.map((btn) => {
          const btnDate = todayIso(btn.offset)
          return (
            <Pill key={btn.label} active={date === btnDate} onClick={() => setDate(btnDate)}>
              {btn.label}
            </Pill>
          )
        })}
        <input
          type="date"
          value={date}
          onChange={(e) => setDate(e.target.value)}
          className="rounded-md border border-line bg-panel px-2 py-1 text-sm font-mono"
        />
        {hiddenCount > 0 && (
          <Pill active={showBush} onClick={() => setShowBush((v) => !v)}>
            {showBush ? 'Hide' : 'Show'} {hiddenCount} bush meeting{hiddenCount === 1 ? '' : 's'}
          </Pill>
        )}
      </div>

      {visibleMeetings.length === 0 ? (
        <EmptyState message={`No races on ${date}.`} />
      ) : (
        <div className="overflow-x-auto rounded-lg border border-line bg-panel">
          <table className="w-full border-collapse">
            <thead>
              <tr className="border-b border-line bg-bg text-xs font-medium text-ink-mute">
                <th className="sticky left-0 z-20 min-w-[10rem] border-r border-line bg-bg px-3 py-2 text-left">
                  Meeting
                </th>
                {raceNumbers.map((n) => (
                  <th key={n} className="min-w-[3.25rem] px-1.5 py-2 text-center font-mono">
                    R{n}
                  </th>
                ))}
              </tr>
            </thead>
            <tbody>
              {visibleMeetings.map((meeting) => (
                <tr
                  key={`${meeting.date}-${meeting.venue}`}
                  className="border-b border-line-soft last:border-b-0"
                >
                  <td className="sticky left-0 z-10 border-r border-line bg-panel px-3 py-2">
                    <div className="font-semibold text-ink">{meeting.venue}</div>
                    <div className="text-xs text-ink-mute">{meeting.state}</div>
                  </td>
                  {raceNumbers.map((n) => {
                    const race = meeting.races.find((r) => r.raceNumber === n)
                    if (!race) return <td key={n} className="px-1.5 py-2" />
                    const soon =
                      !race.allResulted &&
                      new Date(race.startTime).getTime() - now <= SOON_THRESHOLD_MS
                    return (
                      <td key={n} className="px-1.5 py-2 text-center">
                        <button
                          type="button"
                          onClick={() => onSelectRace(race.raceId, race.date)}
                          className={`w-full rounded-md border px-1 py-1 font-mono text-xs transition-colors ${
                            race.allResulted
                              ? 'border-line-soft bg-bg text-ink-faint hover:border-line'
                              : soon
                                ? 'border-emerald-line bg-emerald-bg font-semibold text-emerald-deep hover:opacity-80'
                                : 'border-line-soft bg-bg text-ink hover:border-emerald-line hover:bg-emerald-bg'
                          }`}
                        >
                          {formatTimeOfDay(race.startTime)}
                        </button>
                      </td>
                    )
                  })}
                </tr>
              ))}
            </tbody>
          </table>
        </div>
      )}
    </div>
  )
}
