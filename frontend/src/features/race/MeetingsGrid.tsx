import { useMemo, useState } from 'react'
import type { Race } from '../../types/domain'
import { Pill } from '../../components/Pill'
import { EmptyState } from '../../components/EmptyState'
import {
  groupIntoMeetings,
  isBushMeeting,
  todayIso,
} from '../../lib/meetings'
import { formatCountdown } from '../../lib/countdown'

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

export function MeetingsGrid({ races, onSelectRace, initialDate }: MeetingsGridProps) {
  const [date, setDate] = useState(() => initialDate ?? todayIso())
  const [showBush, setShowBush] = useState(false)

  const meetings = useMemo(() => groupIntoMeetings(races, date), [races, date])
  const visibleMeetings = showBush ? meetings : meetings.filter((m) => !isBushMeeting(m))
  const hiddenCount = meetings.length - visibleMeetings.length

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
        <div className="grid grid-cols-1 gap-3 sm:grid-cols-2 lg:grid-cols-3">
          {visibleMeetings.map((meeting) => (
            <div
              key={`${meeting.date}-${meeting.venue}`}
              className="rounded-lg border border-line bg-panel p-3 shadow-[var(--shadow-1)]"
            >
              <div className="flex items-baseline justify-between">
                <h3 className="font-semibold text-ink">{meeting.venue}</h3>
                <span className="text-xs text-ink-mute">{meeting.state}</span>
              </div>
              <div className="mt-2 flex flex-wrap gap-1.5">
                {meeting.races.map((race) => (
                  <button
                    key={race.raceId}
                    type="button"
                    onClick={() => onSelectRace(race.raceId, race.date)}
                    className="rounded-md border border-line-soft bg-bg px-2 py-1 text-left text-xs transition-colors hover:border-emerald-line hover:bg-emerald-bg"
                  >
                    <div className="font-medium text-ink">R{race.raceNumber}</div>
                    <div className="font-mono text-ink-mute">
                      {race.allResulted ? 'Resulted' : formatCountdown(race.startTime)}
                    </div>
                  </button>
                ))}
              </div>
            </div>
          ))}
        </div>
      )}
    </div>
  )
}
