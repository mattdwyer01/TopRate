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
import { useScrollShadow } from '../../lib/useScrollShadow'
import { raceStatus, STATUS_CLASSES, STATUS_LEGEND, topFinishers } from '../../lib/raceStatus'

interface MeetingsGridProps {
  races: Race[]
  onSelectRace: (raceId: string, date: string) => void
  initialDate?: string | null
  showBush: boolean
  onShowBushChange: (value: boolean) => void
}

const DATE_QUICK_BUTTONS: { label: string; offset: number }[] = [
  { label: 'Yesterday', offset: -1 },
  { label: 'Today', offset: 0 },
  { label: 'Tomorrow', offset: 1 },
]

export function MeetingsGrid({ races, onSelectRace, initialDate, showBush, onShowBushChange }: MeetingsGridProps) {
  const [date, setDate] = useState(() => initialDate ?? todayIso())

  const meetings = useMemo(() => groupIntoMeetings(races, date), [races, date])
  // Total bush meetings for the day, independent of the current toggle
  // state - counting the filtered/unfiltered diff instead made the toggle
  // button (and its "Hide" label) disappear the instant showBush flipped
  // true, since at that point nothing was being filtered out.
  const bushCount = useMemo(() => meetings.filter(isBushMeeting).length, [meetings])
  const visibleMeetings = showBush ? meetings : meetings.filter((m) => !isBushMeeting(m))

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
  const { ref: scrollRef, canScrollRight } = useScrollShadow<HTMLDivElement>()

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
        {bushCount > 0 && (
          <Pill active={showBush} onClick={() => onShowBushChange(!showBush)}>
            {showBush ? 'Hide' : 'Show'} {bushCount} bush meeting{bushCount === 1 ? '' : 's'}
          </Pill>
        )}
      </div>

      {visibleMeetings.length > 0 && (
        <div className="flex flex-wrap items-center gap-x-4 gap-y-1 text-xs text-ink-mute">
          {STATUS_LEGEND.map(({ status, label, dotClass }) => (
            <div key={status} className="flex items-center gap-1.5">
              <span className={`h-2 w-2 flex-none rounded-full ${dotClass}`} />
              {label}
            </div>
          ))}
        </div>
      )}

      {visibleMeetings.length === 0 ? (
        <EmptyState message={`No races on ${date}.`} />
      ) : (
        <div className="relative">
          <div ref={scrollRef} className="overflow-x-auto rounded-lg border border-line bg-panel">
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
                      const status = raceStatus(race, now)
                      // Swap the time for the top finishers once there's a
                      // result to show, not just a colour change - two
                      // shades of grey/neutral (resulted vs. still hours
                      // away) were too easy to mix up at a glance, this
                      // makes the two states show genuinely different text.
                      const finishers = status === 'resulted' || status === 'interim'
                        ? topFinishers(race)
                        : null
                      return (
                        <td key={n} className="px-1.5 py-2 text-center">
                          <button
                            type="button"
                            onClick={() => onSelectRace(race.raceId, race.date)}
                            title={finishers && finishers.length > 0
                              ? `${formatTimeOfDay(race.startTime)} - top ${finishers.length}: #${finishers.join(', #')}`
                              : undefined}
                            className={`w-full rounded-md border px-1 py-1 font-mono text-xs transition-colors ${STATUS_CLASSES[status]}`}
                          >
                            {finishers && finishers.length > 0 ? (
                              // 2x2 grid, not space-joined text left to wrap
                              // on its own - at narrow column widths (and
                              // especially on mobile) plain text wrapping
                              // put one number per line, making these pills
                              // noticeably taller than a time-showing one.
                              <span className="grid grid-cols-2 gap-x-1 leading-tight">
                                {finishers.map((t) => (
                                  <span key={t}>#{t}</span>
                                ))}
                              </span>
                            ) : (
                              formatTimeOfDay(race.startTime)
                            )}
                          </button>
                        </td>
                      )
                    })}
                  </tr>
                ))}
              </tbody>
            </table>
          </div>
          {canScrollRight && (
            <div className="pointer-events-none absolute inset-y-0 right-0 flex w-10 items-center justify-end rounded-r-lg bg-gradient-to-l from-panel via-panel/80 to-transparent pr-1">
              <span className="text-ink-faint">&rsaquo;</span>
            </div>
          )}
        </div>
      )}
    </div>
  )
}
