import { useMemo } from 'react'
import type { Race } from '../../types/domain'
import { Pill } from '../../components/Pill'
import { EmptyState } from '../../components/EmptyState'
import {
  groupIntoMeetings,
  meetingConditions,
  isBushMeeting,
  todayIso,
} from '../../lib/meetings'
import { formatTimeOfDay } from '../../lib/countdown'
import { useScrollShadow } from '../../lib/useScrollShadow'
import { hasQuaddie } from '../../lib/quaddie'
import { raceStatus, STATUS_CLASSES, STATUS_LEGEND, topFinishers } from '../../lib/raceStatus'

interface MeetingsGridProps {
  races: Race[]
  onSelectRace: (raceId: string, date: string) => void
  // The day shown. Owned by the URL (?date=), so it survives reload, back/forward and sharing.
  date: string
  onDateChange: (date: string) => void
  onOpenQuaddie: (venue: string) => void
  showBush: boolean
  onShowBushChange: (value: boolean) => void
  hiddenVenues: Set<string>
  onHideVenue: (venue: string) => void
}

const DATE_QUICK_BUTTONS: { label: string; offset: number }[] = [
  { label: 'Yesterday', offset: -1 },
  { label: 'Today', offset: 0 },
  { label: 'Tomorrow', offset: 1 },
]

// Moves an ISO date (YYYY-MM-DD) by whole days, in UTC so daylight saving cannot shift it.
function shiftDate(iso: string, days: number): string {
  const d = new Date(`${iso}T00:00:00Z`)
  d.setUTCDate(d.getUTCDate() + days)
  return d.toISOString().slice(0, 10)
}

export function MeetingsGrid({
  races,
  onSelectRace,
  date,
  onDateChange,
  onOpenQuaddie,
  showBush,
  onShowBushChange,
  hiddenVenues,
  onHideVenue,
}: MeetingsGridProps) {
  const setDate = onDateChange

  const meetings = useMemo(() => groupIntoMeetings(races, date), [races, date])
  // Total bush meetings for the day, independent of the current toggle
  // state - counting the filtered/unfiltered diff instead made the toggle
  // button (and its "Hide" label) disappear the instant showBush flipped
  // true, since at that point nothing was being filtered out.
  const bushCount = useMemo(() => meetings.filter(isBushMeeting).length, [meetings])
  const bushFiltered = showBush ? meetings : meetings.filter((m) => !isBushMeeting(m))
  // Manually hidden venues (see lib/hiddenVenues.ts) are excluded outright,
  // no toggle to reveal them again from here - unhiding is a Settings-modal
  // action, since this is a curated list rather than an automatic threshold.
  const visibleMeetings = bushFiltered.filter((m) => !hiddenVenues.has(m.venue))

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
  // The closest other date in the loaded window that has any races, for the empty state.
  const nearestDate = useMemo(() => {
    const target = new Date(`${date}T00:00:00Z`).getTime()
    let best: string | null = null
    let bestDist = Infinity
    for (const d of new Set(races.map((r) => r.date))) {
      const dist = Math.abs(new Date(`${d}T00:00:00Z`).getTime() - target)
      if (d !== date && dist < bestDist) {
        best = d
        bestDist = dist
      }
    }
    return best
  }, [races, date])
  const now = Date.now()

  // Upcoming races where the top projection leads the second by the most WPR: a quick way to find the races where the
  // model sees a clear standout. A separation ranking only; it says nothing about price or value.
  const standouts = useMemo(() => {
    const out: { race: Race; top: Race['runners'][number]; lead: number }[] = []
    for (const m of visibleMeetings) {
      for (const race of m.races) {
        const st = raceStatus(race, now)
        if (st === 'resulted' || st === 'interim') continue
        const rated = race.runners
          .filter((r) => !r.dataScratched && r.projectedWpr != null)
          .sort((a, b) => (b.projectedWpr as number) - (a.projectedWpr as number))
        if (rated.length < 5) continue
        out.push({ race, top: rated[0], lead: (rated[0].projectedWpr as number) - (rated[1].projectedWpr as number) })
      }
    }
    return out.sort((a, b) => b.lead - a.lead).slice(0, 5)
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [visibleMeetings])
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
        <div className="flex items-center gap-1">
        <button
          type="button"
          aria-label="Previous day"
          onClick={() => setDate(shiftDate(date, -1))}
          className="rounded-md border border-line bg-panel px-2 py-1 text-sm text-ink-mute hover:text-ink"
        >
          &lsaquo;
        </button>
        <input
          type="date"
          value={date}
          onChange={(e) => setDate(e.target.value)}
          className="rounded-md border border-line bg-panel px-2 py-1 text-sm font-mono"
        />
        <button
          type="button"
          aria-label="Next day"
          onClick={() => setDate(shiftDate(date, 1))}
          className="rounded-md border border-line bg-panel px-2 py-1 text-sm text-ink-mute hover:text-ink"
        >
          &rsaquo;
        </button>
        </div>
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
        <>
        <EmptyState
          message={
            meetings.length > 0
              ? `${meetings.length} meeting${meetings.length === 1 ? ' is' : 's are'} hidden by the bush or hidden-venue filters on ${date}.`
              : nearestDate
                ? `No races on ${date}. Nearest day with racing: ${nearestDate}.`
                : `No races on ${date}.`
          }
        />
        {nearestDate && meetings.length === 0 && (
          <div>
            <Pill active={false} onClick={() => setDate(nearestDate)}>
              Go to {nearestDate}
            </Pill>
          </div>
        )}
        </>
      ) : (
        <>
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
                    <td className="group sticky left-0 z-10 border-r border-line bg-panel px-3 py-2">
                      <div className="flex items-start justify-between gap-1">
                        <div>
                          <div className="font-semibold text-ink">{meeting.venue}</div>
                          <div className="text-xs text-ink-mute">{meeting.state}</div>
                          {(() => {
                            const c = meetingConditions(meeting, (r) => {
                              const st = raceStatus(r, now)
                              return st === 'resulted' || st === 'interim'
                            })
                            if (!c.going && !c.rail) return null
                            return (
                              <div className="max-w-[9.5rem] truncate text-[11px] leading-snug text-ink-mute" title={[c.going, c.rail ? `Rail: ${c.rail}` : null].filter(Boolean).join(' · ')}>
                                {c.going && (
                                  <span className={c.goingFrom ? 'font-semibold text-amber' : undefined} title={c.goingFrom ? `Changed from ${c.goingFrom}` : undefined}>
                                    {c.going}
                                    {c.goingFrom ? ` (was ${c.goingFrom})` : ''}
                                  </span>
                                )}
                                {c.going && c.rail ? ' · ' : ''}
                                {c.rail && <span>{`Rail ${c.rail}`}</span>}
                              </div>
                            )
                          })()}
                          {hasQuaddie(meeting.races) && (
                            <button
                              type="button"
                              onClick={() => onOpenQuaddie(meeting.venue)}
                              className="mt-0.5 text-xs font-medium text-emerald hover:underline"
                              aria-label={`Quaddie for ${meeting.venue}`}
                            >
                              Quaddie &rsaquo;
                            </button>
                          )}
                        </div>
                        <button
                          type="button"
                          onClick={() => onHideVenue(meeting.venue)}
                          title={`Hide ${meeting.venue} from this grid (undo in Settings)`}
                          aria-label={`Hide ${meeting.venue}`}
                          // Always visible below sm: touch devices have no
                          // hover state, so an opacity-0-until-hover button
                          // would be permanently invisible/untappable there
                          // (real user question, 2026-09-19: "How to hide on
                          // mobile?" - this was the actual cause, not just a
                          // discoverability gap). Desktop keeps the
                          // hover-to-reveal declutter from sm: up.
                          className="flex-none rounded px-1 text-xs text-ink-faint transition-opacity hover:bg-bg hover:text-ink sm:opacity-0 sm:group-hover:opacity-100 sm:focus:opacity-100"
                        >
                          ✕
                        </button>
                      </div>
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
                            aria-label={`${meeting.venue} race ${n}, ${status === 'resulted' || status === 'interim' ? 'result ' + (finishers?.join(' ') ?? '') : formatTimeOfDay(race.startTime)}`}
                            title={finishers && finishers.length > 0
                              ? `${formatTimeOfDay(race.startTime)} - top ${finishers.length} (TAB numbers): ${finishers.join('/')}`
                              : undefined}
                            className={`w-full rounded-md border px-1 py-1 font-mono text-xs transition-colors ${STATUS_CLASSES[status]}`}
                          >
                            {finishers && finishers.length > 0 ? (
                              finishers.join('/')
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
          {standouts.length > 0 && (
            <div className="rounded-lg border border-line bg-panel p-3">
              <div className="text-xs font-semibold uppercase tracking-wide text-ink-faint">Clearest standouts still to run</div>
              <p className="mb-2 text-[11px] text-ink-faint">Top projection leads the second by the most WPR. A ranking of separation only, not a tip.</p>
              <ul className="flex flex-col divide-y divide-line-soft text-sm">
                {standouts.map(({ race, top, lead }) => (
                  <li key={race.raceId}>
                    <button
                      type="button"
                      onClick={() => onSelectRace(race.raceId, race.date)}
                      className="flex w-full items-baseline justify-between gap-2 py-1.5 text-left hover:text-emerald-deep"
                    >
                      <span>
                        <span className="font-mono text-xs text-ink-mute">{race.venue} R{race.raceNumber} {formatTimeOfDay(race.startTime)}</span>{' '}
                        {top.tabNumber}. {top.horse}
                      </span>
                      <span className="flex-none font-mono text-xs text-ink-soft">+{lead.toFixed(1)} WPR</span>
                    </button>
                  </li>
                ))}
              </ul>
            </div>
          )}
        </>
      )}
    </div>
  )
}
