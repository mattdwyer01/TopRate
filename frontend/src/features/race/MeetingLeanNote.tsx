import { useMeetingLean } from '../../lib/meetingLean'
import type { Race } from '../../types/domain'

// One line when the earlier races at this meeting (racing.com GPS, VIC and SA) show leaders or the fence winning. Reading aid only: no rating moves.
export function MeetingLeanNote({ race }: { race: Race }) {
  const done = race.runners.some((r) => r.resultKnown || r.finishPosition != null)
  const l = useMeetingLean(race.date, race.venue, race.raceNumber, !done && (race.state === 'VIC' || race.state === 'SA'))
  if (!l || (!l.leadStrong && !l.fenceStrong)) return null
  const parts = [
    l.leadStrong && l.lead != null ? `Leaders are winning (${l.lead >= 0 ? '+' : ''}${l.lead.toFixed(2)})` : null,
    l.fenceStrong && l.fence != null ? `the fence is winning (${l.fence >= 0 ? '+' : ''}${l.fence.toFixed(2)})` : null,
  ].filter(Boolean)
  return (
    <div
      className="flex flex-wrap items-baseline gap-x-3 rounded-md border border-line bg-panel px-2.5 py-1 text-xs text-ink-soft"
      role="note"
      title={`From the racing.com GPS of ${l.races} earlier races today: rank correlation of position after 400m (leaders) and distance off the rail (fence) with the finishing order, averaged. A reading aid, no rating changes.`}
    >
      <span className="font-semibold text-ink">Meeting lean</span>
      <span>{parts.join(', ')} over the last {l.races} races</span>
    </div>
  )
}
