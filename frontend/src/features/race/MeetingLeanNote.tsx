import { useMeetingLean } from '../../lib/meetingLean'
import type { Race } from '../../types/domain'

// One line when the earlier races at this meeting (racing.com GPS, VIC and SA) show leaders or the fence winning. Reading aid only: no rating moves.
export function MeetingLeanNote({ race }: { race: Race }) {
  const done = race.runners.some((r) => r.resultKnown || r.finishPosition != null)
  const l = useMeetingLean(race.date, race.venue, race.raceNumber, !done && (race.state === 'VIC' || race.state === 'SA'))
  if (!l || (!l.leadStrong && !l.fenceShown)) return null
  const signed = (x: number) => `${x >= 0 ? '+' : ''}${x.toFixed(2)}`
  const pts = (x: number) => `${x >= 0 ? '+' : ''}${x.toFixed(1)}`
  const parts = [
    l.leadStrong && l.lead != null ? `Leaders are winning (${signed(l.lead)})` : null,
    l.fenceShown && l.fence != null && l.railPoints != null
      ? `${l.fence > 0 ? 'the fence is winning' : 'runners wide of the fence are winning'} (${signed(l.fence)}): about ${pts(l.railPoints)} rating points for the rail draw and ${pts(-l.railPoints)} for the widest`
      : null,
  ].filter(Boolean)
  return (
    <div
      className="flex flex-wrap items-baseline gap-x-3 rounded-md border border-line bg-panel px-2.5 py-1 text-xs text-ink-soft"
      role="note"
      title={`From the racing.com GPS of ${l.races} earlier races today: rank correlation of position after 400m (leaders) and distance off the rail (fence) with the finishing order, averaged. Points: 12 x barrier position (rail -0.5, widest +0.5) x the fence lean, fitted on 931 VIC/SA races, Apr to Oct 2026 (range 8 to 17). A reading aid, no rating changes.`}
    >
      <span className="font-semibold text-ink">Meeting lean</span>
      <span>{parts.join('; ')} over the last {l.races} races</span>
    </div>
  )
}
