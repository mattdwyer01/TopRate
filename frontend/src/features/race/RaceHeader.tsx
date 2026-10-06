import type { Race } from '../../types/domain'
import { estimatePace } from '../../lib/pace'
import { formatCountdown } from '../../lib/countdown'
import { fmtPrize, GOING_TONE_CLASS, goingChange, goingTone } from './raceFacts'

interface RaceHeaderProps {
  race: Race
  meeting: Race[]
  scratchedInRace: number
  hasAnyResult: boolean
  activeRunners: Race['runners']
}

function Chip({ children, className = '', title }: { children: React.ReactNode; className?: string; title?: string }) {
  return (
    <span
      title={title}
      className={`inline-flex items-center gap-1 rounded-full border px-2.5 py-0.5 text-xs font-medium ${className || 'border-line bg-bg text-ink-soft'}`}
    >
      {children}
    </span>
  )
}

// Title, status and the race's conditions in one place: going (with a flag when the track changed during the meeting), distance, rail,
// prize, field size, expected pace and whether first starters are in the field.
export function RaceHeader({ race, meeting, scratchedInRace, hasAnyResult, activeRunners }: RaceHeaderProps) {
  const change = goingChange(race, meeting)
  const pace = estimatePace(race, activeRunners)
  const prize = fmtPrize(race.prizeMoney)
  const rail = race.rail && race.rail !== 'nan' ? race.rail : null
  return (
    <section className="rounded-lg border border-line bg-panel p-4 shadow-[var(--shadow-1)]">
      <div className="flex flex-wrap items-start justify-between gap-x-4 gap-y-2">
        <div className="min-w-0">
          <div className="text-xs font-semibold uppercase tracking-wide text-ink-faint">
            {race.venue} &middot; {race.state} &middot; Race {race.raceNumber}
          </div>
          <h2 className="mt-0.5 text-xl font-semibold leading-tight text-ink sm:text-2xl">{race.raceName}</h2>
        </div>
        <div className="flex-none text-right">
          {race.allResulted && !race.provisional ? (
            <span className="rounded-full border border-emerald-line bg-emerald-bg px-2.5 py-1 font-mono text-xs font-semibold text-emerald-deep">Resulted</span>
          ) : hasAnyResult ? (
            <span
              className="rounded-full border border-amber-line bg-amber-bg px-2.5 py-1 font-mono text-xs font-semibold text-amber"
              title="TAB's fast provisional feed - toprate.au's confirmed result lands once the whole meeting finishes"
            >
              Interim result
            </span>
          ) : (
            <div>
              <div className="font-mono text-lg font-semibold text-ink">{formatCountdown(race.startTime) || '-'}</div>
              <div className="text-[11px] uppercase tracking-wide text-ink-faint">to jump</div>
            </div>
          )}
        </div>
      </div>

      <div className="mt-3 flex flex-wrap gap-1.5">
        <Chip>{race.distance}m</Chip>
        {race.going && (
          <Chip className={GOING_TONE_CLASS[goingTone(race.going)]} title="Going the projections for this race are made on">
            {race.going}
          </Chip>
        )}
        {change && (
          <Chip className="border-amber-line bg-amber-bg text-amber" title={`The track was ${change.from} at race ${change.race}`}>
            Track changed from {change.from}
          </Chip>
        )}
        {rail && <Chip title="Rail position">Rail {rail}</Chip>}
        {prize && <Chip>{prize}</Chip>}
        <Chip>
          {race.runners.length} runners
          {scratchedInRace > 0 && <span className="text-rose">&nbsp;({scratchedInRace} scratched)</span>}
        </Chip>
        <Chip title={pace.fromShape ? 'Measured early pace' : 'Predicted early pace'}>{pace.display}</Chip>
        {race.hasFirstStarter && <Chip className="border-amber-line bg-amber-bg text-amber">First starter in field</Chip>}
      </div>
    </section>
  )
}
