import type { Race } from '../../types/domain'
import { computeRaceBias, fmtBias, BIAS_FLAG_MIN } from '../../lib/bias'
import type { Ranked } from './raceFacts'

const ordinal = (n: number) => `${n}${n % 100 >= 11 && n % 100 <= 13 ? 'th' : ({ 1: 'st', 2: 'nd', 3: 'rd' } as Record<number, string>)[n % 10] ?? 'th'}`

// Says, on the race page, whether the earlier races at this meeting have changed these projections, and who moved. Hidden once this race has run.
export function BiasNote({ ranked, race, allRaces }: { ranked: Ranked[]; race: Race; allRaces: Race[] }) {
  const done = race.runners.some((r) => r.resultKnown || r.finishPosition != null)
  if (done) return null
  const b = computeRaceBias(ranked, race, allRaces)
  if (b.racesRun === 0) return null
  // Nothing moved: say nothing. Otherwise one line, the biggest movers inline.
  if (b.movers.length === 0) return null
  const shown = b.movers.slice(0, 3)
  return (
    <div
      className="flex flex-wrap items-baseline gap-x-3 gap-y-0.5 rounded-md border border-amber-line bg-amber-bg px-2.5 py-1 text-xs text-ink-soft"
      role="note"
      title={`Read from ${b.racesRun} earlier race${b.racesRun === 1 ? '' : 's'} at this meeting, already included in Proj and SM. ${b.movers.length} runner${b.movers.length === 1 ? '' : 's'} moved by ${BIAS_FLAG_MIN} WPR or more.`}
    >
      <span className="font-semibold text-amber">Track bias</span>
      {shown.map((m) => (
        <span key={m.runner.runId} className="whitespace-nowrap">
          <span className="font-mono text-ink-mute">{m.runner.tabNumber}.</span> {m.runner.horse}{' '}
          <span className={`font-mono font-semibold ${m.bias >= 0 ? 'text-emerald-deep' : 'text-rose'}`}>{fmtBias(m.bias)}</span>
          {m.rankNow !== m.rankBefore && <span className="text-ink-mute"> ({ordinal(m.rankBefore)} to {ordinal(m.rankNow)})</span>}
        </span>
      ))}
      {b.movers.length > shown.length && <span className="text-ink-faint">+{b.movers.length - shown.length} more</span>}
    </div>
  )
}
