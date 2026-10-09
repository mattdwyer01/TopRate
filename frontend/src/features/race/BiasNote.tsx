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
  if (b.movers.length === 0) {
    return (
      <div className="rounded-lg border border-line bg-panel px-3 py-2 text-xs text-ink-mute" role="note">
        <span className="font-semibold text-ink-soft">Track bias:</span> read from {b.racesRun} earlier race{b.racesRun === 1 ? '' : 's'} at this meeting. No runner moved by {BIAS_FLAG_MIN} WPR or more.
      </div>
    )
  }
  const lean = b.drawLean == null ? null : b.drawLean > 0 ? 'wide draws are being helped' : 'inside draws are being helped'
  return (
    <div className="rounded-lg border border-amber-line bg-amber-bg px-3 py-2 text-xs text-ink-soft" role="note">
      <div>
        <span className="font-semibold text-amber">Track bias changed this race.</span> Read from {b.racesRun} earlier race{b.racesRun === 1 ? '' : 's'} at this meeting
        {lean ? `: ${lean}` : ''}. {b.movers.length} runner{b.movers.length === 1 ? '' : 's'} moved by {BIAS_FLAG_MIN} WPR or more
        {b.rankChanges > 0 ? `, ${b.rankChanges} changed place in the ranking` : ', none changed place'}. Already included in Proj and SM.
      </div>
      <ul className="mt-1 flex flex-wrap gap-x-4 gap-y-0.5">
        {b.movers.slice(0, 6).map((m) => (
          <li key={m.runner.runId} className="whitespace-nowrap">
            <span className="font-mono text-ink-mute">{m.runner.tabNumber}.</span> {m.runner.horse}{' '}
            <span className={`font-mono font-semibold ${m.bias >= 0 ? 'text-emerald-deep' : 'text-rose'}`}>{fmtBias(m.bias)}</span>
            {m.rankNow !== m.rankBefore && (
              <span className="text-ink-mute">
                {' '}
                ({ordinal(m.rankBefore)} to {ordinal(m.rankNow)})
              </span>
            )}
          </li>
        ))}
        {b.movers.length > 6 && <li className="text-ink-faint">and {b.movers.length - 6} more</li>}
      </ul>
    </div>
  )
}
