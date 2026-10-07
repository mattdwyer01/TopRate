import { useMemo, useState } from 'react'
import type { Race } from '../../types/domain'
import { Pill } from '../../components/Pill'
import { computeEffectiveRace, INNER_GAP_FROM_TOP, OUTER_GAP_FROM_TOP, SPEED_MAP_TINT_THRESHOLD } from '../../lib/raceModel'
import { fmtWpr } from '../../lib/format'
import { fmtAdj, smClass } from './rowParts'
import { formatTimeOfDay } from '../../lib/countdown'
import { raceStatus, STATUS_PILL_TONE } from '../../lib/raceStatus'
import { Ladder } from './RaceGlance'
import { rankField, type Ranked } from './raceFacts'

interface MultiRaceProps {
  meeting: Race[] // the meeting's races, in race order
  startRaceId: string
  deltas: Record<string, number>
  bases: Record<string, number>
  scratched: Set<string>
  priceBeta: number | null
  onSelectRace: (raceId: string, date: string, runId?: string) => void
  onBack: () => void
}

const WINDOW = 4

function rankRace(race: Race, deltas: Record<string, number>, bases: Record<string, number>, scratched: Set<string>, priceBeta: number | null): Ranked[] {
  const eff = new Set(scratched)
  for (const r of race.runners) if (r.dataScratched) eff.add(r.runId)
  const effective = computeEffectiveRace(race.runners, deltas, bases, priceBeta, eff)
  return rankField(race.runners, effective, eff, INNER_GAP_FROM_TOP, OUTER_GAP_FROM_TOP)
}

// A runner outside the outer line is added back when its speed-map adjustment is clearly favourable (the green threshold in the table and map).
const mapAdded = (x: Ranked) => !x.inner && !x.outer && (x.eff?.speedMapAdj ?? -Infinity) >= SPEED_MAP_TINT_THRESHOLD
const inPool = (x: Ranked) => x.inner || x.outer || mapAdded(x)

const product = (ns: number[]) => ns.reduce((a, b) => a * b, 1)

// Four consecutive races at one meeting side by side (the last four make the quaddie): each race's projection ladder with the inside-4 and
// inside-6 lines, and how many runners sit inside each line. The combination counts are plain arithmetic on those counts, not a selection.
export function MultiRace({ meeting, startRaceId, deltas, bases, scratched, priceBeta, onSelectRace, onBack }: MultiRaceProps) {
  const startIdx0 = Math.max(0, meeting.findIndex((r) => r.raceId === startRaceId))
  const maxStart = Math.max(0, meeting.length - WINDOW)
  const [start, setStart] = useState(Math.min(startIdx0, maxStart))
  const races = useMemo(() => meeting.slice(start, start + WINDOW), [meeting, start])

  const ranked = useMemo(() => races.map((r) => rankRace(r, deltas, bases, scratched, priceBeta)), [races, deltas, bases, scratched, priceBeta])
  const inner = ranked.map((rk) => rk.filter((x) => x.inner).length)
  const outer = ranked.map((rk) => rk.filter((x) => x.inner || x.outer).length)
  const pool = ranked.map((rk) => rk.filter(inPool).length)
  const complete = races.length === WINDOW && inner.every((n) => n > 0)

  return (
    <div className="flex flex-col gap-4">
      <div className="flex flex-wrap items-center justify-between gap-2">
        <button type="button" onClick={onBack} className="w-fit text-sm text-emerald hover:underline">
          &larr; Back to race
        </button>
        <div className="flex items-center gap-1.5 text-sm">
          <button
            type="button"
            aria-label="Earlier races"
            disabled={start <= 0}
            onClick={() => setStart((s) => Math.max(0, s - 1))}
            className="rounded-md border border-line bg-panel px-2 py-1 text-ink-mute enabled:hover:text-ink disabled:opacity-40"
          >
            &lsaquo;
          </button>
          <span className="font-mono text-xs text-ink-soft">
            {races[0] ? `R${races[0].raceNumber} to R${races[races.length - 1].raceNumber}` : ''}
          </span>
          <button
            type="button"
            aria-label="Later races"
            disabled={start >= maxStart}
            onClick={() => setStart((s) => Math.min(maxStart, s + 1))}
            className="rounded-md border border-line bg-panel px-2 py-1 text-ink-mute enabled:hover:text-ink disabled:opacity-40"
          >
            &rsaquo;
          </button>
        </div>
      </div>

      <section className="rounded-lg border border-line bg-panel p-3 sm:p-4">
        <h2 className="text-sm font-semibold text-ink">
          {races[0]?.venue}: {races.length} races side by side
        </h2>
        <p className="mb-2 text-xs text-ink-faint">
          Runners inside the {INNER_GAP_FROM_TOP} and {OUTER_GAP_FROM_TOP} WPR lines of each race&apos;s top projection. Inside {OUTER_GAP_FROM_TOP} held about 78% of winners in testing, so a leg
          is rarely safe with fewer. Runners outside the {OUTER_GAP_FROM_TOP} line are added back when their speed map adjustment is +{SPEED_MAP_TINT_THRESHOLD} or better (the green figure in the race table). Counts only, not tips.
        </p>
        <div className="overflow-x-auto">
          <table className="w-full min-w-[320px] text-xs">
            <thead className="text-left text-ink-mute">
              <tr>
                <th className="py-1 font-medium" />
                {races.map((r) => (
                  <th key={r.raceId} className="py-1 text-right font-medium">R{r.raceNumber}</th>
                ))}
                <th className="py-1 text-right font-medium">Combos</th>
              </tr>
            </thead>
            <tbody className="divide-y divide-line-soft">
              <tr>
                <td className="py-1">Inside {INNER_GAP_FROM_TOP}</td>
                {inner.map((n, i) => (
                  <td key={i} className="py-1 text-right font-mono">{n}</td>
                ))}
                <td className="py-1 text-right font-mono font-semibold">{complete ? product(inner).toLocaleString() : '-'}</td>
              </tr>
              <tr>
                <td className="py-1">Inside {OUTER_GAP_FROM_TOP}</td>
                {outer.map((n, i) => (
                  <td key={i} className="py-1 text-right font-mono">{n}</td>
                ))}
                <td className="py-1 text-right font-mono font-semibold">{outer.every((n) => n > 0) && races.length === WINDOW ? product(outer).toLocaleString() : '-'}</td>
              </tr>
              <tr>
                <td className="py-1">Inside {OUTER_GAP_FROM_TOP} + favoured map</td>
                {pool.map((n, i) => (
                  <td key={i} className="py-1 text-right font-mono">{n}</td>
                ))}
                <td className="py-1 text-right font-mono font-semibold">{pool.every((n) => n > 0) && races.length === WINDOW ? product(pool).toLocaleString() : '-'}</td>
              </tr>
            </tbody>
          </table>
        </div>
      </section>

      <div className="grid grid-cols-1 gap-4 lg:grid-cols-2">
        {races.map((race, i) => {
          const status = raceStatus(race, Date.now())
          return (
            <section key={race.raceId} className="rounded-lg border border-line bg-panel p-3 shadow-[var(--shadow-1)]">
              <div className="mb-1 flex flex-wrap items-center justify-between gap-2">
                <button type="button" onClick={() => onSelectRace(race.raceId, race.date)} className="text-left text-sm font-semibold text-ink hover:text-emerald-deep">
                  R{race.raceNumber} {race.raceName}
                </button>
                <Pill active={false} tone={STATUS_PILL_TONE[status]} onClick={() => onSelectRace(race.raceId, race.date)}>
                  {status === 'resulted' || status === 'interim' ? 'Resulted' : formatTimeOfDay(race.startTime)}
                </Pill>
              </div>
              <div className="mb-1 text-[11px] text-ink-faint">
                {race.distance}m · {race.going || 'going n/a'} · {ranked[i].length} runners · inside {INNER_GAP_FROM_TOP}: {inner[i]} · inside {OUTER_GAP_FROM_TOP}: {outer[i]} · with map: {pool[i]}
              </div>
              {ranked[i].length >= 2 ? (
                <Ladder ranked={ranked[i]} innerGap={INNER_GAP_FROM_TOP} outerGap={OUTER_GAP_FROM_TOP} onSelect={(runId) => onSelectRace(race.raceId, race.date, runId)} />
              ) : (
                <p className="py-4 text-center text-xs text-ink-faint">No projections yet for this race.</p>
              )}
              {ranked[i].some(inPool) && (
                <table className="mt-2 w-full text-xs">
                  <thead className="text-left text-ink-mute">
                    <tr>
                      <th className="py-1 font-medium">Runner</th>
                      <th className="py-1 text-right font-medium">Proj</th>
                      <th className="py-1 text-right font-medium">Behind</th>
                      <th className="py-1 text-right font-medium">SM</th>
                    </tr>
                  </thead>
                  <tbody className="divide-y divide-line-soft">
                    {ranked[i].filter(inPool).map((x) => (
                      <tr key={x.runner.runId}>
                        <td className="py-1">
                          <button type="button" onClick={() => onSelectRace(race.raceId, race.date, x.runner.runId)} className="text-left hover:text-emerald-deep">
                            {x.runner.tabNumber}. {x.runner.horse}
                          </button>
                          {mapAdded(x) && <span className="ml-1.5 rounded border border-emerald-line bg-emerald-bg px-1 text-[10px] text-emerald-deep">map</span>}
                        </td>
                        <td className="py-1 text-right font-mono">{fmtWpr(x.proj)}</td>
                        <td className="py-1 text-right font-mono text-ink-mute">{x.gap === 0 ? 'top' : x.gap.toFixed(1)}</td>
                        <td className={`py-1 text-right font-mono ${smClass(x.eff?.speedMapAdj)}`}>{fmtAdj(x.eff?.speedMapAdj)}</td>
                      </tr>
                    ))}
                  </tbody>
                </table>
              )}
            </section>
          )
        })}
      </div>
    </div>
  )
}
