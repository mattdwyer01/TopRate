import { useMemo } from 'react'
import type { Race } from '../../types/domain'
import { computeDays, computeWeeklyTrend, type DayRace, type DaySummary } from '../../lib/dayResults'
import { fmtPrice } from '../../lib/format'

interface DayReviewProps {
  races: Race[]
  excludeBush: boolean
  onSelectRace: (raceId: string, date: string, runId?: string) => void
}

const fmtPct = (v: number) => `${v.toFixed(0)}%`

function fmtDay(iso: string): string {
  return new Date(`${iso}T00:00:00Z`).toLocaleDateString(undefined, { weekday: 'short', day: 'numeric', month: 'short', timeZone: 'UTC' })
}

// Weekly strike rate of the model's #1 pick against the market favourite, as two lines plus the numbers underneath.
function TrendChart({ weeks }: { weeks: ReturnType<typeof computeWeeklyTrend> }) {
  const W = 320
  const H = 110
  const padX = 24
  const padY = 12
  const all = weeks.flatMap((w) => [w.modelPct, w.favouritePct])
  const lo = Math.max(0, Math.floor(Math.min(...all) / 5) * 5 - 5)
  const hi = Math.min(100, Math.ceil(Math.max(...all) / 5) * 5 + 5)
  const x = (i: number) => (weeks.length === 1 ? W / 2 : padX + (i * (W - padX * 2)) / (weeks.length - 1))
  const y = (v: number) => padY + ((hi - v) * (H - padY * 2)) / (hi - lo || 1)
  const line = (key: 'modelPct' | 'favouritePct') => weeks.map((w, i) => `${i === 0 ? 'M' : 'L'}${x(i).toFixed(1)},${y(w[key]).toFixed(1)}`).join(' ')
  return (
    <svg viewBox={`0 0 ${W} ${H}`} className="w-full max-w-xl" role="img" aria-label="Weekly winner strike rate: model number one pick against the market favourite">
      {[lo, (lo + hi) / 2, hi].map((v) => (
        <g key={v}>
          <line x1={padX} x2={W - padX} y1={y(v)} y2={y(v)} stroke="var(--color-line-soft)" />
          <text x={padX - 4} y={y(v) + 3} textAnchor="end" fontSize={9} fill="var(--color-ink-faint)">{Math.round(v)}%</text>
        </g>
      ))}
      <path d={line('favouritePct')} fill="none" stroke="var(--color-slate)" strokeWidth={2} strokeDasharray="4 3" />
      <path d={line('modelPct')} fill="none" stroke="var(--color-emerald-deep)" strokeWidth={2} />
      {weeks.map((w, i) => (
        <g key={w.weekStart}>
          <circle cx={x(i)} cy={y(w.modelPct)} r={3} fill="var(--color-emerald-deep)" />
          <circle cx={x(i)} cy={y(w.favouritePct)} r={3} fill="var(--color-slate)" />
        </g>
      ))}
    </svg>
  )
}

export function WeeklyTrend({ races, excludeBush }: Omit<DayReviewProps, 'onSelectRace'>) {
  const weeks = useMemo(() => computeWeeklyTrend(computeDays(races, excludeBush)), [races, excludeBush])
  return (
    <div className="rounded-lg border border-line bg-panel p-4">
      <h3 className="text-sm font-semibold text-ink">Week by week</h3>
      {weeks.length < 2 ? (
        <p className="mt-1 text-xs text-ink-faint">Needs at least two weeks with 20 or more resulted races in the loaded window.</p>
      ) : (
        <>
          <p className="mb-2 text-xs text-ink-faint">
            Winner strike rate of the model&apos;s #1 pick (solid) against the market favourite (dashed), same races each week. Only the loaded window (about
            25 days) is covered, so expect a handful of points and wide swings.
          </p>
          <TrendChart weeks={weeks} />
          <div className="mt-2 overflow-x-auto">
            <table className="w-full text-xs">
              <thead className="text-left text-ink-mute">
                <tr>
                  <th className="py-1 font-medium">Week from</th>
                  <th className="py-1 text-right font-medium">Races</th>
                  <th className="py-1 text-right font-medium">Model #1</th>
                  <th className="py-1 text-right font-medium">Favourite</th>
                </tr>
              </thead>
              <tbody className="divide-y divide-line-soft">
                {weeks.map((w) => (
                  <tr key={w.weekStart}>
                    <td className="py-1">{fmtDay(w.weekStart)}</td>
                    <td className="py-1 text-right font-mono">{w.races}</td>
                    <td className="py-1 text-right font-mono">{fmtPct(w.modelPct)}</td>
                    <td className="py-1 text-right font-mono">{fmtPct(w.favouritePct)}</td>
                  </tr>
                ))}
              </tbody>
            </table>
          </div>
        </>
      )}
    </div>
  )
}

function ordinal(n: number): string {
  const v = n % 100
  if (v >= 11 && v <= 13) return `${n}th`
  return `${n}${['th', 'st', 'nd', 'rd'][n % 10 < 4 ? n % 10 : 0]}`
}

function Mark({ won, finish }: { won: boolean; finish: number | null }) {
  if (won) return <span className="font-semibold text-emerald-deep">won</span>
  return <span className="text-ink-mute">{finish != null ? ordinal(finish) : 'unplaced'}</span>
}

function RaceLine({ r, onSelectRace }: { r: DayRace; onSelectRace: DayReviewProps['onSelectRace'] }) {
  return (
    <li>
      <button type="button" onClick={() => onSelectRace(r.raceId, r.date)} className="grid w-full grid-cols-1 gap-x-3 gap-y-0.5 py-1.5 text-left text-xs hover:bg-bg sm:grid-cols-[9rem_1fr_1fr_1fr]">
        <span className="font-mono text-ink-mute">{r.venue} R{r.raceNumber}</span>
        <span>
          <span className="text-ink-faint">Won: </span>
          <span className="font-medium text-ink">{r.winner?.tabNumber}. {r.winner?.horse}</span>
          <span className="text-ink-faint"> {fmtPrice(r.winnerPrice)}{r.winnerModelRank != null ? `, model rank ${r.winnerModelRank}` : ''}</span>
        </span>
        <span>
          <span className="text-ink-faint">Model #1: </span>
          {r.modelTop ? (
            <>
              {r.modelTop.tabNumber}. {r.modelTop.horse} <Mark won={r.modelTopWon} finish={r.modelTopFinish} />
            </>
          ) : (
            '-'
          )}
        </span>
        <span>
          <span className="text-ink-faint">Favourite: </span>
          {r.favourite ? (
            <>
              {r.favourite.tabNumber}. {r.favourite.horse} <Mark won={r.favouriteWon} finish={r.favouriteFinish} />
            </>
          ) : (
            '-'
          )}
        </span>
      </button>
    </li>
  )
}

function DayBlock({ day, defaultOpen, onSelectRace }: { day: DaySummary; defaultOpen: boolean; onSelectRace: DayReviewProps['onSelectRace'] }) {
  return (
    <details open={defaultOpen} className="group rounded-lg border border-line bg-panel">
      <summary className="flex cursor-pointer list-none flex-wrap items-baseline justify-between gap-x-4 gap-y-1 px-4 py-2.5">
        <span className="text-sm font-semibold text-ink">{fmtDay(day.date)}</span>
        <span className="text-xs text-ink-mute">
          {day.races.length} races · model #1 won {day.modelWins} · favourite won {day.favouriteWins}
          <span className="text-ink-faint"> (of {day.comparable} like-for-like)</span>
        </span>
      </summary>
      <ul className="divide-y divide-line-soft border-t border-line px-4">
        {day.races.map((r) => (
          <RaceLine key={r.raceId} r={r} onSelectRace={onSelectRace} />
        ))}
      </ul>
    </details>
  )
}

export function DayByDay({ races, excludeBush, onSelectRace }: DayReviewProps) {
  const days = useMemo(() => computeDays(races, excludeBush), [races, excludeBush])
  if (days.length === 0) return null
  return (
    <div className="flex flex-col gap-2">
      <div>
        <h3 className="text-sm font-semibold text-ink">Day by day</h3>
        <p className="text-xs text-ink-faint">Every resulted race: the winner, the model&apos;s #1 pick and the market favourite. A single day is mostly variance, so read the run of days, not one.</p>
      </div>
      {days.map((d, i) => (
        <DayBlock key={d.date} day={d} defaultOpen={i === 0} onSelectRace={onSelectRace} />
      ))}
    </div>
  )
}
