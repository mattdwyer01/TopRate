import { projectedAtActualScale } from './atw'
import type { Race, Runner } from '../types/domain'
import { BUSH_TRACK_THRESHOLD } from './meetings'

// Race-level results review: for every race with a known winner, the model's #1 pick (highest Proj) against the
// market favourite (shortest settled price) and the actual winner. Reads races directly, not the runner-level
// accuracy rows, so it does not need an actual WPR and covers a race as soon as the winner is known.

export interface DayRace {
  raceId: string
  date: string
  venue: string
  raceNumber: number
  startTime: string
  winner: Runner | null
  winnerModelRank: number | null
  winnerPrice: number | null
  modelTop: Runner | null
  modelTopWon: boolean
  modelTopFinish: number | null
  favourite: Runner | null
  favouriteWon: boolean
  favouriteFinish: number | null
}

export interface DaySummary {
  date: string
  races: DayRace[]
  modelWins: number
  favouriteWins: number
  // Races where both a model pick and a unique favourite exist: the like-for-like pool for the two win counts.
  comparable: number
}

function price(r: Runner): number | null {
  // Settled price when it exists; the last fixed price stands in until the SP is filled (same-day races).
  return r.startingPrice ?? r.postRaceTopPrice ?? r.fixedWinPrice ?? null
}

export function computeDayRace(race: Race): DayRace | null {
  const live = race.runners.filter((r) => !r.dataScratched)
  const winner = live.find((r) => r.finishPosition === 1) ?? null
  if (!winner) return null
  const rated = live.filter((r) => r.projectedWpr != null).sort((a, b) => (projectedAtActualScale(b) as number) - (projectedAtActualScale(a) as number))
  const modelTop = rated[0] ?? null
  const winnerIdx = rated.findIndex((r) => r.runId === winner.runId)
  const priced = live.filter((r) => price(r) != null)
  let favourite: Runner | null = null
  if (priced.length) {
    const best = priced.reduce((a, b) => ((price(b) as number) < (price(a) as number) ? b : a))
    // Joint favourites: no single favourite to compare against.
    if (priced.filter((r) => price(r) === price(best)).length === 1) favourite = best
  }
  return {
    raceId: race.raceId,
    date: race.date,
    venue: race.venue,
    raceNumber: race.raceNumber,
    startTime: race.startTime,
    winner,
    winnerModelRank: winnerIdx >= 0 ? winnerIdx + 1 : null,
    winnerPrice: price(winner),
    modelTop,
    modelTopWon: modelTop?.runId === winner.runId,
    modelTopFinish: modelTop?.finishPosition ?? null,
    favourite,
    favouriteWon: favourite?.runId === winner.runId,
    favouriteFinish: favourite?.finishPosition ?? null,
  }
}

/** Day summaries, newest first. */
export function computeDays(races: Race[], excludeBush: boolean): DaySummary[] {
  const byDate = new Map<string, DayRace[]>()
  for (const race of races) {
    if (excludeBush && (race.prizeMoney ?? 0) <= BUSH_TRACK_THRESHOLD) continue
    const d = computeDayRace(race)
    if (!d) continue
    const g = byDate.get(d.date)
    if (g) g.push(d)
    else byDate.set(d.date, [d])
  }
  const days: DaySummary[] = []
  for (const [date, list] of byDate) {
    list.sort((a, b) => a.startTime.localeCompare(b.startTime))
    const both = list.filter((r) => r.modelTop && r.favourite)
    days.push({
      date,
      races: list,
      modelWins: both.filter((r) => r.modelTopWon).length,
      favouriteWins: both.filter((r) => r.favouriteWon).length,
      comparable: both.length,
    })
  }
  return days.sort((a, b) => b.date.localeCompare(a.date))
}

export interface WeekTrend {
  weekStart: string // Monday, YYYY-MM-DD
  races: number
  modelPct: number
  favouritePct: number
}

function mondayOf(iso: string): string {
  const d = new Date(`${iso}T00:00:00Z`)
  const dow = (d.getUTCDay() + 6) % 7 // Monday = 0
  d.setUTCDate(d.getUTCDate() - dow)
  return d.toISOString().slice(0, 10)
}

/** Weekly strike rate of the model's #1 pick and the favourite, on the like-for-like races, oldest first. */
export function computeWeeklyTrend(days: DaySummary[], minRaces = 20): WeekTrend[] {
  const weeks = new Map<string, { n: number; m: number; f: number }>()
  for (const day of days) {
    const w = mondayOf(day.date)
    const cur = weeks.get(w) ?? { n: 0, m: 0, f: 0 }
    cur.n += day.comparable
    cur.m += day.modelWins
    cur.f += day.favouriteWins
    weeks.set(w, cur)
  }
  return [...weeks.entries()]
    .filter(([, v]) => v.n >= minRaces)
    .map(([weekStart, v]) => ({ weekStart, races: v.n, modelPct: (v.m / v.n) * 100, favouritePct: (v.f / v.n) * 100 }))
    .sort((a, b) => a.weekStart.localeCompare(b.weekStart))
}
