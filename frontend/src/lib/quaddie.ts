import type { Race } from '../types/domain'

export type QuaddieKind = 'late' | 'early'

const WINDOW = 4

// TAB's real quaddie legs, checked against its dividend log (tab_dividends.csv, 2 to 7 Oct 2026, 38 meetings): the late quaddie always ends on a
// meeting's last race (38 of 38) and the early quaddie ends on race max(4, N - 4) for an N-race meeting (36 of 36). So the late quaddie is the
// last four races, the early quaddie is the four before it, and with 7 races or fewer the two overlap. Meetings of 5 races ran no early quaddie.
export function quaddieRaces(meeting: Race[], kind: QuaddieKind): Race[] {
  const n = meeting.length
  if (kind === 'late') return meeting.slice(Math.max(0, n - WINDOW))
  const end = Math.max(WINDOW, n - WINDOW)
  return meeting.slice(end - WINDOW, end)
}

export function hasQuaddie(meeting: Race[]): boolean {
  return meeting.length >= WINDOW
}

export function hasEarlyQuaddie(meeting: Race[]): boolean {
  return meeting.length >= 6
}

// Combination counts for boxed and keyed bets over a pool of n runners (b = pool, a = the keyed first-place runners, a inside b).
export const quinellaBox = (n: number) => (n >= 2 ? (n * (n - 1)) / 2 : 0)
export const trifectaBox = (n: number) => (n >= 3 ? n * (n - 1) * (n - 2) : 0)
export const firstFourBox = (n: number) => (n >= 4 ? n * (n - 1) * (n - 2) * (n - 3) : 0)
export const trifectaKey = (a: number, b: number) => (a >= 1 && b >= 3 ? a * (b - 1) * (b - 2) : 0)
export const firstFourKey = (a: number, b: number) => (a >= 1 && b >= 4 ? a * (b - 1) * (b - 2) * (b - 3) : 0)

export const product = (ns: number[]) => ns.reduce((a, b) => a * b, 1)

export function fmtMoney(v: number): string {
  return v >= 100 ? `$${Math.round(v).toLocaleString()}` : `$${v.toFixed(2)}`
}
