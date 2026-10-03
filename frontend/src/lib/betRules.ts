// Betting rules from racing-model's tests on pre-race dashboard values (3 Oct 2026, racing-model
// reports/dashboard_review.md, exotics_test.md; rules page https://claude.ai/artifact/9uJiHLuBBBqQXDeQJdRZuz).
// Evaluated live on the race page from the same numbers the table shows: Combo gap from the top pick
// (computeCompositeGaps) and the SM column (EffectiveRunner.speedMapAdj, demeaned, +/-0.5 = green / red).
//   Win:      Combo top pick 4+ points clear of the 2nd, SM >= +0.5, no first starter in the race; to win $200.
//   Trifecta: 1st / 2nd from within 4, 3rd from the 8 line (within 4, or 4-8 back with SM > -0.5); no first
//             starter in the race; skip over 36 combinations; $20 flexi.
//   Quaddie:  main quaddie (last 4 races of the meeting); each leg = the 8 line set; skip if any leg has a first
//             starter or the ticket is over 400 combinations; $30 flexi. Early quaddie: the 4 races before the main
//             quaddie (races 1-4, overlapping the main, at meetings of 7 races or fewer); same rule, $15 flexi.
// First starters come from the race-level flag (hasFirstStarter, set when the field was fetched).
import type { Race, Runner } from '../types/domain'
import { computeCompositeGaps, computeEffectiveRace, type EffectiveRunner } from './raceModel'

export const INNER = 4
export const OUTER = 8
export const SM_T = 0.5
export const WIN_TARGET = 200
export const TRI_CAP = 36
export const TRI_STAKE = 20
export const QUAD_CAP = 400
export const QUAD_STAKE = 30
export const EARLY_QUAD_STAKE = 15 // half stake until real early quaddie dividends confirm it

export interface Sel {
  runner: Runner
  gap: number
  sm: number | null
}

export interface RaceSets {
  inner: Sel[] // within 4
  outer: Sel[] // the 8 line set (includes inner)
  top: Sel | null
  clear: number | null // top pick's margin over the 2nd
}

export function raceSets(
  runners: Runner[],
  gaps: Record<string, number | null>,
  effective: Record<string, EffectiveRunner>,
  scratched: Set<string>,
): RaceSets {
  const live: Sel[] = runners
    .filter((r) => !scratched.has(r.runId) && gaps[r.runId] != null)
    .map((r) => ({ runner: r, gap: gaps[r.runId] as number, sm: effective[r.runId]?.speedMapAdj ?? null }))
    .sort((a, b) => a.gap - b.gap)
  const inner = live.filter((s) => s.gap <= INNER)
  const outer = live.filter((s) => s.gap <= INNER || (s.gap <= OUTER && !(s.sm != null && s.sm <= -SM_T)))
  return { inner, outer, top: live[0] ?? null, clear: live.length > 1 ? live[1].gap - live[0].gap : null }
}

export interface WinBet {
  sel: Sel
  price: number | null
  stake: number | null // to win WIN_TARGET at the current fixed price
}

export function winBet(race: Race, s: RaceSets): WinBet | null {
  if (race.hasFirstStarter || !s.top || s.clear == null || s.clear < INNER) return null
  if (s.top.sm == null || s.top.sm < SM_T) return null
  const price = s.top.runner.fixedWinPrice
  return { sel: s.top, price, stake: price != null && price > 1 ? WIN_TARGET / (price - 1) : null }
}

export interface TriBet {
  firstSecond: Sel[]
  third: Sel[]
  combos: number
  skip: string | null // reason when not played
}

export function trifecta(race: Race, s: RaceSets): TriBet | null {
  if (s.inner.length < 2) return null
  // 1st and 2nd distinct runners from inner (inner is inside outer), 3rd any other outer runner
  const combos = s.inner.length * (s.inner.length - 1) * Math.max(0, s.outer.length - 2)
  let skip: string | null = null
  if (race.hasFirstStarter) skip = 'first starter in the race'
  else if (s.outer.length < 3) skip = 'fewer than 3 runners in the 8 line set'
  else if (combos > TRI_CAP) skip = `${combos} combinations, over the ${TRI_CAP} cap`
  return { firstSecond: s.inner, third: s.outer, combos, skip }
}

export interface QuadLeg {
  race: Race
  outer: Sel[]
}

export interface QuadBet {
  legs: QuadLeg[]
  combos: number
  skip: string | null
}

// Main quaddie = the last 4 races of the meeting. Early quaddie = the 4 races before it, or races 1-4 (overlapping
// the main) when the meeting has 7 races or fewer. Returns null when this race is not one of the legs.
export function quaddieLegNumbers(meetingRaces: Race[], kind: 'main' | 'early'): number[] | null {
  const nos = [...new Set(meetingRaces.map((r) => r.raceNumber))].sort((a, b) => a - b)
  if (kind === 'main') return nos.length >= 4 ? nos.slice(-4) : null
  if (nos.length >= 8) return nos.slice(-8, -4)
  return nos.length >= 5 ? nos.slice(0, 4) : null
}

export function quaddie(
  race: Race,
  meetingRaces: Race[],
  setsFor: (r: Race) => RaceSets,
  kind: 'main' | 'early' = 'main',
): QuadBet | null {
  const legNos = quaddieLegNumbers(meetingRaces, kind)
  if (!legNos || !legNos.includes(race.raceNumber)) return null
  const legs: QuadLeg[] = []
  for (const n of legNos) {
    const r = n === race.raceNumber ? race : meetingRaces.find((x) => x.raceNumber === n)
    if (!r) return null
    legs.push({ race: r, outer: setsFor(r).outer })
  }
  const combos = legs.reduce((p, l) => p * l.outer.length, 1)
  let skip: string | null = null
  const fsLeg = legs.find((l) => l.race.hasFirstStarter)
  if (fsLeg) skip = `first starter in R${fsLeg.race.raceNumber}`
  else if (legs.some((l) => l.outer.length === 0)) skip = 'a leg has no Combo ratings yet'
  else if (combos > QUAD_CAP) skip = `${combos} combinations, over the ${QUAD_CAP} cap`
  return { legs, combos, skip }
}

// Sets for another race at the meeting, built the same way RaceDetail builds this race's (its own effective
// runners and Combo gaps, with this device's manual edits and scratchings applied).
export function setsForRace(
  r: Race,
  deltas: Record<string, number>,
  bases: Record<string, number>,
  priceBeta: number | null,
  manualScratched: Set<string>,
): RaceSets {
  const scr = new Set(manualScratched)
  for (const u of r.runners) if (u.dataScratched) scr.add(u.runId)
  const eff = computeEffectiveRace(r.runners, deltas, bases, priceBeta, scr)
  const gaps = computeCompositeGaps(r.runners, eff, scr)
  return raceSets(r.runners, gaps, eff, scr)
}
