// Betting rules from racing-model's tests on pre-race dashboard values (3 Oct 2026, racing-model
// reports/dashboard_review.md, exotics_test.md; rules page https://claude.ai/artifact/9uJiHLuBBBqQXDeQJdRZuz).
// Evaluated live on the race page from the same numbers the table shows: Combo gap from the top pick
// (computeCompositeGaps) and the SM column (EffectiveRunner.speedMapAdj, demeaned, +/-0.5 = green / red).
//   Win:      Combo top pick 4+ points clear of the 2nd, SM >= +0.5, no first starter in the race; stake so it returns $200.
//   Trifecta: 1st / 2nd from within 4, 3rd from the 8 line (within 4, or 4-8 back with SM > -0.5); at least one
//             within-4 runner with SM >= +0.5 (without one: 107 races +4% vs +26%); no first starter in the race;
//             skip over 36 combinations; $10 flexi.
//   Quinella: box the within-4 runners when there are 2 to 4 of them (<= 6 combinations); first starters allowed
//             (they did not hurt quinellas in the test); $15 flexi.
//   Quaddie:  main quaddie (last 4 races of the meeting); each leg = the 8 line set; skip if any leg has a first
//             starter or the ticket is over 400 combinations; $25 flexi. Early quaddie: the 4 races before the main
//             quaddie (races 1-4, overlapping the main, at meetings of 7 races or fewer); same rule, $25 flexi.
//   Heavy track (going Heavy, any leg for a quaddie): every stake halved (user rule, 3 Oct 2026).
// First starters come from the race-level flag (hasFirstStarter, set when the field was fetched).
import type { Race, Runner } from '../types/domain'
import { computeCompositeGaps, computeEffectiveRace, type EffectiveRunner } from './raceModel'

export const INNER = 4
export const OUTER = 8
export const SM_T = 0.5
// Win stake: the bet RETURNS $200 at the fixed price (stake x price = 200), same as bet_log.py
export const WIN_RETURN = 200
export const TRI_CAP = 36
export const TRI_STAKE = 10
export const QUIN_CAP = 6
export const QUIN_STAKE = 15
export const QUAD_CAP = 400
export const QUAD_STAKE = 25
export const EARLY_QUAD_STAKE = 25

// Heavy track: halve every stake
export function isHeavy(race: Race): boolean {
  return /heavy/i.test(race.going ?? '')
}
export function stakeFactor(races: Race[]): number {
  return races.some(isHeavy) ? 0.5 : 1
}

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
  stake: number | null // returns WIN_RETURN (halved on a heavy track) at the current fixed price
  target: number // the return aimed for: WIN_RETURN, or half on a heavy track
}

export function winBet(race: Race, s: RaceSets): WinBet | null {
  if (race.hasFirstStarter || !s.top || s.clear == null || s.clear < INNER) return null
  if (s.top.sm == null || s.top.sm < SM_T) return null
  const price = s.top.runner.fixedWinPrice
  const target = WIN_RETURN * stakeFactor([race])
  return { sel: s.top, price, target, stake: price != null && price > 1 ? target / price : null }
}

export interface TriBet {
  firstSecond: Sel[]
  third: Sel[]
  combos: number
  stake: number
  skip: string | null // reason when not played
}

export function trifecta(race: Race, s: RaceSets): TriBet | null {
  if (s.inner.length < 2) return null
  // 1st and 2nd distinct runners from inner (inner is inside outer), 3rd any other outer runner
  const combos = s.inner.length * (s.inner.length - 1) * Math.max(0, s.outer.length - 2)
  let skip: string | null = null
  if (race.hasFirstStarter) skip = 'first starter in the race'
  else if (!s.inner.some((x) => x.sm != null && x.sm >= SM_T)) skip = 'no green SM within 4'
  else if (s.outer.length < 3) skip = 'fewer than 3 runners in the 8 line set'
  else if (combos > TRI_CAP) skip = `${combos} combinations, over the ${TRI_CAP} cap`
  return { firstSecond: s.inner, third: s.outer, combos, stake: TRI_STAKE * stakeFactor([race]), skip }
}

export interface QuinBet {
  box: Sel[]
  combos: number
  stake: number
  skip: string | null
}

export function quinella(race: Race, s: RaceSets): QuinBet | null {
  if (s.inner.length < 2) return null
  const combos = (s.inner.length * (s.inner.length - 1)) / 2
  const skip = combos > QUIN_CAP ? `${s.inner.length} runners within 4, over the box-of-4 cap` : null
  return { box: s.inner, combos, stake: QUIN_STAKE * stakeFactor([race]), skip }
}

export interface QuadLeg {
  race: Race
  outer: Sel[]
}

export interface QuadBet {
  legs: QuadLeg[]
  combos: number
  stake: number
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
  const base = kind === 'early' ? EARLY_QUAD_STAKE : QUAD_STAKE
  return { legs, combos, stake: base * stakeFactor(legs.map((l) => l.race)), skip }
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
