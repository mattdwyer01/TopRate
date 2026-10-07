import type { Race } from '../../types/domain'
import { computeEffectiveRace, INNER_GAP_FROM_TOP, OUTER_GAP_FROM_TOP, SPEED_MAP_TINT_THRESHOLD } from '../../lib/raceModel'
import { BUSH_TRACK_THRESHOLD } from '../../lib/meetings'
import { loggedBeforeRace, type Period } from '../../lib/accuracyStats'
import { hasEarlyQuaddie, hasQuaddie, product, quaddieRaces, type QuaddieKind } from '../../lib/quaddie'
import { rankField, type Ranked } from './raceFacts'

export function rankRace(race: Race, deltas: Record<string, number>, bases: Record<string, number>, scratched: Set<string>, priceBeta: number | null): Ranked[] {
  const eff = new Set(scratched)
  for (const r of race.runners) if (r.dataScratched) eff.add(r.runId)
  const effective = computeEffectiveRace(race.runners, deltas, bases, priceBeta, eff)
  return rankField(race.runners, effective, eff, INNER_GAP_FROM_TOP, OUTER_GAP_FROM_TOP)
}

// A runner outside the outer line is added back when its speed-map adjustment is clearly favourable (the green threshold in the table and map).
export const mapAdded = (x: Ranked) => !x.inner && !x.outer && (x.eff?.speedMapAdj ?? -Infinity) >= SPEED_MAP_TINT_THRESHOLD
export const inPool = (x: Ranked) => x.inner || x.outer || mapAdded(x)

export type PoolKey = 'inner' | 'outer' | 'map'
export const POOL_LABEL: Record<PoolKey, string> = { inner: 'Inside 4', outer: 'Inside 6', map: 'Inside 6 + favoured map' }
const POOL_TEST: Record<PoolKey, (x: Ranked) => boolean> = { inner: (x) => x.inner, outer: (x) => x.inner || x.outer, map: inPool }
export const poolMembers = (rk: Ranked[], pool: PoolKey) => rk.filter(POOL_TEST[pool])

export interface ScorecardRow {
  pool: PoolKey
  quaddies: number
  legs: number
  legsHit: number
  allFour: number
  avgPerLeg: number
  avgCombos: number
}

export interface QuaddieScorecard {
  kind: QuaddieKind
  rows: ScorecardRow[]
}

function mondayCutoff(period: Period): number | null {
  return period === 'all' || period === 'live' ? null : Date.now() - Number(period) * 86_400_000
}

/** How the pools did on past quaddies: for every meeting whose four legs have all run, did each leg's winner sit in the pool, and did all four.
 * Projections are the ones logged for the race (as shown on the dashboard), with no manual overrides. */
export function computeQuaddieScorecard(races: Race[], opts: { period: Period; excludeBush: boolean }): QuaddieScorecard[] {
  const cutoff = mondayCutoff(opts.period)
  const meetings = new Map<string, Race[]>()
  for (const r of races) {
    if (cutoff != null && new Date(r.date).getTime() < cutoff) continue
    if (opts.excludeBush && (r.prizeMoney ?? 0) <= BUSH_TRACK_THRESHOLD) continue
    const k = `${r.date}|${r.venue}`
    const g = meetings.get(k)
    if (g) g.push(r)
    else meetings.set(k, [r])
  }
  const none = new Set<string>()
  const pools: PoolKey[] = ['inner', 'outer', 'map']
  const kinds: QuaddieKind[] = ['late', 'early']
  return kinds.map((kind) => {
    const acc = pools.map(() => ({ q: 0, legs: 0, hit: 0, all: 0, perLeg: 0, combos: 0 }))
    for (const meeting of meetings.values()) {
      meeting.sort((a, b) => a.raceNumber - b.raceNumber)
      if (!hasQuaddie(meeting) || (kind === 'early' && !hasEarlyQuaddie(meeting))) continue
      const legs = quaddieRaces(meeting, kind)
      const ranked = legs.map((leg) => rankRace(leg, {}, {}, none, null))
      const winners = legs.map((leg) => leg.runners.find((r) => !r.dataScratched && r.finishPosition === 1) ?? null)
      if (winners.some((w) => w == null) || ranked.some((rk) => rk.length < 2)) continue
      if (opts.period === 'live' && !legs.every((leg, i) => loggedBeforeRace(leg, ranked[i][0].runner))) continue
      pools.forEach((pool, pi) => {
        const members = ranked.map((rk) => poolMembers(rk, pool))
        const hits = members.map((m, i) => m.some((x) => x.runner.runId === winners[i]!.runId))
        const a = acc[pi]
        a.q++
        a.legs += legs.length
        a.hit += hits.filter(Boolean).length
        if (hits.every(Boolean)) a.all++
        a.perLeg += members.reduce((s, m) => s + m.length, 0) / legs.length
        a.combos += product(members.map((m) => m.length))
      })
    }
    return {
      kind,
      rows: pools.map((pool, pi) => ({
        pool,
        quaddies: acc[pi].q,
        legs: acc[pi].legs,
        legsHit: acc[pi].hit,
        allFour: acc[pi].all,
        avgPerLeg: acc[pi].q ? acc[pi].perLeg / acc[pi].q : 0,
        avgCombos: acc[pi].q ? acc[pi].combos / acc[pi].q : 0,
      })),
    }
  })
}
