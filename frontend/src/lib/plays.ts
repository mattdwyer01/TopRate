import type { Race, Runner } from '../types/domain'
import { computeEffectiveRace, INNER_GAP_FROM_TOP, OUTER_GAP_FROM_TOP, MAP_POOL_MIN_SM, MAP_VALUE_MIN_SM, type EffectiveRunner } from './raceModel'
import { rankField } from '../features/race/raceFacts'
import { MIN_BIAS_RACES, racesRunBefore, runnerBias, withoutBias, type NoBias } from './bias'

// The Plays tab: the runners the dashboard flags, kept for the day (and after the race has run) with how they went.
// Everything is read from the projections the page already holds (the log's pre-race projection for a race that has run), so a play never
// changes after the jump. No bet is implied: these are filters, and the scoreboard exists to show whether they pay.
export type PlayKind = 'lead' | 'map4' | 'value'

// #1 on projection, clear of the second rated by at least this many WPR. Out-of-sample (14,438 races, 9 Oct 2026): 43% to win, about 71% to place, ROI
// about -10% on its own and about 0% with a favourable map.
export const PLAY_LEAD_MIN = 4

export const PLAY_KINDS: { kind: PlayKind; label: string; short: string; help: string }[] = [
  { kind: 'lead', label: `#1 rated, ${PLAY_LEAD_MIN}+ clear`, short: '#1 clear', help: `Top projection, leading the second rated by ${PLAY_LEAD_MIN} WPR or more.` },
  { kind: 'map4', label: `Map +${MAP_POOL_MIN_SM} within ${INNER_GAP_FROM_TOP}`, short: `Map +${MAP_POOL_MIN_SM}`, help: `Within ${INNER_GAP_FROM_TOP} WPR of the top rated with a speed map (SM) of +${MAP_POOL_MIN_SM} or better against its own field.` },
  { kind: 'value', label: `Map +${MAP_VALUE_MIN_SM}, ${INNER_GAP_FROM_TOP} to ${OUTER_GAP_FROM_TOP} off`, short: `Map +${MAP_VALUE_MIN_SM}`, help: `${INNER_GAP_FROM_TOP} to ${OUTER_GAP_FROM_TOP} WPR off the top with a speed map of +${MAP_VALUE_MIN_SM} or better: the one group outside the inner line that has paid in testing.` },
]

export type Outcome = 'won' | 'placed' | 'unplaced' | 'pending'

export interface Play {
  key: string
  race: Race
  runner: Runner
  eff: EffectiveRunner | undefined
  kinds: PlayKind[]
  // Kinds this runner qualified for earlier today but no longer does (a late projection or price change). Kept so a play does not vanish.
  droppedKinds: PlayKind[]
  // Kinds it qualifies for only because of the day-of track bias (it would not without it), and kinds it lost only because of it.
  biasGained: PlayKind[]
  biasLost: PlayKind[]
  // How far the track bias moved this runner's projection (WPR), 0 when none was read.
  bias: number
  rank: number
  fieldSize: number
  fieldTop: number
  fieldLow: number
  gap: number
  // The top rated's lead over the second rated (only meaningful for the #1).
  lead: number
  sm: number | null
  price: number | null
  isFavourite: boolean
  outcome: Outcome
}

/** Paying places for a field: 3 for 8 or more runners, 2 for 5 to 7, none below. */
export function placesPaid(starters: number): number {
  return starters >= 8 ? 3 : starters >= 5 ? 2 : 0
}

function outcomeOf(runner: Runner, starters: number): Outcome {
  if (runner.won || runner.finishPosition === 1) return 'won'
  const places = placesPaid(starters)
  if (runner.finishPosition != null) return places > 0 && runner.finishPosition <= places ? 'placed' : 'unplaced'
  if (runner.resultKnown) return 'unplaced'
  return 'pending'
}

export const playPrice = (r: Runner): number | null => r.startingPrice ?? r.fixedWinPrice

function kindsFor(main: boolean, light: boolean, isTop: boolean, lead: number, gap: number, sm: number | null): PlayKind[] {
  const kinds: PlayKind[] = []
  if (!main) return kinds
  if (isTop && lead >= PLAY_LEAD_MIN) kinds.push('lead')
  if (!light && sm != null) {
    if (gap <= INNER_GAP_FROM_TOP && sm >= MAP_POOL_MIN_SM) kinds.push('map4')
    if (gap > INNER_GAP_FROM_TOP && gap <= OUTER_GAP_FROM_TOP && sm >= MAP_VALUE_MIN_SM) kinds.push('value')
  }
  return kinds
}

/**
 * Plays for the given races, in race order. `seen` holds kinds a runner qualified for earlier (raceId|runId -> kinds), so a play that stopped
 * qualifying before the jump still shows, marked as dropped.
 */
export function computePlays(
  races: Race[],
  ctx: { deltas: Record<string, number>; bases: Record<string, number>; scratched: Set<string>; priceBeta: number | null },
  seen?: Map<string, PlayKind[]>,
): Play[] {
  const out: Play[] = []
  for (const race of races) {
    // Races with a first starter are left out: the rules were not tested where a debutant is in the field.
    if (race.runners.some((r) => !r.dataScratched && !ctx.scratched.has(r.runId) && r.formHistory.length === 0)) continue
    const eff = new Set(ctx.scratched)
    for (const r of race.runners) if (r.dataScratched) eff.add(r.runId)
    const effective = computeEffectiveRace(race.runners, ctx.deltas, ctx.bases, ctx.priceBeta, eff)
    const ranked = rankField(race.runners, effective, eff, INNER_GAP_FROM_TOP, OUTER_GAP_FROM_TOP)
    if (ranked.length < 5) continue
    const starters = race.runners.filter((r) => !r.dataScratched).length
    const top = ranked[0].proj
    const low = ranked[ranked.length - 1].proj
    const lead = top - ranked[1].proj
    let minPrice = Infinity
    for (const x of ranked) {
      const p = playPrice(x.runner)
      if (p != null && p < minPrice) minPrice = p
    }
    // The same race as it stood before the earlier races at the meeting ran (track bias taken out), to say which flags the bias created or removed.
    const biasShown = racesRunBefore(race, races) >= MIN_BIAS_RACES
    const nb = biasShown ? withoutBias(ranked) : new Map<string, NoBias>()
    const nbRows = ranked.map((x) => ({ x, proj: nb.get(x.runner.runId)?.proj ?? x.proj, sm: nb.has(x.runner.runId) ? (nb.get(x.runner.runId)?.sm ?? null) : (x.eff?.speedMapAdj ?? null) })).sort((p, q) => q.proj - p.proj)
    const nbTop = nbRows[0].proj
    const nbLead = nbTop - nbRows[1].proj
    const nbKinds = new Map<string, PlayKind[]>()
    nbRows.forEach((row, i) => {
      const m = row.x.runner.projectionModel === 'main'
      nbKinds.set(row.x.runner.runId, kindsFor(m, row.x.eff?.speedMapLight ?? false, i === 0, nbLead, nbTop - row.proj, row.sm))
    })
    ranked.forEach((x, i) => {
      const main = x.runner.projectionModel === 'main'
      const sm = x.eff?.speedMapAdj ?? null
      const kinds = kindsFor(main, x.eff?.speedMapLight ?? false, i === 0, lead, x.gap, sm)
      const without = nbKinds.get(x.runner.runId) ?? []
      const biasGained = kinds.filter((k) => !without.includes(k))
      const biasLost = without.filter((k) => !kinds.includes(k))
      const key = `${race.raceId}|${x.runner.runId}`
      const before = seen?.get(key) ?? []
      if (kinds.length === 0 && before.length === 0 && biasLost.length === 0) return
      const price = playPrice(x.runner)
      out.push({
        key,
        race,
        runner: x.runner,
        eff: x.eff,
        kinds,
        droppedKinds: [...new Set([...before.filter((k) => !kinds.includes(k)), ...biasLost])],
        biasGained,
        biasLost,
        bias: biasShown ? runnerBias(x.runner) : 0,
        rank: i + 1,
        fieldSize: ranked.length,
        fieldTop: top,
        fieldLow: low,
        gap: x.gap,
        lead,
        sm,
        price,
        isFavourite: price != null && price === minPrice,
        outcome: outcomeOf(x.runner, starters),
      })
    })
  }
  return out.sort((a, b) => (a.race.startTime ?? '').localeCompare(b.race.startTime ?? '') || a.race.raceNumber - b.race.raceNumber || a.runner.tabNumber - b.runner.tabNumber)
}

export interface TrackRow {
  id: string
  label: string
  short: string
  test: (p: Play) => boolean
}

// What the scoreboard follows. The first three are the plays; the rest are the tighter versions the 15-month test pointed at.
export const TRACK_ROWS: TrackRow[] = [
  { id: 'lead', label: `#1 rated, ${PLAY_LEAD_MIN}+ clear`, short: `#1 ${PLAY_LEAD_MIN}+ clear`, test: (p) => p.kinds.includes('lead') },
  { id: 'leadfav', label: `#1 ${PLAY_LEAD_MIN}+ clear and market favourite`, short: '... and favourite', test: (p) => p.kinds.includes('lead') && p.isFavourite },
  { id: 'map4', label: `Map +${MAP_POOL_MIN_SM} within ${INNER_GAP_FROM_TOP}`, short: `Map +${MAP_POOL_MIN_SM} in ${INNER_GAP_FROM_TOP}`, test: (p) => p.kinds.includes('map4') },
  { id: 'map4p5', label: `Map +${MAP_POOL_MIN_SM} within ${INNER_GAP_FROM_TOP}, over $5`, short: '... over $5', test: (p) => p.kinds.includes('map4') && (p.price ?? 0) > 5 },
  { id: 'map4p5f10', label: `Map +${MAP_POOL_MIN_SM} within ${INNER_GAP_FROM_TOP}, over $5, 10+ runners`, short: '... over $5, 10+ runners', test: (p) => p.kinds.includes('map4') && (p.price ?? 0) > 5 && p.fieldSize >= 10 },
  { id: 'value', label: `Map +${MAP_VALUE_MIN_SM}, ${INNER_GAP_FROM_TOP} to ${OUTER_GAP_FROM_TOP} off`, short: `Map +${MAP_VALUE_MIN_SM}, ${INNER_GAP_FROM_TOP}-${OUTER_GAP_FROM_TOP} off`, test: (p) => p.kinds.includes('value') },
]

export interface Tally {
  plays: number
  run: number
  wins: number
  places: number
  avgPrice: number | null
  // Flat $1 on the win at SP (else the last fixed price), over run plays that had a price.
  roi: number | null
}

export function tally(plays: Play[]): Tally {
  const run = plays.filter((p) => p.outcome !== 'pending')
  const wins = run.filter((p) => p.outcome === 'won').length
  const places = run.filter((p) => p.outcome === 'won' || p.outcome === 'placed').length
  const priced = run.filter((p) => p.price != null && p.price > 1)
  const ret = priced.reduce((s, p) => s + (p.outcome === 'won' ? (p.price as number) - 1 : -1), 0)
  return {
    plays: plays.length,
    run: run.length,
    wins,
    places,
    avgPrice: priced.length ? priced.reduce((s, p) => s + (p.price as number), 0) / priced.length : null,
    roi: priced.length ? ret / priced.length : null,
  }
}
