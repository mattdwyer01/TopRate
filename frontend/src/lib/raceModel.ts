import type { Runner } from '../types/domain'
import { RATING_PER_LN } from './betSignals'

export interface EffectiveRunner {
  // The rating shown and used for ranking and gaps, at the weight carried today (ATW). Where the race has bet signals it is the bet-signal rating (the model's win
  // probabilities on the ATW scale, see lib/betSignals.ts RATING_PER_LN), otherwise the WPR projection below. Manual delta included either way.
  effectiveProjectedWpr: number | null
  // The WPR projection at today's weight (model rating + manual delta + this horse's own offset), whichever the rating above is. The waterfall, the typical
  // winning rating and the track-bias note explain this figure, not the bet-signal rating.
  projectionWpr: number | null
  ratingSource: 'bet' | 'projection'
  // The offset included in effectiveProjectedWpr (0 when the horse has none), so the model's own rating is effectiveProjectedWpr - atwOff.
  atwOff: number
  effectivePrice: number | null
  effectiveRank: number | null
  hasOverride: boolean
  scratched: boolean
  // WPR points behind the field's top-rated (effective) runner - null for a
  // scratched runner or one with no effective wpr. 0 for the top pick itself.
  gapFromTop: number | null
  // The suitability adjustment demeaned against this race's own runners (see speedMapDemeanedByRunId). null for a scratched
  // runner or one with no value.
  speedMapAdj: number | null
  // True when speedMapAdj comes from the light-history estimate (sm_light), which is lower confidence than a main-model value.
  speedMapLight: boolean
}

// The new projection model's suitability adjustment (projection/run.py: settle history, barrier fraction, field size,
// comments, day-of bias; main-model runners only, null for light-history), demeaned against THIS race's own runners.
// For display only, never fed back into any WPR number. Subtracting the race mean removes the part shared by the whole
// field and leaves the relational signal. Shared by the Speed Map tint and the race table's SM column so they cannot drift.
// A light-history runner (0-2 prior runs) has no suitability term in its projection, but the suitability model can still be run on its barrier, the
// day-of bias, field size and jockey/trainer tendencies (the history inputs stay blank). projection/run.py logs that value as `sadj`, overlay.py passes it as
// `sm_light`. Tested 9 Oct 2026 on 6,215 light runners: the value tracks the light model's miss (slope 0.69), so it is shown, but it is lower confidence.
export function hasLightSpeedMap(u: Runner): boolean {
  const b = u.adjustmentBreakdown
  return b?.suitability == null && b?.sm_light != null
}

export function speedMapDemeanedByRunId(runners: Runner[]): Map<string, number | null> {
  // The race mean is taken over main-model runners only, as before light runners were shown, so every main runner's figure is unchanged.
  const raw = runners.map((u) => u.adjustmentBreakdown?.suitability).filter((v): v is number => v != null)
  const mean = raw.length ? raw.reduce((a, b) => a + b, 0) / raw.length : 0
  const result = new Map<string, number | null>()
  for (const u of runners) {
    const v = u.adjustmentBreakdown?.suitability
    const light = raw.length ? u.adjustmentBreakdown?.sm_light : null   // no main runner to measure against: no light value either
    result.set(u.runId, v != null ? v - mean : light != null ? light - mean : null)
  }
  return result
}

// Demeaned suitability value at which a Speed Map tile tint and the SM column colour switch from neutral to favoured/hurt.
// 0.5 tints about 24% of runners (the term's demeaned sd is about 0.5).
export const SPEED_MAP_TINT_THRESHOLD = 0.5

// The wpr_price cap in wpr_projection.py's project_race() - a no-hope
// runner's raw softmax price can blow out to 5-6 figures; capped at 999
// since beyond that the exact number is meaningless.
export const PRICE_CAP = 999

// Backend's own fallback when config.json doesn't carry a beta (see
// wpr_projection.py's get_price_beta) - practically never hit once
// PRICE_BETA is always populated, kept only for defensiveness.
const DEFAULT_BETA = 0.4

// Replicates wpr_projection.py's project_race() price/rank softmax
// EXACTLY (same formula, same beta), but over EFFECTIVE ratings: the
// model's own projectedWpr, or a manually entered base for a runner the
// model couldn't project, each with any manual delta added on top. This is
// what lets a manual override on one runner correctly shift every OTHER
// runner's price too - it's a field-relative softmax, not a per-runner
// calculation.
export function computeEffectiveRace(
  runners: Runner[],
  deltas: Record<string, number>,
  bases: Record<string, number>,
  priceBeta: number | null,
  scratched: Set<string> = new Set(),
  // Bet signals for this race (runId -> model win probability m). When every runner still in the race has one, the rating comes from them.
  signals?: Record<string, { m: number; p: number } | null>,
): Record<string, EffectiveRunner> {
  let beta = priceBeta ?? DEFAULT_BETA

  const withEffectiveWpr = runners.map((r) => {
    const modelBase = r.projectedWpr ?? (r.runId in bases ? bases[r.runId] : null)
    const delta = deltas[r.runId] ?? 0
    const hasOverride = deltas[r.runId] != null || (r.projectedWpr == null && r.runId in bases)
    const isScratched = scratched.has(r.runId)
    const atwOff = r.atwOffset != null && Math.abs(r.atwOffset) >= 0.05 ? r.atwOffset : 0
    return {
      runId: r.runId,
      atwOff,
      // A scratched runner has no wpr for softmax purposes - excluded from
      // the field entirely (not just zeroed out), so the rest of the field
      // renormalizes as if it were never entered.
      wpr: !isScratched && modelBase != null ? modelBase + delta + atwOff : null,
      hasOverride,
      scratched: isScratched,
    }
  })

  // Bet-signal rating: level (the field's mean WPR-projection rating, before manual deltas) + RATING_PER_LN x (ln p - mean ln p), over the runners in
  // both. Only when every runner still in the race has a signal; otherwise the whole race stays on the projection (never a mix of two scales).
  const projectionByRunId = new Map<string, number | null>()
  for (const r of withEffectiveWpr) projectionByRunId.set(r.runId, r.wpr)
  let betSource = false
  if (signals) {
    const active = withEffectiveWpr.filter((r) => !r.scratched)
    const sig = (id: string) => {
      const m = signals[id]?.m
      return m != null && m > 0 ? Math.log(m) : null
    }
    const full = active.length >= 5 && active.every((r) => sig(r.runId) != null)
    const anchor = active.filter((r) => r.wpr != null)
    if (full && anchor.length >= 2) {
      const delta = (id: string) => deltas[id] ?? 0
      const level = anchor.reduce((a, r) => a + (r.wpr as number) - delta(r.runId), 0) / anchor.length
      const meanLn = anchor.reduce((a, r) => a + (sig(r.runId) as number), 0) / anchor.length
      for (const r of withEffectiveWpr) {
        if (r.scratched) continue
        r.wpr = level + RATING_PER_LN * ((sig(r.runId) as number) - meanLn) + delta(r.runId)
      }
      betSource = true
      beta = 1 / RATING_PER_LN   // so the price softmax below reproduces the model's own win probabilities
    }
  }

  const rated = withEffectiveWpr.filter((r) => r.wpr != null) as { runId: string; wpr: number; hasOverride: boolean; scratched: boolean; atwOff: number }[]

  const priceByRunId = new Map<string, number>()
  const rankByRunId = new Map<string, number>()
  const gapByRunId = new Map<string, number>()
  if (rated.length >= 2) {
    const maxWpr = Math.max(...rated.map((r) => r.wpr))
    const exps = rated.map((r) => ({ runId: r.runId, e: Math.exp(beta * (r.wpr - maxWpr)) }))
    const sumE = exps.reduce((s, x) => s + x.e, 0)
    for (const x of exps) {
      priceByRunId.set(x.runId, Math.min(1 / (x.e / sumE), PRICE_CAP))
    }
    for (const r of rated) {
      gapByRunId.set(r.runId, maxWpr - r.wpr)
    }
    ;[...rated]
      .sort((a, b) => b.wpr - a.wpr)
      .forEach((r, i) => rankByRunId.set(r.runId, i + 1))
  }

  // Same non-scratched population SpeedMapGrid.tsx's own caller filters to
  // (RaceDetail.tsx passes it race.runners.filter(!effectiveScratched)) -
  // matches this function's own `scratched` param exactly, so the race
  // mean this demeans against is identical either way.
  const speedMapByRunId = speedMapDemeanedByRunId(runners.filter((r) => !scratched.has(r.runId)))
  const lightIds = new Set(runners.filter(hasLightSpeedMap).map((r) => r.runId))

  const result: Record<string, EffectiveRunner> = {}
  for (const r of withEffectiveWpr) {
    const effectivePrice = r.wpr != null ? (priceByRunId.get(r.runId) ?? null) : null
    const gapFromTop = r.wpr != null ? (gapByRunId.get(r.runId) ?? null) : null
    result[r.runId] = {
      effectiveProjectedWpr: r.wpr,
      projectionWpr: projectionByRunId.get(r.runId) ?? null,
      ratingSource: betSource ? 'bet' : 'projection',
      atwOff: r.atwOff,
      effectivePrice,
      effectiveRank: r.wpr != null ? (rankByRunId.get(r.runId) ?? null) : null,
      hasOverride: r.hasOverride,
      scratched: r.scratched,
      gapFromTop,
      speedMapAdj: r.scratched ? null : (speedMapByRunId.get(r.runId) ?? null),
      speedMapLight: !r.scratched && lightIds.has(r.runId),
    }
  }
  return result
}

// Three gap lines on the Proj scale at today's weight (ATW), set by the user. The outer line moved from 6 to 8 on 9 Oct 2026 after a 15-month
// out-of-sample check (14,438 races, main model trained before 2025): inside 2 holds 2.2 runners a race and 50% of winners, inside 4 holds 3.9 and 70%,
// inside 6 held 5.6 and 84%, inside 8 holds 6.9 and 93%. The core line (2) is table and ladder only; the quaddie view, Compare shortcuts and counts use
// the inner (4) and outer (8) lines. Nothing here is a betting claim: 4 to 6 and 6 to 8 lose money without a favourable speed map.
export const CORE_GAP_FROM_TOP = 2
export const OUTER_GAP_FROM_TOP = 8
export const INNER_GAP_FROM_TOP = 4
// A runner between the inner and outer lines (4 to 8) joins the "map" quaddie pool when its SM Adj is at least MAP_POOL_MIN_SM (main-model runners only).
// 15-month out-of-sample test (14,438 races): inside 4 plus SM +0.5 holds 74.3% of winners with 4.25 runners a leg (inside 4 alone 70.0% with 3.88), so
// a four-leg quaddie lands about 31% against 24% for about 43% more combinations, at nearly the same winners per runner (17.5% vs 18.0%). SM +1.0 or better
// (MAP_VALUE_MIN_SM) adds only 0.06 runners but is the group that returned +20.9% flat on the win between 4 and 8 (777 bets, +10.0% without the 3 biggest
// winners); the 0.5 to 1.0 runners return about -3%. So +0.5 is the coverage rule and +1.0 is the value marker (thicker ring on the ladder).
export const MAP_POOL_MIN_SM = 0.5
export const MAP_VALUE_MIN_SM = 1.0

// Per-runner gap from the race's top effective Proj, scratched runners (client toggle or data) excluded.
// Needs 2+ rated runners, otherwise every gap is null.
export function computeGapsFromTop(
  runners: Runner[],
  effectiveByRunId: Record<string, EffectiveRunner>,
  scratched: Set<string>,
): Record<string, number | null> {
  const gaps: Record<string, number | null> = {}
  for (const r of runners) gaps[r.runId] = null
  const scored = runners
    .filter((r) => !scratched.has(r.runId))
    .map((r) => ({ runId: r.runId, score: effectiveByRunId[r.runId]?.effectiveProjectedWpr ?? null }))
    .filter((r): r is { runId: string; score: number } => r.score != null)
  if (scored.length < 2) return gaps
  const top = Math.max(...scored.map((r) => r.score))
  for (const r of scored) gaps[r.runId] = top - r.score
  return gaps
}
