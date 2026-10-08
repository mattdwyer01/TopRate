import type { Runner } from '../types/domain'

export interface EffectiveRunner {
  // The projection at the weight carried today (ATW): model rating + manual delta + this horse's own offset. Ranking, gaps and fair prices use it.
  effectiveProjectedWpr: number | null
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
): Record<string, EffectiveRunner> {
  const beta = priceBeta ?? DEFAULT_BETA

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

// Three gap lines on the Proj scale at today's weight (ATW), 7 Oct 2026, set by the user and checked on 4,566 pre-race-logged races (1 Jul to 5 Oct 2026):
// inside 2 holds 2.3 runners a race and 49% of winners, inside 4 holds 4.0 and 69%, inside 6 holds 5.7 and 84%. The core line (2) is table and ladder only;
// the quaddie view, Compare shortcuts and counts keep using the inner (4) and outer (6) lines.
export const CORE_GAP_FROM_TOP = 2
export const OUTER_GAP_FROM_TOP = 6
export const INNER_GAP_FROM_TOP = 4

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
