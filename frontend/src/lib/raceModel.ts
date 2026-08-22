import type { Runner } from '../types/domain'

export interface EffectiveRunner {
  effectiveProjectedWpr: number | null
  effectivePrice: number | null
  effectiveRank: number | null
  hasOverride: boolean
}

// The wpr_price cap in wpr_projection.py's project_race() - a no-hope
// runner's raw softmax price can blow out to 5-6 figures; capped at 999
// since beyond that the exact number is meaningless.
const PRICE_CAP = 999

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
): Record<string, EffectiveRunner> {
  const beta = priceBeta ?? DEFAULT_BETA

  const withEffectiveWpr = runners.map((r) => {
    const modelBase = r.projectedWpr ?? (r.runId in bases ? bases[r.runId] : null)
    const delta = deltas[r.runId] ?? 0
    const hasOverride = deltas[r.runId] != null || (r.projectedWpr == null && r.runId in bases)
    return {
      runId: r.runId,
      wpr: modelBase != null ? modelBase + delta : null,
      hasOverride,
    }
  })

  const rated = withEffectiveWpr.filter((r) => r.wpr != null) as { runId: string; wpr: number; hasOverride: boolean }[]

  const priceByRunId = new Map<string, number>()
  const rankByRunId = new Map<string, number>()
  if (rated.length >= 2) {
    const maxWpr = Math.max(...rated.map((r) => r.wpr))
    const exps = rated.map((r) => ({ runId: r.runId, e: Math.exp(beta * (r.wpr - maxWpr)) }))
    const sumE = exps.reduce((s, x) => s + x.e, 0)
    for (const x of exps) {
      priceByRunId.set(x.runId, Math.min(1 / (x.e / sumE), PRICE_CAP))
    }
    ;[...rated]
      .sort((a, b) => b.wpr - a.wpr)
      .forEach((r, i) => rankByRunId.set(r.runId, i + 1))
  }

  const result: Record<string, EffectiveRunner> = {}
  for (const r of withEffectiveWpr) {
    result[r.runId] = {
      effectiveProjectedWpr: r.wpr,
      effectivePrice: r.wpr != null ? (priceByRunId.get(r.runId) ?? null) : null,
      effectiveRank: r.wpr != null ? (rankByRunId.get(r.runId) ?? null) : null,
      hasOverride: r.hasOverride,
    }
  }
  return result
}
