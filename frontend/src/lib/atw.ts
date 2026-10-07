import type { Runner } from '../types/domain'
import { PRICE_CAP } from './raceModel'

// The projection on the scale of the feed's actual rating (ATW, rated at the weight carried in that race). The model predicts the plain rating, so
// a miss measured against the actual needs the horse's own offset for that race. The pipeline freezes it with the projection (projection log
// column atwo); a run with none (older races) is left on the plain rating, as before.
// Also used wherever a raw projectedWpr is shown or compared outside computeEffectiveRace (standouts, speed map labels).
export function projectedAtActualScale(r: Pick<Runner, 'projectedWpr' | 'atwOffset'>): number | null {
  if (r.projectedWpr == null) return null
  return r.projectedWpr + (r.atwOffset ?? 0)
}

// Rank and fair price for every rated, unscratched runner of a finished (or any) race on the ATW scale, the same softmax the race page uses
// (beta 0.20, the pipeline's own price sharpness). Used by Review and the day results so past races are read the way the race page ranks them.
export function atwFieldByRunId(runners: Runner[], beta = 0.2): Map<string, { rank: number; price: number }> {
  const rated = runners
    .filter((r) => !r.dataScratched && r.projectedWpr != null)
    .map((r) => ({ id: r.runId, v: projectedAtActualScale(r) as number }))
    .sort((a, b) => b.v - a.v)
  const out = new Map<string, { rank: number; price: number }>()
  if (rated.length < 2) return out
  const top = rated[0].v
  const sum = rated.reduce((s, x) => s + Math.exp(beta * (x.v - top)), 0)
  rated.forEach((x, i) => {
    const rank = i > 0 && rated[i - 1].v === x.v ? (out.get(rated[i - 1].id) as { rank: number }).rank : i + 1
    out.set(x.id, { rank, price: Math.min(sum / Math.exp(beta * (x.v - top)), PRICE_CAP) })
  })
  return out
}
