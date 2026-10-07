import type { Runner } from '../types/domain'

// The projection on the scale of the feed's actual rating (ATW, rated at the weight carried in that race). The model predicts the plain rating, so
// a miss measured against the actual needs the horse's own offset for that race. The pipeline freezes it with the projection (projection log
// column atwo); a run with none (older races) is left on the plain rating, as before.
// Also used wherever a raw projectedWpr is shown or compared outside computeEffectiveRace (standouts, speed map labels).
export function projectedAtActualScale(r: Pick<Runner, 'projectedWpr' | 'atwOffset'>): number | null {
  if (r.projectedWpr == null) return null
  return r.projectedWpr + (r.atwOffset ?? 0)
}
