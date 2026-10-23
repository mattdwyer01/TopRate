import type { Runner } from '../types/domain'
import type { EffectiveRunner } from './raceModel'
import { speedRatingOnScale } from './speed'

// Display spread (22 Oct 2026, owner's request): the WR (Proj) and SR (Spd) figures are tight inside a race (within-race sd about 4 and 3.4 points against about 8 for what the horses then run), so the table,
// the result panel and the runner page tiles show each figure stretched away from the race average, rank order unchanged. This is a presentation scale only: the underlying figures, the Rating column and its
// ranks, the gap lines, the ladder, the quaddie pools and Rated $ all use the unstretched values. At 1 the figures show as before.
export const DISPLAY_SPREAD: number = 1.5

export interface SpreadCentres {
  wr: number | null // race average of the WR (Proj) figure over the rated, non-scratched runners (first starters' estimates are left out)
  sr: number | null // race average of the SR figure on the same scale
}

export function spreadCentres(runners: Runner[], effective: Record<string, EffectiveRunner | undefined>, scratched: Set<string>): SpreadCentres {
  const wr: number[] = []
  const sr: number[] = []
  for (const r of runners) {
    if (scratched.has(r.runId) || effective[r.runId]?.scratched) continue
    const p = effective[r.runId]?.effectiveProjectedWpr ?? r.projectedWpr
    if (p != null && r.projectionModel !== 'debut') wr.push(p)
    if (r.speedRating != null) sr.push(speedRatingOnScale(r.speedRating))
  }
  const mean = (a: number[]) => (a.length ? a.reduce((x, y) => x + y, 0) / a.length : null)
  return { wr: mean(wr), sr: mean(sr) }
}

// centre + k x (value - centre); the value as it is when there is no centre (fewer than one rated runner) or k is 1
export function stretch(v: number | null | undefined, centre: number | null | undefined, k = DISPLAY_SPREAD): number | null {
  if (v == null) return null
  if (centre == null || k === 1) return v
  return centre + k * (v - centre)
}
