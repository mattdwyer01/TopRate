import type { Runner } from '../types/domain'

// How old the projection on screen is. `projectionMade` is when the logged projection was made (payload wpjmd). A fast projection run follows results, declarations
// and model changes, so a projection many hours old on a race still to run means a refresh was missed. Shown as a chip on the race banner, amber when stale.
const STALE_AFTER_MIN = 180
const STALE_WINDOW_MIN = 12 * 60 // only warn for races starting within this long; later days are re-scored by the daily run anyway

export interface ProjectionAge {
  made: string
  ageMin: number
  stale: boolean
}

export function projectionAge(runners: Runner[], startTime: string | null | undefined, now: number, raceRun: boolean): ProjectionAge | null {
  let newest = 0
  let made = ''
  for (const r of runners) {
    if (!r.projectionMade) continue
    const t = Date.parse(r.projectionMade)
    if (!Number.isNaN(t) && t > newest) {
      newest = t
      made = r.projectionMade
    }
  }
  if (!newest) return null
  const ageMin = Math.max(0, Math.round((now - newest) / 60000))
  const start = startTime ? Date.parse(startTime) : NaN
  const toJumpMin = Number.isNaN(start) ? Infinity : (start - now) / 60000
  const stale = !raceRun && ageMin > STALE_AFTER_MIN && toJumpMin > 0 && toJumpMin < STALE_WINDOW_MIN
  return { made, ageMin, stale }
}

export function formatAge(min: number): string {
  if (min < 60) return `${min}m`
  const h = Math.floor(min / 60)
  return h < 24 ? `${h}h ${min % 60}m` : `${Math.floor(h / 24)}d`
}
