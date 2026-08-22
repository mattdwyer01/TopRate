import type { Race, Runner } from '../types/domain'

export type TempoBucket = 'Fast' | 'Even' | 'Slow'

export interface PaceEstimate {
  display: string
  tempoBucket: TempoBucket
  fromShape: boolean
}

// Prefers the race-wide early-sectional shape (raceShapeEarly) when known -
// a real measurement. Falls back to a settle-position-derived estimate
// (how many runners are predicted to lead/sit on-pace) when the shape figure
// isn't available yet (e.g. sectional data hasn't settled for this race).
export function estimatePace(race: Race, runners: Runner[]): PaceEstimate {
  let leaders = 0
  let onPace = 0
  let midOrBack = 0
  for (const u of runners) {
    const pos = u.avgSettledPos
    if (pos == null) continue
    if (pos <= 2) leaders++
    else if (pos <= 4) onPace++
    else midOrBack++
  }
  let tempoBucket: TempoBucket = 'Even'
  let label = 'Even'
  if (leaders >= 3) {
    tempoBucket = 'Fast'
    label = 'Hot pace'
  } else if (leaders >= 2 && onPace >= 2) {
    tempoBucket = 'Fast'
    label = 'Fast'
  } else if (leaders <= 1 && midOrBack >= 4) {
    tempoBucket = 'Slow'
    label = 'Slow'
  }

  if (race.raceShapeEarly != null) {
    let display: string
    if (race.raceShapeEarly > 0.15) {
      tempoBucket = 'Fast'
      display = 'Fast early'
    } else if (race.raceShapeEarly < -0.15) {
      tempoBucket = 'Slow'
      display = 'Slow early'
    } else {
      tempoBucket = 'Even'
      display = 'Even pace'
    }
    return { display, tempoBucket, fromShape: true }
  }

  return { display: `${label} (est)`, tempoBucket, fromShape: false }
}

// Settling-position band today's projected settle falls into, matching the
// bands the backend uses for predictedSettlingBand / formHistory.relativeSettlePosition.
export function settleBand(relativePosition: number | null): string | null {
  if (relativePosition == null) return null
  if (relativePosition <= 0.2) return 'Leader'
  if (relativePosition <= 0.45) return 'On-pace'
  if (relativePosition <= 0.7) return 'Midfield'
  return 'Back'
}

export function goingBand(going: string | null | undefined): string | null {
  if (!going) return null
  const g = going.toLowerCase()
  if (g.startsWith('firm')) return 'Firm'
  if (g.startsWith('good')) return 'Good'
  if (g.startsWith('soft')) return 'Soft'
  if (g.startsWith('heavy')) return 'Heavy'
  return null
}
