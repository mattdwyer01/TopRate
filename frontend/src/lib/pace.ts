import type { Race, Runner } from '../types/domain'

export type TempoBucket = 'Fast' | 'Even' | 'Slow'

export interface PaceEstimate {
  display: string
  tempoBucket: TempoBucket
  fromShape: boolean
}

// Three-way source priority:
//  1. raceShapeEarly - the real, post-race measurement. Always preferred
//     once the race has actually run.
//  2. paceEstimateScore/Label - race_speed_estimate.py's TRAINED model
//     (early-speed sectionals, settle position, barrier, margin at 800m,
//     aggregated per race), held-out correlation with actual
//     raceShapeEarly ~+0.24. Real signal, modest reliability - labelled
//     "predicted", never presented as a measurement.
//  3. A crude on-the-fly leader-count heuristic (how many runners' own
//     average settle position looks front-running), only reached when
//     the trained model's estimate genuinely isn't available for this
//     race (e.g. a data gap) - last resort, not the primary estimate.
export function estimatePace(race: Race, runners: Runner[]): PaceEstimate {
  if (race.raceShapeEarly != null) {
    let display: string
    let tempoBucket: TempoBucket
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

  if (race.paceEstimateLabel) {
    // Model labels are Hot/Fast/Even/Slow (4-way); Hot folds into the
    // Fast bucket for matching purposes (same as a real Fast-early shape
    // would), but keeps its own word in the display text.
    const tempoBucket: TempoBucket =
      race.paceEstimateLabel === 'Slow' ? 'Slow' : race.paceEstimateLabel === 'Even' ? 'Even' : 'Fast'
    return { display: `${race.paceEstimateLabel} (predicted)`, tempoBucket, fromShape: false }
  }

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
