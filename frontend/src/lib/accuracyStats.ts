import type { Race } from '../types/domain'
import { BUSH_TRACK_THRESHOLD } from './meetings'

// Predicted-vs-actual accuracy, ported from toprate_html_v3.py's WPR
// Accuracy tab (renderAccuracyTab / accCollectRows / accStats /
// accOutcomeStats) - the core "how good are the projections, really"
// question, using only what the new frontend already has in DashboardData.
// Deferred vs the old tab: bet-only/reviewed-only filters (no bet log or
// race-review feature exists yet in this rebuild - Phase 2), the
// track-level breakdown (many small groups, less essential for a v1), and
// multi-select going/distance filters (the period + bush-exclude toggle
// cover the main use case here).

export interface AccuracyRow {
  raceId: string
  date: string
  venue: string
  distance: number
  going: string
  horse: string
  predicted: number
  actual: number
  miss: number // actual - predicted; negative = overprojected
  predictedRank: number | null
  actualRank: number | null
  finishPosition: number | null
  won: boolean
}

export type Period = 'all' | '90' | '30'

export interface AccuracyFilters {
  period: Period
  excludeBush: boolean
}

export function distanceBand(distance: number): string {
  if (distance < 1200) return 'Sprint (<1200m)'
  if (distance < 1600) return 'Mile (1200-1599m)'
  if (distance < 2000) return 'Middle (1600-1999m)'
  return 'Staying (2000m+)'
}

export function collectAccuracyRows(races: Race[], filters: AccuracyFilters): AccuracyRow[] {
  const cutoff = filters.period === 'all' ? null : Date.now() - Number(filters.period) * 86_400_000
  const rows: AccuracyRow[] = []
  for (const race of races) {
    if (cutoff != null && new Date(race.date).getTime() < cutoff) continue
    if (filters.excludeBush && (race.prizeMoney ?? 0) <= BUSH_TRACK_THRESHOLD) continue
    for (const r of race.runners) {
      if (r.projectedWpr == null || r.actualWpr == null) continue
      rows.push({
        raceId: race.raceId,
        date: race.date,
        venue: race.venue,
        distance: race.distance,
        going: race.going,
        horse: r.horse,
        predicted: r.projectedWpr,
        actual: r.actualWpr,
        miss: r.actualWpr - r.projectedWpr,
        predictedRank: r.wprRank,
        actualRank: r.actualWprRank,
        finishPosition: r.finishPosition,
        won: r.won,
      })
    }
  }
  return rows
}

export interface AccuracyStats {
  n: number
  mae: number | null
  bias: number | null
  within3Pct: number | null
  within6Pct: number | null // cumulative: |miss| < 6
}

export function computeAccuracyStats(rows: AccuracyRow[]): AccuracyStats {
  if (rows.length === 0) return { n: 0, mae: null, bias: null, within3Pct: null, within6Pct: null }
  let absSum = 0
  let signedSum = 0
  let within3 = 0
  let within6 = 0
  for (const r of rows) {
    const a = Math.abs(r.miss)
    absSum += a
    signedSum += r.miss
    if (a < 3) within3++
    if (a < 6) within6++
  }
  return {
    n: rows.length,
    mae: absSum / rows.length,
    bias: signedSum / rows.length,
    within3Pct: (within3 / rows.length) * 100,
    within6Pct: (within6 / rows.length) * 100,
  }
}

export interface OutcomeStats {
  topPickN: number
  topPickWinPct: number | null
  topPickPlacePct: number | null
  fieldAvgWinPct: number | null
  winnerN: number
  winnerMedianRank: number | null
  winnerTop3Pct: number | null
}

function quantile(sorted: number[], q: number): number | null {
  if (sorted.length === 0) return null
  const pos = (sorted.length - 1) * q
  const lo = Math.floor(pos)
  const hi = Math.ceil(pos)
  if (lo === hi) return sorted[lo]
  return sorted[lo] + (sorted[hi] - sorted[lo]) * (pos - lo)
}

export function computeOutcomeStats(rows: AccuracyRow[]): OutcomeStats {
  let topPickN = 0
  let topPickWins = 0
  let topPickPlaces = 0
  let allResulted = 0
  let allWinners = 0
  const winnerRanks: number[] = []
  let winnersTop3 = 0
  let winnersWithRank = 0

  for (const r of rows) {
    if (r.finishPosition == null) continue
    allResulted++
    if (r.finishPosition === 1) allWinners++

    if (r.predictedRank === 1) {
      topPickN++
      if (r.finishPosition === 1) topPickWins++
      if (r.finishPosition <= 3) topPickPlaces++
    }
    if (r.finishPosition === 1 && r.predictedRank != null) {
      winnerRanks.push(r.predictedRank)
      winnersWithRank++
      if (r.predictedRank <= 3) winnersTop3++
    }
  }
  winnerRanks.sort((a, b) => a - b)

  return {
    topPickN,
    topPickWinPct: topPickN ? (topPickWins / topPickN) * 100 : null,
    topPickPlacePct: topPickN ? (topPickPlaces / topPickN) * 100 : null,
    fieldAvgWinPct: allResulted ? (allWinners / allResulted) * 100 : null,
    winnerN: winnerRanks.length,
    winnerMedianRank: quantile(winnerRanks, 0.5),
    winnerTop3Pct: winnersWithRank ? (winnersTop3 / winnersWithRank) * 100 : null,
  }
}

export interface BreakdownRow {
  group: string
  n: number
  mae: number
  bias: number
}

const MIN_BREAKDOWN_N = 10

/** Groups rows by keyFn, returns groups with n >= MIN_BREAKDOWN_N sorted
 * worst-MAE-first (surfaces where the model struggles most). */
export function computeBreakdown(rows: AccuracyRow[], keyFn: (r: AccuracyRow) => string): BreakdownRow[] {
  const groups = new Map<string, AccuracyRow[]>()
  for (const r of rows) {
    const k = keyFn(r)
    if (!k) continue
    const existing = groups.get(k)
    if (existing) existing.push(r)
    else groups.set(k, [r])
  }
  const out: BreakdownRow[] = []
  for (const [group, groupRows] of groups) {
    const s = computeAccuracyStats(groupRows)
    if (s.n < MIN_BREAKDOWN_N || s.mae == null || s.bias == null) continue
    out.push({ group, n: s.n, mae: s.mae, bias: s.bias })
  }
  out.sort((a, b) => b.mae - a.mae)
  return out
}

export interface CalibrationCell {
  predLo: number
  actualLo: number
  count: number
}

export interface CalibrationBins {
  binSize: number
  min: number
  max: number
  cells: CalibrationCell[]
  maxCount: number
}

/** Bins predicted x actual into a 2D grid for a density-shaded scatter -
 * with thousands of runners, one dot per row would just be an overplotted
 * smear. Both axes share one domain (predicted and actual are the same WPR
 * scale) so the y=x "perfect projection" reference line is meaningful. */
export function computeCalibrationBins(rows: AccuracyRow[], binSize = 5): CalibrationBins {
  if (rows.length === 0) return { binSize, min: 0, max: 100, cells: [], maxCount: 0 }
  let min = Infinity
  let max = -Infinity
  for (const r of rows) {
    min = Math.min(min, r.predicted, r.actual)
    max = Math.max(max, r.predicted, r.actual)
  }
  min = Math.floor(min / binSize) * binSize
  max = Math.ceil(max / binSize) * binSize

  const counts = new Map<string, number>()
  for (const r of rows) {
    const predBin = Math.floor((r.predicted - min) / binSize) * binSize + min
    const actualBin = Math.floor((r.actual - min) / binSize) * binSize + min
    const key = `${predBin}|${actualBin}`
    counts.set(key, (counts.get(key) ?? 0) + 1)
  }
  const cells: CalibrationCell[] = []
  let maxCount = 0
  for (const [key, count] of counts) {
    const [predLo, actualLo] = key.split('|').map(Number)
    cells.push({ predLo, actualLo, count })
    if (count > maxCount) maxCount = count
  }
  return { binSize, min, max, cells, maxCount }
}
