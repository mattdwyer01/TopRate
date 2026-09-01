import type { Race } from '../types/domain'
import { BUSH_TRACK_THRESHOLD } from './meetings'
import { isVoid } from './wprVoid'

// Predicted-vs-actual accuracy, ported from toprate_html_v3.py's WPR
// Accuracy tab (renderAccuracyTab / accCollectRows / accStats /
// accOutcomeStats) - the core "how good are the projections, really"
// question, using only what the new frontend already has in DashboardData.
// Deferred vs the old tab: bet-only/reviewed-only filters (no bet log or
// race-review feature exists yet in this rebuild - Phase 2) and multi-select
// going/distance filters (the period + bush-exclude toggle cover the main
// use case here). The track-level breakdown WAS deferred originally but is
// now built (see ReviewTab's "By venue" table) - MIN_BREAKDOWN_N keeps it
// from splintering into dozens of single-digit-n rows.
//
// Two genuinely different questions, both answered here, neither a
// substitute for the other: computeAccuracyStats measures each runner's
// OWN point miss (predicted WPR vs its own actual WPR) in isolation.
// computeRankStats measures whether the model ordered the FIELD correctly
// against actual finishing order - a horse predicted 95 that runs 95 (a
// ~zero point miss) but finishes 3rd was not itself a bad prediction; the
// race went to rivals the model under-rated. Point accuracy can't see
// that, only rank accuracy can - see computeRankStats' own comment.

export interface AccuracyRow {
  raceId: string
  runId: string
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
  // The model's own softmax-derived $ price for this runner, and the
  // market's own settled price (starting price, falling back to the
  // post-race top fluctuation when SP itself is missing) - both null
  // until price/result data is available. Used by computeStrikeRates'
  // "rated under $10" / "rated shorter than market" pools.
  wprPrice: number | null
  marketPrice: number | null
  // Was this run compromised (vet/checked/eased/fell/etc), per video and
  // steward comments? Only ever flags UNDERperformances (see lib/wprVoid.ts's
  // direction rule) - a trouble comment on a run that beat its projection
  // anyway isn't an excuse, so it stays counted. Not a fair test of the
  // model either way - see collectAccuracyRows' excludeVoid filter.
  voided: boolean
  voidReason: string
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
      const miss = r.actualWpr - r.projectedWpr
      const voidResult = isVoid(miss, r.commentsVideo, r.commentsSteward)
      rows.push({
        raceId: race.raceId,
        runId: r.runId,
        date: race.date,
        venue: race.venue,
        distance: race.distance,
        going: race.going,
        horse: r.horse,
        predicted: r.projectedWpr,
        actual: r.actualWpr,
        miss,
        predictedRank: r.wprRank,
        actualRank: r.actualWprRank,
        finishPosition: r.finishPosition,
        won: r.won,
        wprPrice: r.wprPrice,
        marketPrice: r.startingPrice ?? r.postRaceTopPrice,
        voided: voidResult.isVoid,
        voidReason: voidResult.reason,
      })
    }
  }
  return rows
}

/** Splits rows into {clean, voided} - clean is what the headline stats
 * should be computed from by default (matches train_wpr_projection()'s own
 * void filter on the training target: a compromised run isn't a fair test
 * of the model either way). voided is kept, not discarded, so the caller
 * can still show the count/list for transparency. */
export function splitVoided(rows: AccuracyRow[]): { clean: AccuracyRow[]; voided: AccuracyRow[] } {
  const clean: AccuracyRow[] = []
  const voided: AccuracyRow[] = []
  for (const r of rows) (r.voided ? voided : clean).push(r)
  return { clean, voided }
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

export interface StrikeRatePool {
  label: string
  n: number
  wins: number
  strikePct: number | null
}

// Four named runner pools the user tracks as the real bar for a model
// change (this session's own validation standard for closing_merit/
// gear_change/the alpha work): does the model's own most-confident
// picks - by rank, and separately by its own $ price against the
// market's - actually win at a good rate. "Rated shorter than market"
// is the model's value/edge signal: wprPrice < marketPrice means the
// model thinks this runner is a better chance than the market prices
// it, so its OWN win rate is the real test of whether that signal means
// anything.
export function computeStrikeRates(rows: AccuracyRow[]): StrikeRatePool[] {
  const pools: { label: string; test: (r: AccuracyRow) => boolean }[] = [
    { label: 'Top rated', test: (r) => r.predictedRank === 1 },
    { label: 'Top 4 rated', test: (r) => r.predictedRank != null && r.predictedRank <= 4 },
    { label: 'Rated under $10', test: (r) => r.wprPrice != null && r.wprPrice < 10 },
    {
      label: 'Rated shorter than market',
      test: (r) => r.wprPrice != null && r.marketPrice != null && r.wprPrice < r.marketPrice,
    },
  ]
  return pools.map(({ label, test }) => {
    let n = 0
    let wins = 0
    for (const r of rows) {
      if (r.finishPosition == null || !test(r)) continue
      n++
      if (r.won) wins++
    }
    return { label, n, wins, strikePct: n > 0 ? (wins / n) * 100 : null }
  })
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

const MIN_FIELD_FOR_RANK = 4

// Rank (1 = best), ties get the MIN rank (matches pandas' method='min',
// used by rank_vs_finish_analysis.py, which this mirrors). Ascending sort:
// caller passes -predicted (or finishPosition as-is) so "best" sorts first.
function rankAscending(values: number[]): number[] {
  const sorted = [...values].sort((a, b) => a - b)
  return values.map((v) => sorted.indexOf(v) + 1)
}

function pearson(xs: number[], ys: number[]): number | null {
  const n = xs.length
  if (n < 2) return null
  const mx = xs.reduce((a, b) => a + b, 0) / n
  const my = ys.reduce((a, b) => a + b, 0) / n
  let num = 0
  let dx2 = 0
  let dy2 = 0
  for (let i = 0; i < n; i++) {
    const dx = xs[i] - mx
    const dy = ys[i] - my
    num += dx * dy
    dx2 += dx * dx
    dy2 += dy * dy
  }
  if (dx2 === 0 || dy2 === 0) return null
  return num / Math.sqrt(dx2 * dy2)
}

export interface RankStats {
  races: number
  rankMae: number | null // mean |predicted rank - finish rank| within a race
  spearman: number | null // rank correlation, per race, averaged (-1..1)
}

/** How well the model orders runners WITHIN each race, as distinct from
 * how close any one runner's own WPR number lands (computeAccuracyStats).
 * A horse predicted 95 (rank 1) that runs 95 (near-zero point miss) but
 * finishes 3rd was NOT a bad prediction on its own - the race was lost to
 * rivals the model under-rated. Point MAE can't see that; only ranking the
 * field and comparing to actual finishing order can. Re-ranks the stored
 * predictedRank WITHIN each race (rather than trusting the raw field,
 * which was computed pre-race against the full field and may have gaps
 * once scratched/unresulted runners are excluded here) - mirrors
 * rank_vs_finish_analysis.py's own accCollectRows/g_ranked approach. */
export function computeRankStats(rows: AccuracyRow[]): RankStats {
  const byRace = new Map<string, AccuracyRow[]>()
  for (const r of rows) {
    if (r.predictedRank == null || r.finishPosition == null) continue
    const existing = byRace.get(r.raceId)
    if (existing) existing.push(r)
    else byRace.set(r.raceId, [r])
  }
  const maeByRace: number[] = []
  const corrByRace: number[] = []
  for (const raceRows of byRace.values()) {
    if (raceRows.length < MIN_FIELD_FOR_RANK) continue
    const predRank = rankAscending(raceRows.map((r) => r.predictedRank as number))
    const finishRank = rankAscending(raceRows.map((r) => r.finishPosition as number))
    const diffs = predRank.map((p, i) => Math.abs(p - finishRank[i]))
    maeByRace.push(diffs.reduce((a, b) => a + b, 0) / diffs.length)
    const r = pearson(predRank, finishRank)
    if (r != null) corrByRace.push(r)
  }
  return {
    races: maeByRace.length,
    rankMae: maeByRace.length ? maeByRace.reduce((a, b) => a + b, 0) / maeByRace.length : null,
    spearman: corrByRace.length ? corrByRace.reduce((a, b) => a + b, 0) / corrByRace.length : null,
  }
}

export interface WinnerRankStats {
  winnerN: number
  meanWinnerRankError: number | null // mean(predictedRank - 1) across actual winners
  rankWinCorrelation: number | null // point-biserial correlation of predicted rank vs won,
  // across every runner (not just winners), sign-flipped so positive = a
  // better (lower-numbered) predicted rank actually associates with winning
}

/** computeRankStats answers "did the model order this race correctly,
 * overall". This answers the narrower, arguably more decision-relevant
 * question: specifically how far off was the model's rank for the horse
 * that actually won (mean, not the median already shown elsewhere), and -
 * across every runner, winners and losers alike - does a better predicted
 * rank actually associate with winning at all. Point-biserial correlation
 * is just Pearson's formula applied to one continuous (rank) and one
 * binary (won) variable - no separate formula needed. */
export function computeWinnerRankStats(rows: AccuracyRow[]): WinnerRankStats {
  const winnerErrors: number[] = []
  const ranksForCorr: number[] = []
  const winsForCorr: number[] = []
  for (const r of rows) {
    if (r.predictedRank == null) continue
    if (r.won) winnerErrors.push(r.predictedRank - 1)
    ranksForCorr.push(-r.predictedRank)
    winsForCorr.push(r.won ? 1 : 0)
  }
  return {
    winnerN: winnerErrors.length,
    meanWinnerRankError: winnerErrors.length
      ? winnerErrors.reduce((a, b) => a + b, 0) / winnerErrors.length
      : null,
    rankWinCorrelation: pearson(ranksForCorr, winsForCorr),
  }
}

export interface MarginStats {
  n: number
  mae: number | null // mean |actual margin - predicted margin| to the top predicted pick
  bias: number | null // mean signed (actual margin - predicted margin)
}

/** Per request: not just "was each horse's own number close" or "did the
 * order come out right", but "was the GAP we predicted between a horse and
 * the top-rated horse the gap that actually showed up". For every runner,
 * predicted margin = (top predicted pick's predicted WPR) - (this horse's
 * predicted WPR) - always >=0, since the top pick IS the highest predicted.
 * Actual margin = (top predicted pick's ACTUAL WPR) - (this horse's actual
 * WPR) - can be any sign (the top pick can run below a horse it was
 * predicted to beat). A horse predicted 5 points behind the top pick whose
 * actual gap also lands near 5 is a well-predicted margin, even if neither
 * horse's own point miss was exactly zero - the SPACING held up, which is
 * what actually separates a good multi and a bad one. Compared against the
 * top pick's ACTUAL result specifically (not the top actual-WPR horse),
 * since the question is whether the model's implied gap to its own top
 * selection held up, not who really ran best that day. */
export function computeMarginStats(rows: AccuracyRow[]): MarginStats {
  const byRace = new Map<string, AccuracyRow[]>()
  for (const r of rows) {
    const existing = byRace.get(r.raceId)
    if (existing) existing.push(r)
    else byRace.set(r.raceId, [r])
  }
  const absMisses: number[] = []
  const signedMisses: number[] = []
  for (const raceRows of byRace.values()) {
    if (raceRows.length < 2) continue
    const top = raceRows.reduce((a, b) => (b.predicted > a.predicted ? b : a))
    for (const r of raceRows) {
      if (r === top) continue
      const predMargin = top.predicted - r.predicted
      const actualMargin = top.actual - r.actual
      const miss = actualMargin - predMargin
      absMisses.push(Math.abs(miss))
      signedMisses.push(miss)
    }
  }
  return {
    n: absMisses.length,
    mae: absMisses.length ? absMisses.reduce((a, b) => a + b, 0) / absMisses.length : null,
    bias: signedMisses.length ? signedMisses.reduce((a, b) => a + b, 0) / signedMisses.length : null,
  }
}

/** A short, factual plain-English readout of the numbers below it - built
 * because a page of a dozen stat tiles doesn't, by itself, tell you what
 * to conclude. Every clause states a real computed number; nothing here
 * is a judgment call the reader has to make on their own. */
export function buildHeadlineSummary(
  periodLabel: string,
  rankStats: RankStats,
  marginStats: MarginStats,
  voidedCount: number,
  totalCount: number
): string[] {
  const lines: string[] = []
  if (rankStats.spearman != null) {
    lines.push(
      `${periodLabel}, the model ordered the field with a ${rankStats.spearman.toFixed(2)} rank correlation ` +
        `(1.0 = perfect order, 0 = random).`
    )
  }
  if (marginStats.mae != null) {
    const skew =
      marginStats.bias != null && Math.abs(marginStats.bias) >= 1
        ? marginStats.bias > 0
          ? ' - gaps tended to run WIDER than predicted (the top pick underperformed relative to the field)'
          : ' - gaps tended to run NARROWER than predicted (the top pick outperformed the field)'
        : ''
    lines.push(
      `The predicted WPR gap between each horse and the top pick was off by ` +
        `${marginStats.mae.toFixed(1)} points on average${skew}.`
    )
  }
  if (voidedCount > 0 && totalCount > 0) {
    lines.push(
      `${voidedCount.toLocaleString()} of ${totalCount.toLocaleString()} runs ` +
        `(${((voidedCount / totalCount) * 100).toFixed(1)}%) were excluded below as compromised by an ` +
        `incident (vet, checked, eased, etc, per video/steward comments) - not a fair test of the model either way.`
    )
  }
  return lines
}
