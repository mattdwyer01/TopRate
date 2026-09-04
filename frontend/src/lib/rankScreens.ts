import type { Race, Runner } from '../types/domain'
import { BUSH_TRACK_THRESHOLD } from './meetings'

// Rank-conjunction screens: three toggleable volume tiers of ONE validated
// rule found via offline backtesting (Sep 2026, see wpr_rank_conjunction_
// screen_v1.py through v8.py in the repo root) - within-race form (ewm5)
// rank AND jockey_win_pct_90d>=15% AND trainer_win_pct_365d>=15%, varying
// only the form-rank cutoff (top-1/2/3) to trade selectivity for volume.
//
// The ablation study (v7) found WPR rank and sect_i_time rank both DILUTE
// this combo rather than help it once form+jockey+trainer are combined -
// deliberately excluded here, not an oversight. form_string (v3) and
// pfm_score (v4) were also tested and found negative. ewm5 itself isn't in
// the payload, so it's derived algebraically from two fields that are:
// baseWpr = 0.30*wprNett + 0.70*ewm5 (see wpr_projection.py's base calc),
// so ewm5 = (baseWpr - 0.30*wprNett) / 0.70.
//
// Same speculative-signal caveat as lib/signalWatch.ts: this is the
// candidate that survived a wide search across chronological H1/H2 halves,
// re-checked (weaker, but still positive both directions) on the real last
// 30 days and the last 4 actual Saturdays. Not statistically bulletproof,
// kept deliberately separate from the load-bearing accuracy pipeline.
export const RANK_SCREEN_JOCKEY_CUT = 15
export const RANK_SCREEN_TRAINER_CUT = 15

export type RankScreenTierId = 'targeted' | 'mid' | 'high'

export interface RankScreenTier {
  id: RankScreenTierId
  label: string
  formRankMax: number
  description: string
}

export const RANK_SCREEN_TIERS: RankScreenTier[] = [
  {
    id: 'targeted',
    label: 'Targeted',
    formRankMax: 1,
    description: 'Form (ewm5) ranked #1 in its race, AND jockey/trainer both >=15% - fewest bets, best backtested ROI.',
  },
  {
    id: 'mid',
    label: 'Mid volume',
    formRankMax: 2,
    description: 'Form (ewm5) ranked top-2 in its race, AND jockey/trainer both >=15% - a middle ground on volume vs selectivity.',
  },
  {
    id: 'high',
    label: 'High volume',
    formRankMax: 3,
    description: 'Form (ewm5) ranked top-3 in its race, AND jockey/trainer both >=15% - most bets, lower average edge per bet.',
  },
]

/** ewm5 (recency-weighted recent form) isn't in the payload directly, but
 * baseWpr = 0.30*wprNett + 0.70*ewm5 always holds (see wpr_projection.py) -
 * so it's recoverable exactly from two fields that are already exposed. */
export function deriveEwm5(r: Runner): number | null {
  if (r.baseWpr == null || r.wprNett == null) return null
  return (r.baseWpr - 0.3 * r.wprNett) / 0.7
}

export interface RankScreenRow {
  raceId: string
  runId: string
  date: string
  venue: string
  horse: string
  formRank: number
  price: number
  jockeyWinPct90d: number | null
  trainerWinPct365d: number | null
  won: boolean
  placed: boolean
}

export interface RankScreenFilters {
  period: 'all' | '90' | '30'
  excludeBush: boolean
}

/** Same period/bush-track filtering convention as signalWatch.ts/
 * accuracyStats.ts, applied independently so this feature can't regress
 * either of those pipelines. */
export function collectRankScreenRows(races: Race[], tierId: RankScreenTierId, filters: RankScreenFilters): RankScreenRow[] {
  const tier = RANK_SCREEN_TIERS.find((t) => t.id === tierId) ?? RANK_SCREEN_TIERS[0]
  const cutoff = filters.period === 'all' ? null : Date.now() - Number(filters.period) * 86_400_000
  const rows: RankScreenRow[] = []
  for (const race of races) {
    if (cutoff != null && new Date(race.date).getTime() < cutoff) continue
    if (filters.excludeBush && (race.prizeMoney ?? 0) <= BUSH_TRACK_THRESHOLD) continue

    // Rank ewm5 within the full non-scratched field first (matters for
    // which runners count as "top-N"), then filter down to resulted rows.
    const ranked = race.runners
      .filter((r) => !r.dataScratched)
      .map((r) => ({ r, ewm5: deriveEwm5(r) }))
      .filter((x): x is { r: Runner; ewm5: number } => x.ewm5 != null)
      .sort((a, b) => b.ewm5 - a.ewm5)

    let rank = 0
    for (const { r } of ranked) {
      // Standard "first" ranking (ties broken by sort/encounter order) -
      // matches pandas' rank(method="first") used in the offline backtest
      // scripts: rank increments by 1 every row, ties included.
      rank += 1

      if (rank > tier.formRankMax) continue
      if (r.finishPosition == null) continue // only resulted runs
      const price = r.fixedWinPrice ?? r.startingPrice
      if (price == null || price <= 1) continue
      const jockeyOk = (r.jockeyWinPct90d ?? -Infinity) >= RANK_SCREEN_JOCKEY_CUT
      const trainerOk = (r.trainerWinPct365d ?? -Infinity) >= RANK_SCREEN_TRAINER_CUT
      if (!jockeyOk || !trainerOk) continue

      rows.push({
        raceId: race.raceId,
        runId: r.runId,
        date: race.date,
        venue: race.venue,
        horse: r.horse,
        formRank: rank,
        price,
        jockeyWinPct90d: r.jockeyWinPct90d,
        trainerWinPct365d: r.trainerWinPct365d,
        won: r.won,
        placed: r.finishPosition >= 1 && r.finishPosition <= 3,
      })
    }
  }
  return rows
}

export interface RankScreenStats {
  n: number
  strikePct: number | null
  placeStrikePct: number | null
  roiPct: number | null
  avgPrice: number | null
}

/** Same proportional-return convention as signalWatch.ts's computeSignalWatchStats. */
export function computeRankScreenStats(rows: RankScreenRow[]): RankScreenStats {
  if (rows.length === 0) return { n: 0, strikePct: null, placeStrikePct: null, roiPct: null, avgPrice: null }
  let wins = 0
  let places = 0
  let profit = 0
  let priceSum = 0
  for (const r of rows) {
    priceSum += r.price
    if (r.won) {
      wins += 1
      profit += r.price - 1
    } else {
      profit -= 1
    }
    if (r.placed) places += 1
  }
  return {
    n: rows.length,
    strikePct: (wins / rows.length) * 100,
    placeStrikePct: (places / rows.length) * 100,
    roiPct: (profit / rows.length) * 100,
    avgPrice: priceSum / rows.length,
  }
}
