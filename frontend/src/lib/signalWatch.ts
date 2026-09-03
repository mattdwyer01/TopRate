import type { Race } from '../types/domain'
import { BUSH_TRACK_THRESHOLD } from './meetings'

// "Signal watch": tracks ONE specific candidate rule found via offline
// K-fold backtesting (Sep 2026, see wpr_roi_rule_mining.py and wpr_
// trainer_jockey_decile_check.py in the repo root) - it is NOT a proven
// edge, it is the single candidate that survived every robustness check
// run against it (holds across every edge threshold tried for jockey
// alone, all 4 held-out folds positive for the combined rule, n=1,168).
// Every other filter tried this session (price caps, market-rank
// agreement, prob floors, field size, barrier, distance, class move,
// days since, wpr/form rank agreement, ...) came back negative. This is
// a genuinely small-sample, NOT statistically significant (t=1.58,
// short of the usual 1.96 bar) result from a wide multiple-comparisons
// search - existing purely to be checked against real forward data
// before anyone considers it a real edge. Deliberately kept separate
// from accuracyStats.ts (the established, load-bearing accuracy
// pipeline) rather than folded in, so this speculative addition can
// never regress anything that pipeline already does.
export const SIGNAL_WATCH_RULE = {
  edgeThreshold: 0.05,
  priceCap: 26,
  jockeyWinPctCut: 16.9,
  trainerWinPctCut: 17.3,
} as const

export interface SignalWatchRow {
  raceId: string
  runId: string
  date: string
  venue: string
  horse: string
  price: number
  edge: number
  jockeyWinPct90d: number | null
  trainerWinPct365d: number | null
  won: boolean
}

export interface SignalWatchFilters {
  period: 'all' | '90' | '30'
  excludeBush: boolean
}

/** Same period/bush-track filtering convention as accuracyStats.ts's
 * collectAccuracyRows, applied independently here (not shared) so this
 * experimental feature can't regress that established pipeline. */
export function collectSignalWatchRows(races: Race[], filters: SignalWatchFilters): SignalWatchRow[] {
  const cutoff = filters.period === 'all' ? null : Date.now() - Number(filters.period) * 86_400_000
  const rows: SignalWatchRow[] = []
  for (const race of races) {
    if (cutoff != null && new Date(race.date).getTime() < cutoff) continue
    if (filters.excludeBush && (race.prizeMoney ?? 0) <= BUSH_TRACK_THRESHOLD) continue
    for (const r of race.runners) {
      const price = r.fixedWinPrice ?? r.startingPrice
      if (price == null || price <= 1) continue
      if (r.edge == null) continue
      if (r.finishPosition == null) continue // only resulted runs
      const meetsRule =
        r.edge >= SIGNAL_WATCH_RULE.edgeThreshold &&
        price <= SIGNAL_WATCH_RULE.priceCap &&
        ((r.jockeyWinPct90d ?? -Infinity) >= SIGNAL_WATCH_RULE.jockeyWinPctCut ||
          (r.trainerWinPct365d ?? -Infinity) >= SIGNAL_WATCH_RULE.trainerWinPctCut)
      if (!meetsRule) continue
      rows.push({
        raceId: race.raceId,
        runId: r.runId,
        date: race.date,
        venue: race.venue,
        horse: r.horse,
        price,
        edge: r.edge,
        jockeyWinPct90d: r.jockeyWinPct90d,
        trainerWinPct365d: r.trainerWinPct365d,
        won: r.won,
      })
    }
  }
  return rows
}

export interface SignalWatchStats {
  n: number
  strikePct: number | null
  roiPct: number | null
  avgPrice: number | null
}

/** Proportional-return-style ROI: profit on a $1 stake per bet, same
 * convention as wpr_bet_selection_post_retrain.py's report() (the
 * backtest this rule came from) - sp-1 on a win, -1 on a loss. */
export function computeSignalWatchStats(rows: SignalWatchRow[]): SignalWatchStats {
  if (rows.length === 0) return { n: 0, strikePct: null, roiPct: null, avgPrice: null }
  let wins = 0
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
  }
  return {
    n: rows.length,
    strikePct: (wins / rows.length) * 100,
    roiPct: (profit / rows.length) * 100,
    avgPrice: priceSum / rows.length,
  }
}
