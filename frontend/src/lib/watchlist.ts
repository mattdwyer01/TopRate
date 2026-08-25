import type { Race, Runner } from '../types/domain'

// The one pattern from the Aug 2026 "back the top-rated runner" backtesting
// session that actually held up under a chronological split-half check (both
// halves independently positive, not just the aggregate) - see the session's
// analysis for the full numbers. Flags the field's #1 WPR-ranked runner when:
//   - it leads the #2-ranked runner by a wide margin (a genuinely confident
//     pick, not a close call between the top two)
//   - the market still has it out at a long-ish price (the model's
//     confidence hasn't been priced in yet)
//   - the race is provincial/midweek-city grade, not a feature race (where
//     the market is sharpest) or a bush track (too thin a sample to trust)
// This is NOT a proven edge - it's a promising, still-thin-sample (n=74
// historically) pattern being paper-tracked here before any real staking
// decision. Thresholds are deliberately hardcoded, not user-configurable -
// they came from one specific backtest and changing them without re-testing
// would silently invalidate the whole premise.
export const WATCHLIST_MIN_GAP = 4
export const WATCHLIST_MIN_ODDS = 8
export const WATCHLIST_MIN_PRIZE = 15000
export const WATCHLIST_MAX_PRIZE = 60000

export interface WatchlistEntry {
  race: Race
  runner: Runner
  gap: number
}

export function computeWatchlist(races: Race[]): WatchlistEntry[] {
  const entries: WatchlistEntry[] = []
  for (const race of races) {
    if (
      race.prizeMoney == null ||
      race.prizeMoney <= WATCHLIST_MIN_PRIZE ||
      race.prizeMoney > WATCHLIST_MAX_PRIZE
    ) {
      continue
    }
    const rank1 = race.runners.find((r) => r.wprRank === 1)
    const rank2 = race.runners.find((r) => r.wprRank === 2)
    if (!rank1 || !rank2 || rank1.projectedWpr == null || rank2.projectedWpr == null) continue
    const gap = rank1.projectedWpr - rank2.projectedWpr
    if (gap < WATCHLIST_MIN_GAP) continue
    if (rank1.fixedWinPrice == null || rank1.fixedWinPrice < WATCHLIST_MIN_ODDS) continue
    entries.push({ race, runner: rank1, gap })
  }
  return entries
}

// A flagged runner with no finishPosition never actually raced with a known
// outcome (scratched, or the race hasn't run yet) - excluded from the track
// record's tally rather than counted as a loss.
export function hasKnownOutcome(entry: WatchlistEntry): boolean {
  return entry.runner.finishPosition != null
}

export interface WatchlistTally {
  n: number
  wins: number
  strikeRate: number
  flatRoi: number
  propRoi: number
}

export function tallyWatchlist(entries: WatchlistEntry[]): WatchlistTally {
  const settled = entries.filter(hasKnownOutcome)
  const n = settled.length
  if (n === 0) {
    return { n: 0, wins: 0, strikeRate: 0, flatRoi: 0, propRoi: 0 }
  }
  let wins = 0
  let flatProfit = 0
  let propStakeTotal = 0
  let propProfitTotal = 0
  for (const e of settled) {
    const price = e.runner.fixedWinPrice as number
    const won = e.runner.won
    if (won) wins += 1
    flatProfit += won ? price - 1 : -1
    const propStake = 1 / price
    propStakeTotal += propStake
    propProfitTotal += (won ? 1 : 0) - propStake
  }
  return {
    n,
    wins,
    strikeRate: wins / n,
    flatRoi: flatProfit / n,
    propRoi: propProfitTotal / propStakeTotal,
  }
}
