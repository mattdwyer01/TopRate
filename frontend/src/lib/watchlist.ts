import type { Race, Runner } from '../types/domain'

// The pattern from the Aug 2026 "back the top-rated runner" backtesting
// session that held up under a chronological split-half check (both halves
// independently positive, not just the aggregate). Flags the field's #1
// WPR-ranked runner when:
//   - it leads the #2-ranked runner by at least minGap WPR points
//   - the market still has it out at at least minPrice fixed
//   - the race has no first starter anywhere in the field (unraced debutants
//     add noise a form-based model can't see coming, even when the debutant
//     itself isn't the horse being backed - excluding them held up at every
//     gap/price combination tested, not just one)
// Thresholds are user-editable (Settings) rather than hardcoded - the
// backtest behind this is still a few months of one account's data, so the
// "right" cutoff is a judgment call, not a fixed constant. Still NOT a
// proven edge - this exists to accumulate live, out-of-sample evidence
// before any staking decision, not to recommend bets.
export interface WatchlistEntry {
  race: Race
  runner: Runner
  gap: number
}

export function computeWatchlist(races: Race[], minGap: number, minPrice: number): WatchlistEntry[] {
  const entries: WatchlistEntry[] = []
  for (const race of races) {
    if (race.hasFirstStarter) continue
    const rank1 = race.runners.find((r) => r.wprRank === 1)
    const rank2 = race.runners.find((r) => r.wprRank === 2)
    if (!rank1 || !rank2 || rank1.projectedWpr == null || rank2.projectedWpr == null) continue
    const gap = rank1.projectedWpr - rank2.projectedWpr
    if (gap < minGap) continue
    if (rank1.fixedWinPrice == null || rank1.fixedWinPrice < minPrice) continue
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
