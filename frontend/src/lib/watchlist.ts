import type { Race, Runner } from '../types/domain'
import { bushMeetingKeys, meetingKey } from './meetings'

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

// A runner's rating for Watchlist purposes: the model's own projection, or
// (when the model couldn't project the runner at all - typically a first
// starter) a manually-entered base rating from the runner detail panel, if
// one has been set. null means genuinely unrated - no model projection and
// no manual entry either.
function effectiveWpr(runner: Runner, bases: Record<string, number>): number | null {
  if (runner.projectedWpr != null) return runner.projectedWpr
  return runner.runId in bases ? bases[runner.runId] : null
}

export function computeWatchlist(
  races: Race[],
  minGap: number,
  minPrice: number,
  bases: Record<string, number> = {},
): WatchlistEntry[] {
  const entries: WatchlistEntry[] = []
  const bushKeys = bushMeetingKeys(races)
  for (const race of races) {
    // Same bush/picnic-meeting definition as the rest of the app (top race
    // at that meeting <= $20k) - the backtest behind this rule was run on
    // real toprate.au data, which skews city/provincial; bush meetings are
    // both a thin, untested slice of that backtest and, practically, the
    // races a user is least likely to actually bet.
    if (bushKeys.has(meetingKey(race))) continue
    const rated = race.runners.map((r) => ({ runner: r, wpr: effectiveWpr(r, bases) }))
    // A race with even one genuinely unrated runner (no model projection,
    // no manual base entered) is excluded - this is what "no first starter"
    // meant historically, but stated in terms of what actually matters
    // (does every runner have SOME rating), not the has_first_starter flag
    // itself, so a manually-entered base for that one first starter can
    // rescue the whole race back into eligibility.
    if (rated.some((x) => x.wpr == null)) continue
    const sorted = [...rated].sort((a, b) => (b.wpr as number) - (a.wpr as number))
    const rank1 = sorted[0]
    const rank2 = sorted[1]
    if (!rank1 || !rank2) continue
    const gap = (rank1.wpr as number) - (rank2.wpr as number)
    if (gap < minGap) continue
    // The price threshold is always the real market price (untouched by
    // rating overrides), not a model-implied one.
    if (rank1.runner.fixedWinPrice == null || rank1.runner.fixedWinPrice < minPrice) continue
    entries.push({ race, runner: rank1.runner, gap })
  }
  return entries
}

export type WatchlistStatus = 'pending' | 'settled' | 'void'

// The race itself (allResulted), not just this runner's finishPosition,
// decides pending vs. settled - a SCRATCHED runner never gets a
// finishPosition even after the race has long since been run, so gating on
// finishPosition alone left old scratches stuck showing PENDING forever.
// 'void' (race resulted, but this runner never got a finish - scratched, or
// a data gap) is excluded from both the pending list and the tally, same as
// the historical backtest excluded scratches (it required a non-null `won`).
export function watchlistStatus(entry: WatchlistEntry): WatchlistStatus {
  if (!entry.race.allResulted) return 'pending'
  return entry.runner.finishPosition != null ? 'settled' : 'void'
}

export function hasKnownOutcome(entry: WatchlistEntry): boolean {
  return watchlistStatus(entry) === 'settled'
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
