import type { Race, Runner } from '../types/domain'
import { signalFor, TIER_UNITS, type BetSignals, type Signal } from './betSignals'

// Bets for the Plays tab (Oct 2026, EXPERIMENTAL). A bet is a runner whose bet-signal tier is Select or Volume. Before the jump the live pass is used;
// once the race has run, the frozen pass (last made at least a few minutes before the jump) so a bet never changes after the result.
export type Outcome = 'won' | 'placed' | 'unplaced' | 'pending'

export interface Bet {
  key: string
  race: Race
  runner: Runner
  tier: 'S' | 'V'
  units: number
  sig: Signal
  // Price the bet is judged at: the fixed price when the pass was made (not SP).
  price: number
  // Set when the signal was backfilled rather than a live pass: 'sp' (closing starting price) or 'last' (last recorded fixed price).
  backfilled: 'sp' | 'last' | null
  outcome: Outcome
  // Units won (negative = lost). 0 while pending.
  profit: number
  fieldSize: number
}

/** Paying places for a field: 3 for 8 or more runners, 2 for 5 to 7, none below. */
export function placesPaid(starters: number): number {
  return starters >= 8 ? 3 : starters >= 5 ? 2 : 0
}

function outcomeOf(runner: Runner, starters: number): Outcome {
  if (runner.won || runner.finishPosition === 1) return 'won'
  const places = placesPaid(starters)
  if (runner.finishPosition != null) return places > 0 && runner.finishPosition <= places ? 'placed' : 'unplaced'
  if (runner.resultKnown) return 'unplaced'
  return 'pending'
}

function raceHasRun(race: Race): boolean {
  return race.runners.some((r) => r.resultKnown || r.finishPosition != null)
}

export function computeBets(races: Race[], signals: BetSignals | null, scratched: Set<string>): Bet[] {
  if (!signals) return []
  const out: Bet[] = []
  for (const race of races) {
    const jumped = raceHasRun(race) || (race.startTime ? new Date(race.startTime).getTime() < Date.now() : false)
    const starters = race.runners.filter((r) => !r.dataScratched).length
    for (const r of race.runners) {
      if (r.dataScratched || scratched.has(r.runId)) continue
      const sig = signalFor(signals.runs[r.runId], jumped)
      if (!sig || (sig.t !== 'S' && sig.t !== 'V')) continue
      const units = TIER_UNITS[sig.t]
      const outcome = outcomeOf(r, starters)
      out.push({
        key: `${race.raceId}|${r.runId}`,
        race,
        runner: r,
        tier: sig.t,
        units,
        sig,
        price: sig.p,
        backfilled: sig.bf ?? null,
        outcome,
        profit: outcome === 'pending' ? 0 : outcome === 'won' ? units * (sig.p - 1) : -units,
        fieldSize: starters,
      })
    }
  }
  return out.sort((a, b) => (a.race.startTime ?? '').localeCompare(b.race.startTime ?? '') || a.race.raceNumber - b.race.raceNumber || a.runner.tabNumber - b.runner.tabNumber)
}

export interface Tally {
  bets: number
  run: number
  wins: number
  places: number
  staked: number // units, run bets only
  profit: number // units
  avgPrice: number | null
  // Profit over units staked, run bets only.
  roi: number | null
  // Flat 1 unit per bet, for comparison with the backtest numbers.
  flatRoi: number | null
}

export function tally(bets: Bet[]): Tally {
  const run = bets.filter((b) => b.outcome !== 'pending')
  const staked = run.reduce((s, b) => s + b.units, 0)
  const profit = run.reduce((s, b) => s + b.profit, 0)
  const flat = run.reduce((s, b) => s + (b.outcome === 'won' ? b.price - 1 : -1), 0)
  return {
    bets: bets.length,
    run: run.length,
    wins: run.filter((b) => b.outcome === 'won').length,
    places: run.filter((b) => b.outcome === 'won' || b.outcome === 'placed').length,
    staked,
    profit,
    avgPrice: run.length ? run.reduce((s, b) => s + b.price, 0) / run.length : null,
    roi: staked > 0 ? profit / staked : null,
    flatRoi: run.length ? flat / run.length : null,
  }
}
