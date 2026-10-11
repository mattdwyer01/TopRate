import { useEffect, useState } from 'react'
import type { Race } from '../types/domain'

// Bet signals (Oct 2026, EXPERIMENTAL): a market-residual win model (betsignal/ in the repo). It starts from the current fixed price, corrects it
// with form, ratings and connections, and returns a win probability. Model price = 1 / probability, edge = probability x price - 1.
// Backtested against closing SP only (2022 to 2026, walk-forward); not yet shown to hold at a price taken before the jump. The scoreboard on
// the Plays tab is how that gets checked going forward, judged at the last pass made at least 5 minutes before the jump.
export type Tier = 'S' | 'V' | ''

export interface Signal {
  p: number // the fixed win price it was judged against
  m: number // model win probability
  e: number // probability x price (1.20 = 20% above break-even)
  t: Tier
  at: string // when this pass was made
  k: number // market rank by price (1 = favourite)
  // Set on backfilled signals (bet_signals_history.json): 'sp' = scored out of sample against the closing starting price, 'last' = against the last recorded
  // fixed price. Neither is a price taken before the jump, so they are listed and scored separately from live passes.
  bf?: 'sp' | 'last'
}

export interface RunSignal {
  now?: Signal // latest pass
  fz?: Signal // last pass made at least `freezeMins` before the jump: what the scoreboard judges
  d: string
}

export interface BetSignals {
  made: string
  trainedThrough: string
  freezeMins: number
  runs: Record<string, RunSignal>
}

// Stakes by tier, in units (1 unit = $50). Select carries the edge; Volume is the action tier and costs a little (backtest -3% on its own), so it is small.
export const TIER_UNITS: Record<'S' | 'V', number> = { S: 2, V: 0.25 }
export const UNIT_DOLLARS = 50

export const TIER_LABEL: Record<'S' | 'V', string> = { S: 'Select', V: 'Volume' }
export const TIER_HELP: Record<'S' | 'V', string> = {
  S: 'Select: the model rates this clearly above the price (edge above 20%, or above 30% for the favourite). Backtested at SP: about 120 bets a year, ROI about +53%, positive in every year. Not yet shown at a price taken before the jump.',
  V: 'Volume: edge above 5% at $3 or more, about 10 bets a Saturday. Backtested at SP these lose about 3% on their own (13% with a price 10% worse): it is the action tier, so the stake is small.',
}

export const modelPrice = (m: number | null | undefined): number | null => (m != null && m > 0 ? 1 / m : null)
export const edgePct = (e: number | null | undefined): number | null => (e != null ? (e - 1) * 100 : null)

export function fmtEdge(e: number | null | undefined): string {
  const v = edgePct(e)
  if (v == null) return ''
  return `${v >= 0 ? '+' : ''}${v.toFixed(0)}%`
}

/** Stake in dollars for a number of units: $100, $12.50. */
export function fmtStake(units: number): string {
  const v = units * UNIT_DOLLARS
  return Number.isInteger(v) ? `$${v}` : `$${v.toFixed(2)}`
}

/** The pass to show: the live pass before the jump, the frozen pre-jump pass afterwards. */
export function signalFor(sig: RunSignal | undefined, jumped: boolean): Signal | null {
  if (!sig) return null
  return (jumped ? (sig.fz ?? sig.now) : (sig.now ?? sig.fz)) ?? null
}

const FILE = 'bet_signals.json'
const HISTORY_FILE = 'bet_signals_history.json'
const POLL_MS = 60_000

interface RawFile {
  made?: string
  trained_through?: string
  rules?: { freeze_mins?: number }
  runs?: Record<string, RunSignal>
}

// Backfilled days (betsignal/backfill.py): runs[run_id] = [price, probability, edge, tier, market rank], days[date] = 'sp' | 'last'.
interface RawHistory {
  days?: Record<string, 'sp' | 'last'>
  runs?: Record<string, [number, number, number, Tier, number, 'sp' | 'last']>
}

let historyPromise: Promise<Record<string, RunSignal>> | null = null

// Read once per page load: it only changes when the backfill is re-run.
function fetchHistory(): Promise<Record<string, RunSignal>> {
  if (!historyPromise) {
    historyPromise = (async () => {
      try {
        const res = await fetch(HISTORY_FILE, { cache: 'no-cache' })
        if (!res.ok) return {}
        const raw = (await res.json()) as RawHistory
        const out: Record<string, RunSignal> = {}
        for (const [id, v] of Object.entries(raw.runs ?? {})) {
          out[id] = { d: '', fz: { p: v[0], m: v[1], e: v[2], t: v[3], at: '', k: v[4], bf: v[5] ?? 'sp' } }
        }
        return out
      } catch {
        return {}
      }
    })()
  }
  return historyPromise
}

export async function fetchBetSignals(): Promise<BetSignals | null> {
  const history = await fetchHistory()
  let live: RawFile | null = null
  try {
    const res = await fetch(FILE, { cache: 'no-cache' })
    if (res.ok) live = (await res.json()) as RawFile
  } catch {
    live = null
  }
  const liveRuns = live && typeof live === 'object' && live.runs ? live.runs : {}
  const runs: Record<string, RunSignal> = { ...history, ...liveRuns }   // a live pass always wins over a backfilled one
  if (Object.keys(runs).length === 0) return null
  return { made: live?.made ?? '', trainedThrough: live?.trained_through ?? '', freezeMins: live?.rules?.freeze_mins ?? 5, runs }
}

/** Latest bet signals (live passes over backfilled history), refreshed every minute. null until loaded, or when neither file exists. */
export function useBetSignals(): BetSignals | null {
  const [signals, setSignals] = useState<BetSignals | null>(null)
  useEffect(() => {
    let cancelled = false
    const load = () => {
      fetchBetSignals().then((s) => {
        if (!cancelled && s) setSignals((prev) => (prev && prev.made === s.made && Object.keys(prev.runs).length === Object.keys(s.runs).length ? prev : s))
      })
    }
    load()
    const t = window.setInterval(load, POLL_MS)
    return () => {
      cancelled = true
      window.clearInterval(t)
    }
  }, [])
  return signals
}

// The bet-signal rating (Oct 2026): the model's win probabilities turned into ratings on the ATW scale (it is blended with the WPR projection, see RATING_BET_SHARE). Within a race a runner's rating is
//   level + RATING_PER_LN x (ln p - mean ln p)
// where level is the field's average WPR-projection rating at today's weight, so the numbers sit on the same scale as the Recent runs table. RATING_PER_LN
// is not the price beta inverted (5 rating points per ln p at beta 0.20): over 85k races the actual rating moved 0.73 for each point of that raw
// conversion, so it is shrunk by that factor (5 x 0.73 = 3.66) to make the number a calibrated prediction of the rating the horse will run.
export const RATING_PER_LN = 3.66

// The rating shown is a BLEND of the bet-signal rating and the WPR projection, not the bet-signal rating alone: the bet-signal rating is the market's own
// order (its #1 is the market favourite in 99.5% of races, rank correlation 0.99), so it told you little the Fixed $ column did not. 1,692 July to October
// 2026 races: a 45% share keeps #1 = favourite in 77% of races (rank correlation 0.90), picks the winner as #1 in 32.4% (projection alone 28.4%, bet rating
// alone 34.3%), has the lowest error against the rating actually run (8.63 against 8.74 projection, 8.78 bet rating) and winner log-loss 1.814 (projection
// 1.936, bet rating 1.766, market 1.770). 40% to 50% are within noise of each other; below about 40% winner picking drops away, above 60% it is mostly the market.
export const RATING_BET_SHARE = 0.45

/** Signal per runner for one race: the live pass before the jump, the frozen pass once it has run. Runners with none are null. */
export function signalsForRace(race: Race, signals: BetSignals | null, now = Date.now()): Record<string, Signal | null> {
  const jumped = race.runners.some((r) => r.finishPosition !== null || r.resultKnown) || (race.startTime ? new Date(race.startTime).getTime() < now : false)
  const m: Record<string, Signal | null> = {}
  for (const r of race.runners) m[r.runId] = signalFor(signals?.runs[r.runId], jumped)
  return m
}
