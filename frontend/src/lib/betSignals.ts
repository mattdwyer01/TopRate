import { useEffect, useState } from 'react'

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
const POLL_MS = 60_000

interface RawFile {
  made?: string
  trained_through?: string
  rules?: { freeze_mins?: number }
  runs?: Record<string, RunSignal>
}

export async function fetchBetSignals(): Promise<BetSignals | null> {
  try {
    const res = await fetch(FILE, { cache: 'no-cache' })
    if (!res.ok) return null
    const raw = (await res.json()) as RawFile
    if (!raw || typeof raw !== 'object' || !raw.runs) return null
    return { made: raw.made ?? '', trainedThrough: raw.trained_through ?? '', freezeMins: raw.rules?.freeze_mins ?? 5, runs: raw.runs }
  } catch {
    return null // optional layer: the dashboard works without it
  }
}

/** Latest bet signals, refreshed every minute. null until loaded, or when the file does not exist. */
export function useBetSignals(): BetSignals | null {
  const [signals, setSignals] = useState<BetSignals | null>(null)
  useEffect(() => {
    let cancelled = false
    const load = () => {
      fetchBetSignals().then((s) => {
        if (!cancelled && s) setSignals((prev) => (prev && prev.made === s.made ? prev : s))
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
