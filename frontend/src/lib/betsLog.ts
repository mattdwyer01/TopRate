import { useEffect, useState } from 'react'
import type { Race } from '../types/domain'

// The frozen bet record (bets_log.json, written by the TAB poller's bet_log.py): each bet is locked ~10 minutes before
// its race (a quaddie before its first leg) and settled from TAB's real dividends. Read by the Bets tab and by the
// race page's Bets card, which shows the logged bet and its result in place of the live rule once a bet is logged.

export type LoggedKind = 'Win' | 'Trifecta' | 'Quinella' | 'Quaddie' | 'EarlyQuaddie'

export interface LoggedBet {
  bet_id: string
  date: string
  venue: string
  race: number
  race_id: string
  start_utc: string
  bet: LoggedKind
  legs: string // '5' for a single race, '5-8' for a quaddie
  selection: string
  combos: number
  stake: number
  price: number | null
  flexi_pct: number
  status: 'pending' | 'won' | 'lost' | 'refund' | 'void'
  winners: string | null
  dividend: number | null
  return: number | null
  profit: number | null
}

// One shared fetch for every component that wants the log, refreshed each minute.
let cache: LoggedBet[] | null = null
let cacheError: string | null = null
const listeners = new Set<() => void>()
let timer: number | null = null

function load() {
  fetch(`bets_log.json?t=${Date.now()}`, { cache: 'no-store' })
    .then((r) => (r.ok ? r.json() : Promise.reject(new Error(`HTTP ${r.status}`))))
    .then((j) => {
      cache = j.bets ?? []
      cacheError = null
    })
    .catch((e) => {
      cacheError = e instanceof Error && e.message === 'HTTP 404' ? 'No bets logged yet.' : 'Could not load the bets log.'
    })
    .finally(() => listeners.forEach((f) => f()))
}

export function useBetsLog(): { bets: LoggedBet[] | null; error: string | null } {
  const [, tick] = useState(0)
  useEffect(() => {
    const f = () => tick((n) => n + 1)
    listeners.add(f)
    if (listeners.size === 1) {
      load()
      timer = window.setInterval(load, 60_000)
    }
    return () => {
      listeners.delete(f)
      if (listeners.size === 0 && timer != null) {
        window.clearInterval(timer)
        timer = null
      }
    }
  }, [])
  return { bets: cache, error: cacheError }
}

// Logged bets that cover this race: its own win / quinella / trifecta, and any quaddie with this race as a leg.
export function betsForRace(bets: LoggedBet[] | null, race: Race): LoggedBet[] {
  if (!bets) return []
  return bets.filter((b) => {
    if (b.bet === 'Quaddie' || b.bet === 'EarlyQuaddie') {
      if (b.date !== race.date || b.venue !== race.venue) return false
      const [lo, hi] = b.legs.split('-').map(Number)
      return race.raceNumber >= lo && race.raceNumber <= (hi ?? lo)
    }
    return b.race_id === race.raceId
  })
}
