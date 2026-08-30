import { useCallback, useState } from 'react'
import type { StrategyTier } from './jtComboStrategy'

// Tracks which Strategy-tab qualifiers the user actually took, so the tab
// can show real forward performance instead of only the historical
// backtest. Persisted per-device (same pattern as useShowBushMeetings) -
// not yet synced across devices via the GitHub Gist mechanism, since a
// bet log needs additive merging on pull rather than the overwrite the
// existing sync does for simple preferences.
const STORAGE_KEY = 'toprate_strategy_picks_v1'

export interface StrategyPick {
  runId: string
  raceId: string
  date: string
  tier: StrategyTier
  takenAt: string
}

function readStored(): Record<string, StrategyPick> {
  try {
    const raw = window.localStorage.getItem(STORAGE_KEY)
    if (!raw) return {}
    const parsed = JSON.parse(raw)
    return typeof parsed === 'object' && parsed != null ? parsed : {}
  } catch {
    return {}
  }
}

function writeStored(picks: Record<string, StrategyPick>) {
  try {
    window.localStorage.setItem(STORAGE_KEY, JSON.stringify(picks))
  } catch {
    // localStorage can throw in private-browsing/storage-full states - the
    // in-memory picks still work for the rest of this session.
  }
}

export function useStrategyPicks() {
  const [picks, setPicks] = useState<Record<string, StrategyPick>>(() => readStored())

  const toggleTaken = useCallback((runId: string, raceId: string, date: string, tier: StrategyTier) => {
    setPicks((prev) => {
      const next = { ...prev }
      if (next[runId]) {
        delete next[runId]
      } else {
        next[runId] = { runId, raceId, date, tier, takenAt: new Date().toISOString() }
      }
      writeStored(next)
      return next
    })
  }, [])

  return { picks, toggleTaken }
}
