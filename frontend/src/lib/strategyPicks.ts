import { useCallback, useState } from 'react'
import type { EdgeTier } from './edgeOverlay'

// Tracks which Edge Overlays qualifiers the user actually took, so the tab
// can show real forward performance instead of only the historical
// backtest. Persisted per-device (same pattern as useShowBushMeetings) -
// not yet synced across devices via the GitHub Gist mechanism, since a
// bet log needs additive merging on pull rather than the overwrite the
// existing sync does for simple preferences.
//
// Storage key bumped (was toprate_strategy_picks_v1) when the underlying
// signal changed from the leaky jtComboWinPct tiers to edge overlays (Aug
// 2026) - old entries used a different tier enum ('high-volume' etc.) that
// would silently mis-group under EdgeScoreboard's edge-tier buckets, so
// this starts fresh rather than risk mixing the two.
const STORAGE_KEY = 'toprate_edge_picks_v1'

export interface StrategyPick {
  runId: string
  raceId: string
  date: string
  tier: EdgeTier
  takenAt: string
}

// Exported for lib/githubSync.ts - cross-device sync needs to read/write
// this same storage to merge picks made on another device, rather than
// going through the hook (which only runs inside a mounted component).
export function readStoredPicks(): Record<string, StrategyPick> {
  try {
    const raw = window.localStorage.getItem(STORAGE_KEY)
    if (!raw) return {}
    const parsed = JSON.parse(raw)
    return typeof parsed === 'object' && parsed != null ? parsed : {}
  } catch {
    return {}
  }
}

export function writeStoredPicks(picks: Record<string, StrategyPick>) {
  try {
    window.localStorage.setItem(STORAGE_KEY, JSON.stringify(picks))
  } catch {
    // localStorage can throw in private-browsing/storage-full states - the
    // in-memory picks still work for the rest of this session.
  }
}

export function useStrategyPicks() {
  const [picks, setPicks] = useState<Record<string, StrategyPick>>(() => readStoredPicks())

  const toggleTaken = useCallback((runId: string, raceId: string, date: string, tier: EdgeTier) => {
    setPicks((prev) => {
      const next = { ...prev }
      if (next[runId]) {
        delete next[runId]
      } else {
        next[runId] = { runId, raceId, date, tier, takenAt: new Date().toISOString() }
      }
      writeStoredPicks(next)
      return next
    })
  }, [])

  return { picks, toggleTaken }
}
