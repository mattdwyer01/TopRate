import { useCallback, useState } from 'react'

// Per-device override of the Watchlist thresholds (see lib/watchlist.ts) -
// editable from Settings rather than hardcoded, since the backtest behind
// them is thin (a handful of months of one account's data) and the right
// values are a judgment call worth being able to tune without a redeploy.
const STORAGE_KEY = 'toprate_watchlist_thresholds_v1'

export interface WatchlistThresholds {
  minGap: number
  minPrice: number
}

// gap>=2.0 & price>=4.0 (Aug 2026 default): the split-half backtest actually
// found price>=4.0 slightly negative at this gap (-1.2% ROI held-out) - the
// lowest price that tested cleanly positive at gap>=2.0 was ~$4.50-5.00. Set
// to $4.00 anyway per explicit user choice, to watch it play out live rather
// than assume the backtest's verdict holds going forward. Adjust in Settings.
export const DEFAULT_THRESHOLDS: WatchlistThresholds = { minGap: 2.0, minPrice: 4.0 }

function readStored(): WatchlistThresholds {
  try {
    const raw = window.localStorage.getItem(STORAGE_KEY)
    if (!raw) return DEFAULT_THRESHOLDS
    const parsed = JSON.parse(raw)
    const minGap = Number(parsed.minGap)
    const minPrice = Number(parsed.minPrice)
    if (!Number.isFinite(minGap) || !Number.isFinite(minPrice)) return DEFAULT_THRESHOLDS
    return { minGap, minPrice }
  } catch {
    return DEFAULT_THRESHOLDS
  }
}

export function useWatchlistThresholds() {
  const [thresholds, setThresholdsState] = useState<WatchlistThresholds>(() => readStored())

  const setThresholds = useCallback((next: WatchlistThresholds) => {
    setThresholdsState(next)
    try {
      window.localStorage.setItem(STORAGE_KEY, JSON.stringify(next))
    } catch {
      // localStorage can throw in private-browsing/storage-full states -
      // the in-memory value still works for the rest of the session.
    }
  }, [])

  return { thresholds, setThresholds }
}
