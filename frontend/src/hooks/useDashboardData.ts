import { useCallback, useEffect, useState } from 'react'
import { fetchDashboardData } from '../api/fetchData'
import type { DashboardData } from '../types/domain'

export type FreshnessLevel = 'fresh' | 'aging' | 'stale'

// Same thresholds as the current dashboard's freshness dot
// (toprate_html_v3.py #freshness-dot: green <10min, amber <30min, red beyond).
const FRESH_MINUTES = 10
const AGING_MINUTES = 30

export function freshnessLevel(runIso: string, now = new Date()): FreshnessLevel {
  const ageMs = now.getTime() - new Date(runIso).getTime()
  const ageMinutes = ageMs / 60_000
  if (ageMinutes < FRESH_MINUTES) return 'fresh'
  if (ageMinutes < AGING_MINUTES) return 'aging'
  return 'stale'
}

type State =
  | { status: 'loading'; progress: number | null }
  | { status: 'error'; message: string }
  | { status: 'ready'; data: DashboardData }

// Matches the backend's own price-refresh cadence (.github/workflows/
// price_refresh.yml runs every 5 minutes during racing hours) - polling
// faster than the source data actually changes would just be wasted
// bandwidth against a ~90MB payload.
const REFRESH_INTERVAL_MS = 5 * 60_000

export function useDashboardData() {
  const [state, setState] = useState<State>({ status: 'loading', progress: null })
  const [reloadToken, setReloadToken] = useState(0)

  const retry = useCallback(() => {
    setState({ status: 'loading', progress: null })
    setReloadToken((t) => t + 1)
  }, [])

  useEffect(() => {
    let cancelled = false
    fetchDashboardData((pct) => {
      if (!cancelled) setState({ status: 'loading', progress: pct })
    })
      .then((data) => {
        if (!cancelled) setState({ status: 'ready', data })
      })
      .catch((err: Error) => {
        if (!cancelled) setState({ status: 'error', message: err.message })
      })
    return () => {
      cancelled = true
    }
  }, [reloadToken])

  // Background refresh so an open tab doesn't quietly go stale during
  // racing hours - deliberately doesn't flip status back to 'loading' (no
  // flash) and a failed poll just leaves the last-known-good data in place
  // rather than surfacing an error for what's likely a transient blip; the
  // next poll (or an error state's own Retry) will recover it. A poll that
  // succeeds while in an error state recovers automatically.
  useEffect(() => {
    const id = setInterval(() => {
      fetchDashboardData()
        .then((data) => setState({ status: 'ready', data }))
        .catch(() => {})
    }, REFRESH_INTERVAL_MS)
    return () => clearInterval(id)
  }, [])

  return { state, retry }
}
