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

// The backend now typically publishes a live update within under a minute
// of a TAB poll cycle starting (see tab_results_poller.py's PUBLISHING
// docstring section - most cycles patch toprate_data.json directly rather
// than waiting for a full rebuild), so 5 minutes was leaving real updates
// sitting unseen for most of that window. 60s keeps detection latency
// close to how fast the data actually changes without polling pointlessly
// often - each poll is a conditional GET (`cache: 'no-cache'` in
// fetchData.ts revalidates against the server's ETag/Last-Modified rather
// than blindly re-downloading), so an unchanged ~90MB payload costs a
// cheap 304, not a full re-fetch.
const REFRESH_INTERVAL_MS = 60_000

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
    const poll = () => {
      fetchDashboardData()
        .then((data) => setState({ status: 'ready', data }))
        .catch(() => {})
    }
    const id = setInterval(poll, REFRESH_INTERVAL_MS)
    // Browsers throttle/suspend setInterval in a backgrounded tab, so the
    // most common "why hasn't this updated" moment is exactly the one the
    // timer alone handles worst: switching back to a tab that's been
    // sitting in the background. Poll immediately on becoming visible
    // again instead of waiting for the next (possibly overdue) tick.
    const onVisible = () => {
      if (document.visibilityState === 'visible') poll()
    }
    document.addEventListener('visibilitychange', onVisible)
    return () => {
      clearInterval(id)
      document.removeEventListener('visibilitychange', onVisible)
    }
  }, [])

  return { state, retry }
}
