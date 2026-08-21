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
  | { status: 'loading' }
  | { status: 'error'; message: string }
  | { status: 'ready'; data: DashboardData }

export function useDashboardData() {
  const [state, setState] = useState<State>({ status: 'loading' })
  const [reloadToken, setReloadToken] = useState(0)

  const retry = useCallback(() => {
    setState({ status: 'loading' })
    setReloadToken((t) => t + 1)
  }, [])

  useEffect(() => {
    let cancelled = false
    fetchDashboardData()
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

  return { state, retry }
}
