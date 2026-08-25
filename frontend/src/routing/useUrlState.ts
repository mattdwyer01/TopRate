import { useCallback, useEffect, useRef, useState } from 'react'

// Replicates the current dashboard's URL routing behavior
// (toprate_html_v3.py _rtPushRaceUrl/_rtApplyStateFromUrl, L6108-6184):
// ?tab=race&date=YYYY-MM-DD&race=<race_id>, pushState (no reload) on
// selecting a race, a plain ?tab=race&date=... with race cleared when
// browsing back to the meetings grid, and a popstate listener that
// re-applies whatever the URL currently says. Only the Race tab
// participates in URL state (matches current behavior - Phase 2/3 tabs can
// extend this later if that changes).
//
// _rtSyncing-equivalent guard: applying state FROM a popstate event must
// never itself push a new history entry, or back/forward becomes a loop.

export interface RaceUrlState {
  date: string | null
  raceId: string | null
  // Deep-links straight to a runner's detail panel within the race (set by
  // search and Review-tab cross-linking). Only ever consumed as RaceDetail's
  // initial selection, not kept in sync while the modal is open/closed -
  // see App.tsx's key={race.raceId} on RaceDetail for why that's enough.
  runId: string | null
}

function readFromLocation(): RaceUrlState {
  const params = new URLSearchParams(window.location.search)
  if (params.get('tab') !== 'race') return { date: null, raceId: null, runId: null }
  return {
    date: params.get('date'),
    raceId: params.get('race'),
    runId: params.get('run'),
  }
}

function buildSearch(state: RaceUrlState): string {
  const params = new URLSearchParams()
  params.set('tab', 'race')
  if (state.date) params.set('date', state.date)
  if (state.raceId) params.set('race', state.raceId)
  if (state.runId) params.set('run', state.runId)
  return `?${params.toString()}`
}

export function useUrlState() {
  const [state, setState] = useState<RaceUrlState>(() => readFromLocation())
  const syncing = useRef(false)

  useEffect(() => {
    function onPopState() {
      syncing.current = true
      setState(readFromLocation())
      syncing.current = false
    }
    window.addEventListener('popstate', onPopState)
    return () => window.removeEventListener('popstate', onPopState)
  }, [])

  const push = useCallback((next: RaceUrlState) => {
    if (syncing.current) return
    setState(next)
    const search = buildSearch(next)
    if (search !== window.location.search) {
      window.history.pushState(null, '', search)
    }
  }, [])

  return { urlState: state, pushUrlState: push }
}
