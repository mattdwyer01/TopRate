import { useEffect } from 'react'
import { useDashboardData, freshnessLevel } from './hooks/useDashboardData'
import { useUrlState } from './routing/useUrlState'
import { MeetingsGrid } from './features/race/MeetingsGrid'
import { ErrorState, EmptyState } from './components/EmptyState'
import { FreshnessDot } from './components/FreshnessDot'
import { RaceDetail } from './features/race/RaceDetail'

function App() {
  const { state, retry } = useDashboardData()
  const { urlState, pushUrlState } = useUrlState()

  // Boot-time deep-link handling: if the URL already names a race (a shared
  // link or a page reload mid-session), that wins over the default meetings
  // view once data loads - matches __initDashboard's "shared link wins"
  // behavior (toprate_html_v3.py L5376-5421).
  useEffect(() => {
    if (state.status !== 'ready') return
    if (!urlState.raceId) return
    const raceExists = state.data.races.some((r) => r.raceId === urlState.raceId)
    if (!raceExists) {
      // Stale/invalid link - fall back to the meetings view rather than
      // getting stuck on a race that no longer resolves.
      pushUrlState({ date: urlState.date, raceId: null })
    }
    // Only needs to run once data becomes ready.
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [state.status])

  return (
    <div className="min-h-screen bg-bg text-ink">
      <header className="sticky top-0 z-10 border-b border-line bg-panel px-4 py-3">
        <div className="mx-auto flex max-w-6xl items-center justify-between">
          <h1 className="text-lg font-semibold text-emerald">TopRate</h1>
          {state.status === 'ready' && (
            <FreshnessDot
              level={freshnessLevel(state.data.runIso)}
              runDate={state.data.runDate}
            />
          )}
        </div>
      </header>

      <main className="mx-auto max-w-6xl px-4 py-4">
        {state.status === 'loading' && (
          <EmptyState message="Loading today's races..." />
        )}
        {state.status === 'error' && (
          <ErrorState message={state.message} onRetry={retry} />
        )}
        {state.status === 'ready' &&
          (urlState.raceId ? (
            <RaceDetail
              race={state.data.races.find((r) => r.raceId === urlState.raceId)!}
              allRaces={state.data.races}
              onBack={() => pushUrlState({ date: urlState.date, raceId: null })}
              onSelectRace={(raceId, date) => pushUrlState({ date, raceId })}
            />
          ) : (
            <MeetingsGrid
              races={state.data.races}
              initialDate={urlState.date}
              onSelectRace={(raceId, date) => pushUrlState({ date, raceId })}
            />
          ))}
      </main>
    </div>
  )
}

export default App
