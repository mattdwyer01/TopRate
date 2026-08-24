import { useEffect, useMemo, useState } from 'react'
import { useDashboardData, freshnessLevel } from './hooks/useDashboardData'
import { useUrlState } from './routing/useUrlState'
import { useBetaOverride } from './lib/priceBetaOverride'
import { useShowBushMeetings } from './lib/bushMeetings'
import { bushMeetingKeys, meetingKey } from './lib/meetings'
import { MeetingsGrid } from './features/race/MeetingsGrid'
import { ErrorState, EmptyState } from './components/EmptyState'
import { FreshnessDot } from './components/FreshnessDot'
import { NextToJumpTicker } from './components/NextToJumpTicker'
import { SettingsModal } from './components/SettingsModal'
import { HowWprWorksModal } from './components/HowWprWorksModal'
import { RaceDetail } from './features/race/RaceDetail'
import { ReviewTab } from './features/review/ReviewTab'

type TopTab = 'race' | 'review'

function readTopTab(): TopTab {
  return new URLSearchParams(window.location.search).get('tab') === 'review' ? 'review' : 'race'
}

function App() {
  const { state, retry } = useDashboardData()
  const { urlState, pushUrlState } = useUrlState()
  const { betaOverride, setBetaOverride } = useBetaOverride()
  const { showBush, setShowBush } = useShowBushMeetings()
  const [settingsOpen, setSettingsOpen] = useState(false)
  const [methodologyOpen, setMethodologyOpen] = useState(false)
  const [topTab, setTopTabState] = useState<TopTab>(() => readTopTab())

  // Keep topTab in sync with back/forward navigation - separate from
  // useUrlState's own popstate handling (that hook only tracks the Race
  // tab's date/race params), so both listeners just re-derive independently.
  useEffect(() => {
    function onPopState() {
      setTopTabState(readTopTab())
    }
    window.addEventListener('popstate', onPopState)
    return () => window.removeEventListener('popstate', onPopState)
  }, [])

  function switchTab(tab: TopTab) {
    setTopTabState(tab)
    if (tab === 'review') {
      if (window.location.search !== '?tab=review') {
        window.history.pushState(null, '', '?tab=review')
      }
    } else {
      pushUrlState({ date: urlState.date, raceId: urlState.raceId })
    }
  }

  function goToRace(raceId: string, date: string) {
    setTopTabState('race')
    pushUrlState({ date, raceId })
  }

  const tickerRaces = useMemo(() => {
    if (state.status !== 'ready') return []
    if (showBush) return state.data.races
    const bushKeys = bushMeetingKeys(state.data.races)
    return state.data.races.filter((r) => !bushKeys.has(meetingKey(r)))
  }, [state, showBush])

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
      <header className="sticky top-0 z-10 flex flex-col gap-2 border-b border-line bg-panel px-4 py-3">
        <div className="mx-auto flex w-full max-w-6xl items-center justify-between">
          <div className="flex items-center gap-4">
            <h1 className="text-lg font-semibold text-emerald">TopRate</h1>
            <nav className="flex rounded-md border border-line bg-bg p-0.5">
              <button
                type="button"
                onClick={() => switchTab('race')}
                className={
                  'rounded px-2.5 py-1 text-sm font-medium transition-colors ' +
                  (topTab === 'race' ? 'bg-panel text-ink shadow-[var(--shadow-1)]' : 'text-ink-mute hover:text-ink')
                }
              >
                Race
              </button>
              <button
                type="button"
                onClick={() => switchTab('review')}
                className={
                  'rounded px-2.5 py-1 text-sm font-medium transition-colors ' +
                  (topTab === 'review' ? 'bg-panel text-ink shadow-[var(--shadow-1)]' : 'text-ink-mute hover:text-ink')
                }
              >
                Review
              </button>
            </nav>
          </div>
          <div className="flex items-center gap-3">
            {state.status === 'ready' && (
              <FreshnessDot
                level={freshnessLevel(state.data.runIso)}
                runDate={state.data.runDate}
              />
            )}
            <div className="relative">
              <button
                type="button"
                onClick={() => setSettingsOpen(true)}
                aria-label={betaOverride != null ? 'Settings (custom price sharpness active)' : 'Settings'}
                className="flex h-7 w-7 items-center justify-center rounded-md text-ink-mute transition-colors hover:bg-bg hover:text-ink"
              >
                ⚙
              </button>
              {betaOverride != null && (
                <span
                  className="pointer-events-none absolute -right-0.5 -top-0.5 h-2 w-2 rounded-full bg-amber ring-2 ring-panel"
                  title="Custom WPR $ price sharpness active"
                />
              )}
            </div>
          </div>
        </div>
        {state.status === 'ready' && topTab === 'race' && (
          <div className="mx-auto w-full max-w-6xl">
            <NextToJumpTicker
              races={tickerRaces}
              onSelectRace={goToRace}
            />
          </div>
        )}
      </header>

      <main className="mx-auto max-w-6xl px-4 py-4">
        {state.status === 'loading' && (
          <EmptyState message="Loading today's races..." progress={state.progress} />
        )}
        {state.status === 'error' && (
          <ErrorState message={state.message} onRetry={retry} />
        )}
        {state.status === 'ready' && topTab === 'review' && (
          <ReviewTab races={state.data.races} onSelectRace={goToRace} />
        )}
        {state.status === 'ready' && topTab === 'race' &&
          (urlState.raceId ? (
            <RaceDetail
              race={state.data.races.find((r) => r.raceId === urlState.raceId)!}
              allRaces={state.data.races}
              priceBeta={betaOverride ?? state.data.priceBeta}
              onBack={() => pushUrlState({ date: urlState.date, raceId: null })}
              onSelectRace={goToRace}
            />
          ) : (
            <MeetingsGrid
              races={state.data.races}
              initialDate={urlState.date}
              onSelectRace={goToRace}
              showBush={showBush}
              onShowBushChange={setShowBush}
            />
          ))}
      </main>

      {settingsOpen && (
        <SettingsModal
          serverBeta={state.status === 'ready' ? state.data.priceBeta : null}
          betaOverride={betaOverride}
          onSetBetaOverride={setBetaOverride}
          onClose={() => setSettingsOpen(false)}
          onOpenMethodology={() => {
            setSettingsOpen(false)
            setMethodologyOpen(true)
          }}
        />
      )}

      {methodologyOpen && <HowWprWorksModal onClose={() => setMethodologyOpen(false)} />}
    </div>
  )
}

export default App
