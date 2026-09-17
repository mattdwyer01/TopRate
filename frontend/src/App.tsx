import { useEffect, useMemo, useState } from 'react'
import { useDashboardData, freshnessLevel } from './hooks/useDashboardData'
import { useNow } from './hooks/useNow'
import { useUrlState } from './routing/useUrlState'
import { useBetaOverride } from './lib/priceBetaOverride'
import { useWprOverrides } from './lib/wprOverrides'
import { useShowBushMeetings } from './lib/bushMeetings'
import { bushMeetingKeys, meetingKey } from './lib/meetings'
import { MeetingsGrid } from './features/race/MeetingsGrid'
import { ErrorState, EmptyState } from './components/EmptyState'
import { FreshnessDot } from './components/FreshnessDot'
import { NextToJumpTicker } from './components/NextToJumpTicker'
import { SettingsModal } from './components/SettingsModal'
import { HowWprWorksModal } from './components/HowWprWorksModal'
import { GlobalSearch } from './components/GlobalSearch'
import { RaceDetail } from './features/race/RaceDetail'
import { ReviewTab } from './features/review/ReviewTab'
import { TrackersTab } from './features/trackers/TrackersTab'

type TopTab = 'race' | 'review' | 'trackers'

function readTopTab(): TopTab {
  const t = new URLSearchParams(window.location.search).get('tab')
  return t === 'review' || t === 'trackers' ? t : 'race'
}

function App() {
  const { state, retry } = useDashboardData()
  const now = useNow()
  const { urlState, pushUrlState } = useUrlState()
  const { betaOverride, setBetaOverride } = useBetaOverride()
  const { deltas, bases, scratched, setDelta, setBase, setScratched } = useWprOverrides()
  const { showBush, setShowBush } = useShowBushMeetings()
  const [settingsOpen, setSettingsOpen] = useState(false)
  const [methodologyOpen, setMethodologyOpen] = useState(false)
  const [searchOpen, setSearchOpen] = useState(false)
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

  // "/" opens search, matching the common convention (GitHub, etc) - guarded
  // against firing while the user is already typing in some other field.
  useEffect(() => {
    function onKey(e: KeyboardEvent) {
      if (e.key !== '/') return
      const tag = (e.target as HTMLElement | null)?.tagName
      if (tag === 'INPUT' || tag === 'TEXTAREA') return
      e.preventDefault()
      setSearchOpen(true)
    }
    window.addEventListener('keydown', onKey)
    return () => window.removeEventListener('keydown', onKey)
  }, [])

  function switchTab(tab: TopTab) {
    setTopTabState(tab)
    if (tab === 'review' || tab === 'trackers') {
      const q = `?tab=${tab}`
      if (window.location.search !== q) {
        window.history.pushState(null, '', q)
      }
    } else {
      pushUrlState({ date: urlState.date, raceId: urlState.raceId, runId: null })
    }
  }

  function goToRace(raceId: string, date: string, runId?: string) {
    setTopTabState('race')
    pushUrlState({ date, raceId, runId: runId ?? null })
    // The page itself doesn't remount on a tab switch, so without this the
    // Race tab opens at whatever scroll position the caller (Summary tab,
    // Review tab, the next-to-jump ticker) was left at, not the top of the
    // race just navigated to - real user feedback, 2026-09-17.
    window.scrollTo(0, 0)
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
      pushUrlState({ date: urlState.date, raceId: null, runId: null })
    }
    // Only needs to run once data becomes ready.
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [state.status])

  return (
    <div className="min-h-screen bg-bg text-ink">
      {/* z-30, not z-10: this is the one sticky header that must always sit
          above EVERY other in-page sticky element (RunnerRow's sticky
          silk/name cells, RaceDetail's sticky table header, MeetingsGrid's
          sticky venue column - all z-10, some z-20). Those don't establish
          their own stacking context, so at equal z-index the LATER one in
          DOM order wins the paint order - and the runner table renders
          after this header, so a plain z-10 here let a scrolled row's
          sticky silk/name cells paint on top of the ticker/nav (reported:
          a runner row visually floating over the ticker mid-scroll,
          reproduced in a plain scroll test, not iOS-Safari-specific). */}
      <header className="sticky top-0 z-30 flex flex-col gap-2 border-b border-line bg-panel px-4 py-3">
        {state.status === 'ready' && (
          <div className="mx-auto w-full max-w-6xl">
            <NextToJumpTicker
              races={tickerRaces}
              onSelectRace={goToRace}
            />
          </div>
        )}
        <div className="mx-auto flex w-full max-w-6xl items-center justify-between">
          <div className="flex items-center gap-2 sm:gap-4">
            {/* text-base/px-1.5/text-xs below sm: the full-size header (logo
                + 3 tabs + freshness/search/settings) needs ~379px of natural
                content width, which doesn't fit inside common phone
                viewports (360-393px, ~328-361px of room once the header's
                own px-4 side padding and the icon cluster are accounted
                for) - real bug found via a UX audit (2026-09-17): with
                nothing shrinking, the overflow silently forced the WHOLE
                PAGE to scroll horizontally on every tab (not just one
                screen), since this header is shared/sticky across all of
                them. Tightened at base, restored to the original sizing at
                sm (640px+) where there's room to spare. */}
            <h1 className="text-base font-semibold text-emerald sm:text-lg">TopRate</h1>
            <nav className="flex rounded-md border border-line bg-bg p-0.5">
              {/* Internal tab id stays 'trackers' (URL state, App.tsx's own
                  switchTab/useUrlState) - only the visible label changed
                  (real user feedback, 2026-09-17: it was Race that got
                  renamed to Summary, corrected - Trackers is Summary, Race
                  keeps its own name) so existing deep links/bookmarks with
                  tab=trackers keep working. */}
              <button
                type="button"
                onClick={() => switchTab('trackers')}
                className={
                  'rounded px-1.5 py-1 text-xs font-medium transition-colors sm:px-2.5 sm:text-sm ' +
                  (topTab === 'trackers' ? 'bg-panel text-ink shadow-[var(--shadow-1)]' : 'text-ink-mute hover:text-ink')
                }
              >
                Summary
              </button>
              <button
                type="button"
                onClick={() => switchTab('race')}
                className={
                  'rounded px-1.5 py-1 text-xs font-medium transition-colors sm:px-2.5 sm:text-sm ' +
                  (topTab === 'race' ? 'bg-panel text-ink shadow-[var(--shadow-1)]' : 'text-ink-mute hover:text-ink')
                }
              >
                Race
              </button>
              <button
                type="button"
                onClick={() => switchTab('review')}
                className={
                  'rounded px-1.5 py-1 text-xs font-medium transition-colors sm:px-2.5 sm:text-sm ' +
                  (topTab === 'review' ? 'bg-panel text-ink shadow-[var(--shadow-1)]' : 'text-ink-mute hover:text-ink')
                }
              >
                Review
              </button>
            </nav>
          </div>
          <div className="flex items-center gap-2 sm:gap-3">
            {state.status === 'ready' && (
              <FreshnessDot
                level={freshnessLevel(state.data.runIso, new Date(now))}
                runIso={state.data.runIso}
                now={now}
              />
            )}
            <button
              type="button"
              onClick={() => setSearchOpen(true)}
              aria-label="Search horse, jockey, or trainer"
              title="Search (/)"
              className="flex h-7 w-7 items-center justify-center rounded-md text-ink-mute transition-colors hover:bg-bg hover:text-ink"
            >
              🔍
            </button>
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
                  title="Custom fair price sharpness active"
                />
              )}
            </div>
          </div>
        </div>
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
        {state.status === 'ready' && topTab === 'trackers' && (
          <TrackersTab races={state.data.races} onSelectRace={goToRace} />
        )}
        {state.status === 'ready' && topTab === 'race' &&
          (urlState.raceId ? (
            <RaceDetail
              key={urlState.raceId}
              race={state.data.races.find((r) => r.raceId === urlState.raceId)!}
              allRaces={state.data.races}
              priceBeta={betaOverride ?? state.data.priceBeta}
              deltas={deltas}
              bases={bases}
              scratched={scratched}
              setDelta={setDelta}
              setBase={setBase}
              setScratched={setScratched}
              initialRunId={urlState.runId}
              onBack={() => pushUrlState({ date: urlState.date, raceId: null, runId: null })}
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

      {searchOpen && state.status === 'ready' && (
        <GlobalSearch
          races={state.data.races}
          onSelectRunner={(raceId, date, runId) => goToRace(raceId, date, runId)}
          onClose={() => setSearchOpen(false)}
        />
      )}
    </div>
  )
}

export default App
