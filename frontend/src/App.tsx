import { useEffect, useMemo, useState } from 'react'
import { useDashboardData, freshnessLevel } from './hooks/useDashboardData'
import { useNow } from './hooks/useNow'
import { useUrlState } from './routing/useUrlState'
import { useBetaOverride } from './lib/priceBetaOverride'
import { useWprOverrides } from './lib/wprOverrides'
import { useShowBushMeetings } from './lib/bushMeetings'
import { useHiddenVenues } from './lib/hiddenVenues'
import { bushMeetingKeys, distinctVenues, meetingKey, todayIso } from './lib/meetings'
import { MeetingsGrid } from './features/race/MeetingsGrid'
import { ErrorState, EmptyState } from './components/EmptyState'
import { FreshnessDot } from './components/FreshnessDot'
import { NextToJumpTicker } from './components/NextToJumpTicker'
import { SettingsModal } from './components/SettingsModal'
import { HowWprWorksModal } from './components/HowWprWorksModal'
import { GlobalSearch } from './components/GlobalSearch'
import { RaceDetail } from './features/race/RaceDetail'
import { ReviewTab } from './features/review/ReviewTab'

type TopTab = 'race' | 'review'

function readTopTab(): TopTab {
  const t = new URLSearchParams(window.location.search).get('tab')
  return t === 'review' ? t : 'race'
}

// The live poller only reads prices and results for races from 30 minutes ago to 2 hours ahead (tab_results_poller.py), so with none in that
// window the payload does not change and its age says nothing about health. Returns undefined while a race is in the window (the normal
// age colours apply), otherwise the next jump time (null when none is left today).
const POLL_BEHIND_MS = 30 * 60_000
const POLL_AHEAD_MS = 2 * 60 * 60_000
function quietNextJump(races: { startTime: string }[], now: number): Date | null | undefined {
  let next: number | null = null
  for (const r of races) {
    const t = new Date(r.startTime).getTime()
    if (Number.isNaN(t)) continue
    if (t >= now - POLL_BEHIND_MS && t <= now + POLL_AHEAD_MS) return undefined
    if (t > now && (next == null || t < next)) next = t
  }
  return next == null ? null : new Date(next)
}

function App() {
  const { state, retry, refresh, historyPending, pollFailed } = useDashboardData()
  const [refreshing, setRefreshing] = useState(false)
  const now = useNow()
  const { urlState, pushUrlState } = useUrlState()
  const { betaOverride, setBetaOverride } = useBetaOverride()
  const { deltas, bases, scratched, setDelta, setBase, setScratched } = useWprOverrides()
  const { showBush, setShowBush } = useShowBushMeetings()
  const { hiddenVenues, hideVenue, unhideVenue } = useHiddenVenues()
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
      if (e.key !== '/' || e.metaKey || e.ctrlKey || e.altKey) return
      const el = e.target as HTMLElement | null
      const tag = el?.tagName
      if (tag === 'INPUT' || tag === 'TEXTAREA' || tag === 'SELECT' || el?.isContentEditable) return
      // Not while a modal is open or before there is anything to search.
      if (document.querySelector('[role="dialog"]') || state.status !== 'ready') return
      e.preventDefault()
      setSearchOpen(true)
    }
    window.addEventListener('keydown', onKey)
    return () => window.removeEventListener('keydown', onKey)
  }, [state.status])

  function switchTab(tab: TopTab) {
    setTopTabState(tab)
    if (tab === 'review') {
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
    const bushKeys = showBush ? null : bushMeetingKeys(state.data.races)
    return state.data.races.filter((r) => {
      if (hiddenVenues.has(r.venue)) return false
      if (bushKeys && bushKeys.has(meetingKey(r))) return false
      return true
    })
  }, [state, showBush, hiddenVenues])

  // Boot-time deep-link handling: if the URL already names a race (a shared
  // link or a page reload mid-session), that wins over the default meetings
  // view once data loads - matches __initDashboard's "shared link wins"
  // behavior (toprate_html_v3.py L5376-5421).
  useEffect(() => {
    if (state.status !== 'ready') return
    if (!urlState.raceId) return
    const raceExists = state.data.races.some((r) => r.raceId === urlState.raceId)
    // Earlier days arrive in a second file: wait for it before calling the link stale.
    if (!raceExists && !historyPending) {
      // Stale/invalid link - fall back to the meetings view rather than
      // getting stuck on a race that no longer resolves.
      pushUrlState({ date: urlState.date, raceId: null, runId: null })
    }
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [state.status, historyPending])

  const currentRace =
    state.status === 'ready' && urlState.raceId
      ? state.data.races.find((r) => r.raceId === urlState.raceId)
      : undefined

  // Tab title follows the race so bookmarks and shared links are tellable apart.
  useEffect(() => {
    document.title = currentRace
      ? `${currentRace.venue} R${currentRace.raceNumber} - TopRate`
      : topTab === 'review'
        ? 'Review - TopRate'
        : 'TopRate'
  }, [currentRace, topTab])

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
            {/* Visible "TopRate" wordmark removed (26 Sep 2026 user request); kept for screen readers. */}
            <h1 className="sr-only">TopRate</h1>
            <nav className="flex rounded-md border border-line bg-bg p-0.5">
              {/* Summary (trackers) and Bets tabs removed 3 Oct 2026 (user request); old ?tab=trackers / ?tab=bets links open Race. */}
              <button
                type="button"
                onClick={() => switchTab('race')}
                aria-current={topTab === 'race' ? 'page' : undefined}
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
                aria-current={topTab === 'review' ? 'page' : undefined}
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
                quietNext={quietNextJump(state.data.races, now)}
                pollFailed={pollFailed}
              />
            )}
            {state.status === 'ready' && (
              <button
                type="button"
                aria-label="Refresh data"
                title="Refresh data now"
                disabled={refreshing}
                onClick={() => {
                  setRefreshing(true)
                  void refresh().finally(() => setRefreshing(false))
                }}
                className={`rounded p-1 text-ink-mute hover:text-ink focus-visible:outline focus-visible:outline-2 focus-visible:outline-indigo ${refreshing ? 'animate-spin' : ''}`}
              >
                <span aria-hidden="true">↻</span>
              </button>
            )}
            <button
              type="button"
              aria-label="How WPR works and what the columns mean"
              title="How WPR works and what the columns mean"
              onClick={() => setMethodologyOpen(true)}
              className="rounded p-1 text-sm font-semibold text-ink-mute hover:text-ink focus-visible:outline focus-visible:outline-2 focus-visible:outline-indigo"
            >
              ?
            </button>
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
        {state.status === 'ready' && topTab === 'race' && urlState.raceId && !currentRace && historyPending && (
          <EmptyState message="Loading earlier races..." progress={null} />
        )}
        {state.status === 'ready' && topTab === 'race' && !(urlState.raceId && !currentRace && historyPending) &&
          (currentRace ? (
            <RaceDetail
              key={urlState.raceId}
              race={currentRace}
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
              date={urlState.date ?? todayIso()}
              onDateChange={(d) => pushUrlState({ date: d, raceId: null, runId: null })}
              onSelectRace={goToRace}
              showBush={showBush}
              onShowBushChange={setShowBush}
              hiddenVenues={hiddenVenues}
              onHideVenue={hideVenue}
            />
          ))}
      </main>

      {settingsOpen && (
        <SettingsModal
          serverBeta={state.status === 'ready' ? state.data.priceBeta : null}
          betaOverride={betaOverride}
          onSetBetaOverride={setBetaOverride}
          venues={state.status === 'ready' ? distinctVenues(state.data.races) : []}
          hiddenVenues={hiddenVenues}
          onHideVenue={hideVenue}
          onUnhideVenue={unhideVenue}
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
