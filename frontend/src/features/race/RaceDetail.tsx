import { Fragment, useMemo, useState } from 'react'
import type { Race } from '../../types/domain'
import { Pill } from '../../components/Pill'
import { useTableDensity } from '../../lib/density'
import { useShowScratched } from '../../lib/scratchedVisibility'
import { computeEffectiveRace, computeCompositeGaps, OVERLAY_MAX_GAP_FROM_TOP, COMPOSITE_MAX_GAP_FROM_TOP } from '../../lib/raceModel'
import { sortRunners, DEFAULT_DIRECTION, type SortKey, type SortDirection } from '../../lib/sorting'
import { bushMeetingKeys, meetingKey } from '../../lib/meetings'
import { evaluateTrackerQualifiers } from '../../lib/trackerRules'
import { RunnerRow } from './RunnerRow'
import { RunnerDetailModal } from './RunnerDetailModal'
import { SpeedMap } from './SpeedMap'
import { SpeedMapGrid } from './SpeedMapGrid'
import { formatCountdown } from '../../lib/countdown'
import { raceStatus, STATUS_PILL_TONE } from '../../lib/raceStatus'

interface RaceDetailProps {
  race: Race
  allRaces: Race[]
  priceBeta: number | null
  deltas: Record<string, number>
  bases: Record<string, number>
  scratched: Set<string>
  setDelta: (runId: string, value: number | null) => void
  setBase: (runId: string, value: number | null) => void
  setScratched: (runId: string, value: boolean) => void
  // A runner to pre-select on mount (search, Review-tab cross-linking).
  // Only read once - App.tsx keys RaceDetail on race.raceId, so a fresh
  // deep link always remounts rather than needing a sync effect here.
  initialRunId?: string | null
  onBack: () => void
  onSelectRace: (raceId: string, date: string) => void
}

// RTS ("runs this spell" - the spellPosition label: FU/2U/3U/.../nU) sits
// right after Horse and is always visible (mobile included, not just
// desktop's Full density) - user request, Aug 2026. Bar(rier) dropped
// entirely per the same request. Order here drives both header rows'
// column order below and RunnerRow's matching grid-template order - keep
// all three in sync if this ever changes again.
const COLUMN_LABELS: { key: SortKey; label: string; showCompact?: boolean }[] = [
  { key: 'tab', label: '#' },
  { key: 'horse', label: 'Horse', showCompact: true },
  { key: 'daysSince', label: 'RTS', showCompact: true },
  { key: 'baseWpr', label: 'Base' },
  { key: 'adjustment', label: 'Adj' },
  // speed_map ADJ_TERM, demeaned against this race (2026-09-19, real user
  // request: "add a column for speed map adj, with green and red colour")
  // - the same number SpeedMapGrid's own tile tint is built from (see
  // raceModel.ts's speedMapDemeanedByRunId). Desktop-only, same as Base/
  // Adj immediately to its left - not added to either mobile density's
  // grid-cols/MOBILE_COLUMN_LABELS below, per this file's own long history
  // of mobile-column overflow bugs; still reachable via the mobile sort
  // dropdown like Base/Adj already are.
  { key: 'speedMapAdj', label: 'SM Adj' },
  // Combo: shown on both mobile densities too (2026-09-19, real user
  // request: "sort by combo by default... on mobile show combo column,
  // hide TR" - see MOBILE_COLUMN_LABELS_FULL/_COMPACT below, which now
  // show Combo in TR's old slot). Initially shipped desktop-only; that
  // was a deliberate scope-limiting choice at the time (this codebase's
  // long, hard-won history of mobile grid-cols overflow bugs, see
  // CLAUDE.md), superseded by this explicit request rather than a bug.
  // Moved ahead of Proj, and given Proj's own bold/emerald styling
  // (2026-09-19, direct follow-up: "combo should be the bold number, not
  // proj... have combo to the left of proj") - it's the headline figure
  // now; Proj demoted to the plain style below it in RunnerRow.tsx.
  { key: 'compositeScore', label: 'Combo' },
  { key: 'projectedWpr', label: 'Proj', showCompact: true },
  { key: 'toprateRating', label: 'TopRate' },
  { key: 'formFactor', label: 'Form' },
  { key: 'jockeyWinPct', label: 'Jky Win%' },
  { key: 'fixedPrice', label: 'Fixed $' },
  { key: 'finish', label: 'FP' },
]

// Full mobile density (Compact's own subset is below) - Base/Adj stay
// desktop-only in EITHER mobile density (real user feedback, 2026-09-16:
// "remove base from mobile race summary, re-add adj to desktop" - Adj had
// briefly been dropped from every view, now it's back but desktop-only,
// same as Base always was on mobile). Order here must match RunnerRow's
// own full-mobile grid-cols exactly, same as COLUMN_LABELS does for the
// desktop template above. Adjustment is also still shown in the runner
// detail modal's own breakdown regardless of any of this.
// Real words here (TopRate/Form/Jky Win%) don't fit these columns' own
// necessarily-narrow tracks even at full width, let alone truncated - CSS
// `truncate` was rendering them as unreadable "To...''/"Fo...''/"Jky...''
// fragments (real user feedback, 2026-09-17: "columns aren't readable").
// These mobile headers get their OWN short, whole labels instead of
// truncating the desktop ones - TR/Fm/J% read cleanly at any width these
// columns can realistically have, where a truncated "TopRate" never will.
// TR replaced with Combo (2026-09-19, real user request: "on mobile show
// combo column, hide TR") - RunnerRow.tsx's matching mobile grid-cols
// widened Combo's own track to Proj's width (not TR's narrower one,
// since Combo shows a decimal WPR-scale value like Proj rather than a
// bare integer), recovered from Horse's own floor per this file's
// established pattern - see that file's own comment for the exact
// numbers.
const MOBILE_COLUMN_LABELS_FULL: { key: SortKey; label: string }[] = [
  { key: 'horse', label: 'Horse' },
  // SM Adj (2026-09-19, direct follow-up: "not seeing it" on mobile - see
  // RunnerRow.tsx's SM Adj cell for why it's shown on Full but not
  // Compact). Short label, matches Fm/J%'s own brevity in this cramped a
  // track (30px).
  { key: 'speedMapAdj', label: 'SM' },
  { key: 'compositeScore', label: 'Cb' },
  { key: 'projectedWpr', label: 'Proj' },
  { key: 'formFactor', label: 'Fm' },
  { key: 'jockeyWinPct', label: 'J%' },
  { key: 'fixedPrice', label: 'Fixed $' },
  { key: 'finish', label: 'FP' },
]

// Compact mobile (the default density, see useTableDensity) drops
// Form/Jockey Win% too (on top of Base/Adj, dropped from both densities
// above) so the whole row fits within a phone's own width without needing
// ANY horizontal scroll, verified down to 360px (real user feedback,
// 2026-09-16: "trim mobile columns so it fits without scrolling") - must
// match RunnerRow's own compact mobile grid-cols exactly (desktop is
// unaffected either way - it always shows every column, see
// COLUMN_LABELS/sm:grid-cols above).
const MOBILE_COLUMN_LABELS_COMPACT: { key: SortKey; label: string }[] = [
  { key: 'horse', label: 'Horse' },
  { key: 'compositeScore', label: 'Cb' },
  { key: 'projectedWpr', label: 'Proj' },
  { key: 'fixedPrice', label: 'Fixed $' },
  { key: 'finish', label: 'FP' },
]

export function RaceDetail({
  race,
  allRaces,
  priceBeta,
  deltas,
  bases,
  scratched,
  setDelta,
  setBase,
  setScratched,
  initialRunId,
  onBack,
  onSelectRace,
}: RaceDetailProps) {
  const { compact, setCompact } = useTableDensity()
  const { showScratched, setShowScratched } = useShowScratched()
  // Combo default (2026-09-19, real user request: "sort by combo by
  // default") - was projectedWpr; see raceModel.ts's compositeScore() own
  // comment for the backtest that motivated Combo existing at all.
  const [sortKey, setSortKey] = useState<SortKey>('compositeScore')
  const [sortDir, setSortDir] = useState<SortDirection>(DEFAULT_DIRECTION.compositeScore)
  const [selectedRunId, setSelectedRunId] = useState<string | null>(initialRunId ?? null)
  const [speedMapView, setSpeedMapView] = useState<'bar' | 'grid'>('grid')

  // scratched (prop) is the manual, this-device-only toggle set - merge in
  // each runner's real data-driven scratch (see toprate_price_refresh.py)
  // so a late scratch the pipeline actually detected takes effect here too,
  // not just ones a person happened to click. Toggling in the UI still only
  // ever writes to the manual set (setScratched) - a data-confirmed scratch
  // isn't something a click should be able to undo.
  const effectiveScratched = useMemo(() => {
    const merged = new Set(scratched)
    for (const r of race.runners) {
      if (r.dataScratched) merged.add(r.runId)
    }
    return merged
  }, [race.runners, scratched])

  const effectiveByRunId = useMemo(
    () => computeEffectiveRace(race.runners, deltas, bases, priceBeta, effectiveScratched),
    [race.runners, deltas, bases, priceBeta, effectiveScratched],
  )

  // Composite score's own "gap from top" - independent of effectiveByRunId's
  // WPR-based gapFromTop (see computeCompositeGaps' own comment for why: that
  // one is calibrated for price/overlay math, this one has a different
  // scale entirely).
  const compositeGapByRunId = useMemo(
    () => computeCompositeGaps(race.runners, effectiveByRunId, effectiveScratched),
    [race.runners, effectiveByRunId, effectiveScratched],
  )

  // Live tracker-rule flag (see lib/trackerRules.ts) - evaluated fresh
  // against this race's CURRENT data on every render, not read from the
  // slower-to-update CSV log the Trackers tab reads. Real user feedback,
  // 2026-09-16: "race summary should flag if a horse fits the criteria for
  // a tracker bet" - this is that flag, shown inline on RunnerRow.
  const trackerQualifiers = useMemo(
    () => evaluateTrackerQualifiers(race, bushMeetingKeys(allRaces).has(meetingKey(race))),
    [race, allRaces],
  )
  // effectiveScratched still carries the manual set's OTHER-race run_ids
  // (it's a global set with this race's data-scratches merged in) - count
  // only this race's runners against it, not the set's raw size.
  const scratchedInRace = race.runners.filter((r) => effectiveScratched.has(r.runId)).length

  // Drives the "Interim Result" status badge below - true as soon as ANY
  // runner has a finish position, whether that's a handful of TAB results
  // trickling in mid-meeting or the whole field once race.provisional's
  // "done via TAB only" case applies.
  const hasAnyResult = race.runners.some((r) => r.finishPosition !== null)

  // Scratched runners sort to the bottom regardless of the chosen sort key -
  // they're out of the race, cluttering the top of a Proj-sorted list with
  // a horse that can no longer win is worse than losing strict sort order
  // for the (rare, temporary) scratched few.
  const sortedRunners = useMemo(() => {
    const sorted = sortRunners(race.runners, sortKey, sortDir, effectiveByRunId, race.date)
    const active = sorted.filter((r) => !effectiveScratched.has(r.runId))
    if (!showScratched) return active
    const scratchedRunners = sorted.filter((r) => effectiveScratched.has(r.runId))
    return [...active, ...scratchedRunners]
  }, [race.runners, race.date, sortKey, sortDir, effectiveByRunId, effectiveScratched, showScratched])
  const selectedIndex = sortedRunners.findIndex((r) => r.runId === selectedRunId)
  const selectedRunner = selectedIndex >= 0 ? sortedRunners[selectedIndex] : null

  const meetingRaces = useMemo(
    () =>
      allRaces
        .filter((r) => r.venue === race.venue && r.date === race.date)
        .sort((a, b) => a.raceNumber - b.raceNumber),
    [allRaces, race.venue, race.date],
  )

  function onSort(key: SortKey) {
    if (key === sortKey) {
      setSortDir((d) => (d === 'asc' ? 'desc' : 'asc'))
    } else {
      setSortKey(key)
      setSortDir(DEFAULT_DIRECTION[key])
    }
  }

  function step(delta: number) {
    if (selectedIndex < 0) return
    const next = (selectedIndex + delta + sortedRunners.length) % sortedRunners.length
    setSelectedRunId(sortedRunners[next].runId)
  }

  return (
    <div className="flex flex-col gap-3">
      <button type="button" onClick={onBack} className="w-fit text-sm text-emerald hover:underline">
        &larr; Back to meetings
      </button>

      <div className="flex flex-wrap gap-1.5">
        {meetingRaces.map((r) => (
          <Pill
            key={r.raceId}
            active={r.raceId === race.raceId}
            tone={STATUS_PILL_TONE[raceStatus(r, Date.now())]}
            onClick={() => onSelectRace(r.raceId, r.date)}
          >
            R{r.raceNumber}
          </Pill>
        ))}
      </div>

      <div className="rounded-lg border border-line bg-panel p-3 shadow-[var(--shadow-1)]">
        <div className="flex flex-wrap items-baseline justify-between gap-2">
          <h2 className="text-lg font-semibold text-ink">
            {race.venue} R{race.raceNumber} &middot; {race.raceName}
          </h2>
          {race.allResulted && !race.provisional ? (
            <span className="rounded-full border border-emerald-line bg-emerald-bg px-2 py-0.5 font-mono text-xs font-semibold text-emerald-deep">
              Resulted
            </span>
          ) : hasAnyResult ? (
            <span
              className="rounded-full border border-amber-line bg-amber-bg px-2 py-0.5 font-mono text-xs font-semibold text-amber"
              title="TAB's fast provisional feed - toprate.au's confirmed result lands once the whole meeting finishes"
            >
              Interim Result
            </span>
          ) : (
            <span className="font-mono text-sm text-ink-mute">{formatCountdown(race.startTime)}</span>
          )}
        </div>
        <div className="mt-1 flex flex-wrap gap-x-4 gap-y-1 text-xs text-ink-mute">
          <span>{race.distance}m</span>
          <span>{race.going}</span>
          <span>
            {/* race.fieldSize is the ACTIVE (non-scratched) count the model
                uses internally (see toprate_daily.py's _active_field_size) -
                using it here too used to read as "8 runners (4 scratched)"
                on a 12-horse field, implying 8 was the total. runners.length
                is always the true declared field size regardless of scratch
                source (data-driven or this device's manual toggle). */}
            {race.runners.length} runners
            {scratchedInRace > 0 && (
              <span className="text-rose"> ({scratchedInRace} scratched)</span>
            )}
          </span>
          {race.hasFirstStarter && <span className="text-amber">First starter in field</span>}
        </div>
      </div>

      <div className="flex flex-wrap items-center justify-between gap-2">
        <div className="flex flex-wrap gap-1">
          <Pill active={compact} onClick={() => setCompact(true)}>Compact</Pill>
          <Pill active={!compact} onClick={() => setCompact(false)}>Full</Pill>
          {scratchedInRace > 0 && (
            <Pill active={!showScratched} onClick={() => setShowScratched(!showScratched)}>
              {showScratched ? 'Hide scratched' : 'Show scratched'}
            </Pill>
          )}
        </div>
        {/* The full column-header row (with its own sort buttons) is desktop-
            only (hidden below sm - see the grid below), so mobile needs its
            own way to change sort - otherwise it's stuck on whatever was
            last set, with no visible way to change it. */}
        <div className="flex items-center gap-1.5 sm:hidden">
          <select
            value={sortKey}
            onChange={(e) => onSort(e.target.value as SortKey)}
            aria-label="Sort by"
            className="rounded-md border border-line bg-panel px-2 py-1 text-xs"
          >
            {COLUMN_LABELS.map((col) => (
              <option key={col.key} value={col.key}>
                Sort: {col.label}
              </option>
            ))}
          </select>
          <button
            type="button"
            onClick={() => setSortDir((d) => (d === 'asc' ? 'desc' : 'asc'))}
            aria-label={sortDir === 'asc' ? 'Sort ascending' : 'Sort descending'}
            className="flex h-6 w-6 items-center justify-center rounded-md border border-line text-ink-mute transition-colors hover:bg-bg hover:text-ink"
          >
            {sortDir === 'asc' ? '↑' : '↓'}
          </button>
        </div>
      </div>

      <div className="overflow-x-auto rounded-lg border border-line bg-panel">
        {/* Mobile header: matches RunnerRow's mobile grid-cols exactly for
            the current density - Base/Adj never show on mobile in either
            density (desktop-only). Compact additionally drops Form/Jockey
            Win% (and narrows Horse) to fit with zero horizontal scroll;
            Full keeps Form/Jockey Win% too, with every column narrowed just
            enough that the whole row fits with zero scroll at a typical
            (~393px) phone width and only a few px at the narrowest
            (~360px) ones, same as Compact - see RunnerRow's own comment on
            this exact grid-cols string for the Playwright measurements
            behind these numbers, including why the Horse column is
            `minmax(Npx, 1fr)` rather than a bare px value (2026-09-17: a
            bare-px row pinned to exactly its own content width left a
            growing blank gap on any phone wider than that content - a
            wide but still sub-`sm` device, not just a tablet - instead of
            filling the card; 1fr lets the Horse column absorb that space
            instead). Compact also had its own long-standing Fixed $
            overflow (44px, the same too-narrow size Full started at) -
            see RunnerRow's own comment for how that was found (a 2-digit
            TopRate value rendering as a single digit, its neighbour eaten
            by Fixed $'s own overflowing content) and fixed to the same
            76px. Full's own header labels are short mobile-only ones
            (TR/Fm/J%, see MOBILE_COLUMN_LABELS_FULL above), not the
            desktop words truncated - those never actually fit these
            tracks either, `truncate` just made them illegible fragments
            (real user feedback, 2026-09-17: "columns aren't readable").
            Free (no width cost, the data cells were already sized to
            content) - the leftover ~16px of "acceptable" scroll at 360px
            from the previous fix was recovered from Horse's own floor
            (68->52) instead, since checking it turned up a real defect:
            scrolled all the way to reveal FP, Proj's own value was
            partially covered by the sticky name cell.
            Still not enough (real user feedback, 2026-09-17, on a wide
            phone where Horse had plenty of room via 1fr): TopRate/Form/
            Jky% sit right next to Fixed $, which is 76px wide to survive
            a rare "$101.00" - three ~26-28px columns at a 2px gap read as
            cramped next to it regardless of Horse's own slack. Checked
            alignment first (exact per-column pixel match at 430/480/540px)
            to confirm this was a density complaint, not a bug, then
            widened TopRate/Form/Jky%/their shared gap and recovered from
            Horse's floor again (52->39) rather than dropping Form from
            mobile Full - a real user choice via AskUserQuestion. The
            desktop header further down covers every column but is hidden
            below sm since it's laid out differently there. */}
        <div
          className={`grid min-w-full border-b border-line bg-bg px-2 py-1.5 text-xs font-medium text-ink-mute sm:hidden ${
            // Full gained an SM Adj track (2026-09-19, direct follow-up:
            // "not seeing it" on mobile) - must match RunnerRow's own
            // grid-cols exactly, see that file's comment for the numbers.
            compact
              ? 'gap-x-1 grid-cols-[40px_minmax(80px,1fr)_40px_40px_76px_20px]'
              : 'gap-x-[3px] grid-cols-[40px_minmax(38px,1fr)_30px_36px_36px_29px_31px_76px_20px]'
          }`}
        >
          <span className="sticky left-0 z-10 -ml-2 bg-bg pl-2" />
          {(compact ? MOBILE_COLUMN_LABELS_COMPACT : MOBILE_COLUMN_LABELS_FULL).map((col, i) => (
            <button
              key={col.key}
              type="button"
              onClick={() => onSort(col.key)}
              className={`block min-w-0 truncate transition-colors hover:text-ink ${
                // left-12 (48px) to match RunnerRow's silk cell's true
                // rendered width - see that file's own comment. min-w-0 +
                // truncate: Full mobile's narrowed columns (e.g. "TopRate"
                // in a 28px track) would otherwise overflow past their own
                // grid track and visually bleed into the next column - a
                // grid item's default min-width is its content size, not
                // its track, so without this the label just overflows
                // rather than shrinking (real user feedback, 2026-09-17).
                i === 0 ? 'sticky left-12 z-10 bg-bg text-left' : 'text-right'
              } ${sortKey === col.key ? 'text-emerald-deep' : ''}`}
            >
              {col.label}
              {sortKey === col.key && (sortDir === 'asc' ? ' ↑' : ' ↓')}
            </button>
          ))}
        </div>
        <div className="hidden min-w-full grid-cols-[44px_36px_1fr_56px_56px_60px_60px_60px_56px_52px_44px_56px_68px_52px] gap-x-2 border-b border-line bg-bg px-2 py-1.5 text-xs font-medium text-ink-mute sm:grid">
          <span />
          {COLUMN_LABELS.map((col) => {
            const align = col.key === 'horse' || col.key === 'tab' ? 'text-left' : 'text-center'
            return (
              <button
                key={col.key}
                type="button"
                onClick={() => onSort(col.key)}
                className={`${align} transition-colors hover:text-ink ${sortKey === col.key ? 'text-emerald-deep' : ''}`}
              >
                {col.label}
                {sortKey === col.key && (sortDir === 'asc' ? ' ↑' : ' ↓')}
              </button>
            )
          })}
        </div>
        {sortedRunners.map((runner, i) => {
          // Gap-from-top marker line: only meaningful when the list is
          // actually grouped by rating (Proj or Combo sort) - otherwise
          // "within the gap threshold of the top pick" runners aren't
          // necessarily contiguous, and the line would land at a fairly
          // arbitrary-looking spot. Detected as a transition (this row
          // qualifies, the next doesn't) so it still works under either
          // sort direction, not just descending. Combo (Sep 2026) reads
          // its own gap/threshold (compositeGapByRunId/
          // COMPOSITE_MAX_GAP_FROM_TOP) rather than the WPR-based ones -
          // see computeCompositeGaps' own comment for why they're kept
          // entirely separate. Reads the live constants from raceModel.ts
          // (not a second hardcoded copy) since this line exists
          // specifically to show that cutoff.
          const usingComposite = sortKey === 'compositeScore'
          const gap = usingComposite ? compositeGapByRunId[runner.runId] : effectiveByRunId[runner.runId]?.gapFromTop
          const nextGapRunId = i + 1 < sortedRunners.length ? sortedRunners[i + 1].runId : undefined
          const nextGap =
            nextGapRunId == null
              ? undefined
              : usingComposite
                ? compositeGapByRunId[nextGapRunId]
                : effectiveByRunId[nextGapRunId]?.gapFromTop
          const gapThreshold = usingComposite ? COMPOSITE_MAX_GAP_FROM_TOP : OVERLAY_MAX_GAP_FROM_TOP
          const showBoundary = (sortKey === 'projectedWpr' || usingComposite) && gap != null
          const showGapLine =
            showBoundary &&
            gap <= gapThreshold &&
            (nextGap == null || nextGap === undefined || nextGap > gapThreshold)
          return (
            <Fragment key={runner.runId}>
              <RunnerRow
                runner={runner}
                raceDate={race.date}
                compact={compact}
                selected={runner.runId === selectedRunId}
                effective={effectiveByRunId[runner.runId]}
                trackerQualifier={trackerQualifiers.get(runner.runId)}
                onClick={() => setSelectedRunId(runner.runId === selectedRunId ? null : runner.runId)}
              />
              {showGapLine && (
                <div className="flex w-full items-center gap-2 bg-indigo-bg px-2 py-0.5">
                  <span className="h-[2px] flex-1 bg-indigo" />
                  <span className="flex-none font-mono text-[10px] font-semibold uppercase tracking-wide text-indigo">
                    {gapThreshold} {usingComposite ? 'pts (Combo)' : 'WPR'} from top rated
                  </span>
                  <span className="h-[2px] flex-1 bg-indigo" />
                </div>
              )}
            </Fragment>
          )
        })}
      </div>

      {/* Scratched runners are excluded, not just visually - the speed map
          plots who's actually going to run, not the original field. */}
      <div className="flex items-center justify-end gap-1.5">
        <Pill active={speedMapView === 'grid'} onClick={() => setSpeedMapView('grid')}>
          Grid
        </Pill>
        <Pill active={speedMapView === 'bar'} onClick={() => setSpeedMapView('bar')}>
          Bar
        </Pill>
      </div>
      {speedMapView === 'grid' ? (
        <SpeedMapGrid race={race} runners={race.runners.filter((r) => !effectiveScratched.has(r.runId))} />
      ) : (
        <SpeedMap race={race} runners={race.runners.filter((r) => !effectiveScratched.has(r.runId))} />
      )}

      {selectedRunner && (
        <RunnerDetailModal
          runner={selectedRunner}
          race={race}
          effective={effectiveByRunId[selectedRunner.runId]}
          deltaValue={deltas[selectedRunner.runId] ?? null}
          baseValue={bases[selectedRunner.runId] ?? null}
          onSetDelta={(v) => setDelta(selectedRunner.runId, v)}
          onSetBase={(v) => setBase(selectedRunner.runId, v)}
          onToggleScratch={() => setScratched(selectedRunner.runId, !scratched.has(selectedRunner.runId))}
          onClose={() => setSelectedRunId(null)}
          onPrev={() => step(-1)}
          onNext={() => step(1)}
        />
      )}
    </div>
  )
}
