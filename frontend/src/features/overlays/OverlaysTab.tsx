import { useMemo, useState } from 'react'
import type { Race, Runner } from '../../types/domain'
import { Pill } from '../../components/Pill'
import { StatTile } from '../../components/StatTile'
import { EmptyState } from '../../components/EmptyState'
import { computeEffectiveRace } from '../../lib/raceModel'
import { todayIso, bushMeetingKeys, meetingKey } from '../../lib/meetings'
import { useExcludedTracks } from '../../lib/excludedTracks'
import { formatTimeOfDay } from '../../lib/countdown'
import { fmtPrice, fmtWpr } from '../../lib/format'

interface OverlaysTabProps {
  races: Race[]
  priceBeta: number | null
  deltas: Record<string, number>
  bases: Record<string, number>
  scratched: Set<string>
  initialDate?: string | null
  // Shared with the Race tab (App.tsx lifts this via useShowBushMeetings) so
  // the "hide bush meetings" preference is one setting, not a different
  // default on every tab.
  showBush: boolean
  onShowBushChange: (value: boolean) => void
  onSelectRace: (raceId: string, date: string, runId?: string) => void
}

const DATE_QUICK_BUTTONS: { label: string; offset: number }[] = [
  { label: 'Yesterday', offset: -1 },
  { label: 'Today', offset: 0 },
  { label: 'Tomorrow', offset: 1 },
]

// Shared shape for both the overlays list and the backed-in-underlays list -
// same columns, same click-through, same result badge. `flag` is which
// price-drift badge (if any) this row should show; the two lists never mix
// flags (an overlay can only ever show 'drift', a backed-in row always shows
// 'backedIn'), but keeping it on one row type lets both lists share a single
// table/card renderer instead of two near-identical copies.
interface DisplayRow {
  race: Race
  runner: Runner
  wpr: number
  effectivePrice: number
  gapFromTop: number
  marketPrice: number
  flag: 'drift' | 'backedIn' | null
}

interface GroupedDisplayRow extends DisplayRow {
  isNewRace: boolean
  groupIndex: number
}

// Proportional staking: size the stake so a win returns a fixed TOTAL
// (stake + profit) of returnUnits, not a fixed profit - e.g. at $50/unit,
// backing a $5 chance to return 4 units ($200) means staking $40 (0.8
// units), since stake * price = returnUnits. User-corrected Sep 2026 (an
// earlier version sized stake as returnUnits/(price-1), which fixes the
// PROFIT at 1 unit instead - a materially different relative weighting
// across price tiers, not just a scale factor).
function stakeFor(price: number, returnUnits = 4): number {
  return returnUnits / price
}

// Precomputed once per list, not per-row during render: which rows start a
// new race group (so the venue/race/time label only prints once, with a
// heavier top border), and which alternating group they belong to (for the
// zebra tint) - a race that produced 2+ rows used to repeat its own
// venue/time text on every row, which was the main reason this list was hard
// to scan.
function groupByRace(rows: DisplayRow[]): GroupedDisplayRow[] {
  let groupIndex = -1
  let prevRaceId: string | null = null
  return rows.map((o) => {
    const isNewRace = o.race.raceId !== prevRaceId
    if (isNewRace) groupIndex += 1
    prevRaceId = o.race.raceId
    return { ...o, isNewRace, groupIndex }
  })
}

// Warning badge (an overlay that was a material underlay at today's open
// price and has since drifted into overlay territory) or informational
// badge (the mirror case - a material overlay at open that's since been
// backed into an underlay) - see raceModel.ts's driftedToOverlay/
// firmedToUnderlay for the full reasoning. Flag, not exclusion (user
// decision, Sep 2026).
function FlagBadge({ flag }: { flag: 'drift' | 'backedIn' | null }) {
  if (flag === 'drift') {
    return (
      <span
        title="Was a material underlay at today's open price, has since drifted into an overlay - a possible bad sign (market may know something the model doesn't), not a validated buy signal"
        className="flex-none rounded bg-amber-bg px-1 text-[10px] font-semibold text-amber"
      >
        ⚠ drift
      </span>
    )
  }
  if (flag === 'backedIn') {
    return (
      <span
        title="Was a material overlay at today's open price, has since been backed into an underlay - the market has grown more confident in this runner than it started (and than our own price)"
        className="flex-none rounded bg-emerald-bg px-1 text-[10px] font-semibold text-emerald-deep"
      >
        ▲ backed in
      </span>
    )
  }
  return null
}

// Shared between the desktop table and the mobile card list below, so the
// two never drift apart on what a result looks like.
function ResultBadge({ runner }: { runner: Runner }) {
  if (runner.finishPosition == null) return <span className="text-xs text-ink-faint">—</span>
  return (
    <span
      className={`inline-flex min-w-[2.25rem] items-center justify-center rounded-full px-1.5 py-0.5 font-mono text-xs font-semibold ${
        runner.won ? 'bg-emerald-bg text-emerald-deep' : 'bg-rose-bg text-rose'
      }`}
    >
      {runner.won ? 'WON' : runner.finishPosition}
    </span>
  )
}

// Mobile card list + desktop table for one set of rows (overlays, or
// backed-in underlays) - identical layout either way, only the badge and the
// row data differ.
function PriceMoveList({
  rows,
  onSelectRace,
}: {
  rows: GroupedDisplayRow[]
  onSelectRace: (raceId: string, date: string, runId?: string) => void
}) {
  const byRace = useMemo(() => {
    const map = new Map<string, GroupedDisplayRow[]>()
    for (const o of rows) {
      const key = o.race.raceId
      if (!map.has(key)) map.set(key, [])
      map.get(key)!.push(o)
    }
    return [...map.values()]
  }, [rows])

  return (
    <>
      {/* Mobile: cards, not a horizontally-scrolled table - this table has no
          sticky column to keep the horse/race in view while scrolling
          sideways (unlike RaceDetail's runner grid), so squeezing it into a
          phone width just hides WPR $/Fixed $/Result off-screen with no
          obvious way to reach them. One card per race, its rows stacked
          inside, keeps every value visible without scrolling. */}
      <div className="flex flex-col gap-2 sm:hidden">
        {byRace.map((group) => (
          <div key={group[0].race.raceId} className="rounded-lg border border-line bg-panel p-3">
            <div className="mb-2 flex items-baseline justify-between">
              <span className="font-medium text-ink">
                {group[0].race.venue} R{group[0].race.raceNumber}
              </span>
              <span className="font-mono text-xs text-ink-faint">{formatTimeOfDay(group[0].race.startTime)}</span>
            </div>
            <div className="flex flex-col gap-2">
              {group.map((o) => (
                <div
                  key={o.runner.runId}
                  role="button"
                  tabIndex={0}
                  onClick={() => onSelectRace(o.race.raceId, o.race.date, o.runner.runId)}
                  onKeyDown={(e) => {
                    if (e.key === 'Enter' || e.key === ' ') {
                      e.preventDefault()
                      onSelectRace(o.race.raceId, o.race.date, o.runner.runId)
                    }
                  }}
                  className="flex cursor-pointer items-center gap-2 rounded-md border border-line-soft px-2.5 py-2 hover:bg-emerald-bg/30"
                >
                  {o.runner.silkUrl ? (
                    <img src={o.runner.silkUrl} alt="" className="h-8 w-8 flex-none rounded-sm object-contain" />
                  ) : (
                    <span className="h-8 w-8 flex-none" />
                  )}
                  <div className="min-w-0 flex-1">
                    <div className="flex items-center gap-1">
                      <span className="truncate font-medium text-ink">
                        {o.runner.tabNumber}. {o.runner.horse}
                      </span>
                      <FlagBadge flag={o.flag} />
                    </div>
                    <div className="font-mono text-xs text-ink-mute">
                      <span className="font-semibold text-emerald-deep">{fmtWpr(o.wpr)}</span> &middot; Gap{' '}
                      {o.gapFromTop.toFixed(1)} &middot; WPR {fmtPrice(o.effectivePrice)} &middot; Fixed{' '}
                      {fmtPrice(o.marketPrice)}
                    </div>
                  </div>
                  <ResultBadge runner={o.runner} />
                </div>
              ))}
            </div>
          </div>
        ))}
      </div>

      <div className="hidden overflow-x-auto rounded-lg border border-line bg-panel sm:block">
        <table className="w-full min-w-[560px] border-collapse text-sm">
          <thead>
            <tr className="border-b border-line bg-bg text-xs font-medium text-ink-mute">
              <th className="px-3 py-2 text-left">Race</th>
              <th className="w-8 px-1 py-2" />
              <th className="px-3 py-2 text-left">Horse</th>
              <th className="px-3 py-2 text-right">WPR</th>
              <th className="px-3 py-2 text-right" title="WPR points behind the field's top-rated runner">
                Gap
              </th>
              <th className="px-3 py-2 text-right">WPR $</th>
              <th className="px-3 py-2 text-right">Fixed $</th>
              <th className="px-3 py-2 text-center">Result</th>
            </tr>
          </thead>
          <tbody>
            {rows.map((o) => {
              const zebra = o.groupIndex % 2 === 1 ? 'bg-bg/60' : ''
              return (
                <tr
                  key={o.runner.runId}
                  role="button"
                  tabIndex={0}
                  onClick={() => onSelectRace(o.race.raceId, o.race.date, o.runner.runId)}
                  onKeyDown={(e) => {
                    if (e.key === 'Enter' || e.key === ' ') {
                      e.preventDefault()
                      onSelectRace(o.race.raceId, o.race.date, o.runner.runId)
                    }
                  }}
                  className={`cursor-pointer border-b border-line-soft last:border-b-0 hover:bg-emerald-bg/30 ${zebra} ${
                    o.isNewRace && o.groupIndex > 0 ? 'border-t-2 border-t-line' : ''
                  }`}
                >
                  <td className="whitespace-nowrap px-3 py-2 align-top text-ink-mute">
                    {o.isNewRace && (
                      <>
                        <div className="font-mono text-xs text-ink-faint">{formatTimeOfDay(o.race.startTime)}</div>
                        <div className="font-medium text-ink">
                          {o.race.venue} R{o.race.raceNumber}
                        </div>
                      </>
                    )}
                  </td>
                  <td className="px-1 py-2">
                    {o.runner.silkUrl ? (
                      <img src={o.runner.silkUrl} alt="" className="h-8 w-8 flex-none rounded-sm object-contain" />
                    ) : null}
                  </td>
                  <td className="px-3 py-2 font-medium text-ink">
                    <div className="flex items-center gap-1">
                      <span>
                        {o.runner.tabNumber}. {o.runner.horse}
                      </span>
                      <FlagBadge flag={o.flag} />
                    </div>
                  </td>
                  <td className="px-3 py-2 text-right font-mono font-semibold text-emerald-deep">{fmtWpr(o.wpr)}</td>
                  <td className="px-3 py-2 text-right font-mono text-ink-mute">{o.gapFromTop.toFixed(1)}</td>
                  <td className="px-3 py-2 text-right font-mono text-ink-mute">{fmtPrice(o.effectivePrice)}</td>
                  <td className="px-3 py-2 text-right font-mono text-ink-mute">{fmtPrice(o.marketPrice)}</td>
                  <td className="px-3 py-2 text-center">
                    <ResultBadge runner={o.runner} />
                  </td>
                </tr>
              )
            })}
          </tbody>
        </table>
      </div>
    </>
  )
}

// All overlays on one date, across every race - not filtered to a strategy
// threshold beyond the same caps the race table's own overlay highlight uses
// (raceModel.ts's OVERLAY_MAX_GAP_FROM_TOP / MIN_TOP_RATED_WPR), so this tab
// and a highlighted race table always agree on what counts as an overlay.
// Also surfaces the mirror case (backed-in underlays, raceModel.ts's
// firmedToUnderlay) behind a filter toggle, since those runners are
// structurally excluded from the overlay list itself (by definition they're
// no longer priced longer than our fair value) but are still useful context
// - e.g. spotting a horse you were considering that the market has since
// backed in hard.
export function OverlaysTab({
  races,
  priceBeta,
  deltas,
  bases,
  scratched,
  initialDate,
  showBush,
  onShowBushChange,
  onSelectRace,
}: OverlaysTabProps) {
  const [date, setDate] = useState(() => initialDate ?? todayIso())
  const [showBackedIn, setShowBackedIn] = useState(false)
  const { excludedTracks, toggleTrack } = useExcludedTracks()

  const dateRaces = useMemo(() => races.filter((r) => r.date === date), [races, date])

  // Same bush/picnic threshold and default (hidden) as the Race tab's own
  // meetings grid - a shared preference, not a separate default per tab.
  const bushCount = useMemo(() => bushMeetingKeys(dateRaces).size, [dateRaces])

  const dayRacesBeforeTrackFilter = useMemo(() => {
    const withoutBush = showBush
      ? dateRaces
      : (() => {
          const bushKeys = bushMeetingKeys(dateRaces)
          return dateRaces.filter((r) => !bushKeys.has(meetingKey(r)))
        })()
    return [...withoutBush].sort((a, b) => new Date(a.startTime).getTime() - new Date(b.startTime).getTime())
  }, [dateRaces, showBush])

  // Venues actually on offer today (post-bush-filter) - what the track-filter
  // pills below list, in first-race order rather than alphabetically so the
  // row roughly matches the day's running order.
  const venuesToday = useMemo(() => {
    const seen = new Set<string>()
    const ordered: string[] = []
    for (const r of dayRacesBeforeTrackFilter) {
      if (!seen.has(r.venue)) {
        seen.add(r.venue)
        ordered.push(r.venue)
      }
    }
    return ordered
  }, [dayRacesBeforeTrackFilter])

  const dayRaces = useMemo(
    () => dayRacesBeforeTrackFilter.filter((r) => !excludedTracks.has(r.venue)),
    [dayRacesBeforeTrackFilter, excludedTracks],
  )

  // One pass over the day's races builds both lists together (they use the
  // same per-race computeEffectiveRace call) rather than looping the day
  // twice.
  const { overlays, backedIn } = useMemo(() => {
    const overlayRows: DisplayRow[] = []
    const backedInRows: DisplayRow[] = []
    for (const race of dayRaces) {
      // Same data-scratch + manual-scratch merge RaceDetail does - a real
      // scratch still needs to exclude that runner from the softmax here,
      // not just visually.
      const effectiveScratched = new Set(scratched)
      for (const r of race.runners) {
        if (r.dataScratched) effectiveScratched.add(r.runId)
      }
      const effectiveByRunId = computeEffectiveRace(race.runners, deltas, bases, priceBeta, effectiveScratched)
      for (const runner of race.runners) {
        const eff = effectiveByRunId[runner.runId]
        if (!eff || eff.effectiveProjectedWpr == null || eff.effectivePrice == null || eff.gapFromTop == null) continue
        const marketPrice = runner.fixedWinPrice ?? runner.startingPrice
        if (marketPrice == null) continue
        const base = {
          race,
          runner,
          wpr: eff.effectiveProjectedWpr,
          effectivePrice: eff.effectivePrice,
          gapFromTop: eff.gapFromTop,
          marketPrice,
        }
        if (eff.isOverlay) overlayRows.push({ ...base, flag: eff.driftedToOverlay ? 'drift' : null })
        if (eff.firmedToUnderlay) backedInRows.push({ ...base, flag: 'backedIn' })
      }
    }
    return { overlays: overlayRows, backedIn: backedInRows }
  }, [dayRaces, deltas, bases, priceBeta, scratched])

  const groupedOverlays = useMemo(() => groupByRace(overlays), [overlays])
  const groupedBackedIn = useMemo(() => groupByRace(backedIn), [backedIn])

  const resulted = overlays.filter((o) => o.runner.finishPosition != null)
  const summary = useMemo(() => {
    if (resulted.length === 0) return null
    let staked = 0
    let profit = 0
    let wins = 0
    for (const o of resulted) {
      const stake = stakeFor(o.marketPrice)
      staked += stake
      if (o.runner.won) {
        profit += stake * (o.marketPrice - 1)
        wins += 1
      } else {
        profit -= stake
      }
    }
    return { n: resulted.length, strike: wins / resulted.length, roi: staked > 0 ? profit / staked : 0, profit }
  }, [resulted])

  return (
    <div className="flex flex-col gap-4">
      <div className="flex flex-wrap items-center gap-2">
        {DATE_QUICK_BUTTONS.map((btn) => {
          const btnDate = todayIso(btn.offset)
          return (
            <Pill key={btn.label} active={date === btnDate} onClick={() => setDate(btnDate)}>
              {btn.label}
            </Pill>
          )
        })}
        <input
          type="date"
          value={date}
          onChange={(e) => setDate(e.target.value)}
          className="rounded-md border border-line bg-panel px-2 py-1 text-sm font-mono"
        />
        {bushCount > 0 && (
          <Pill active={showBush} onClick={() => onShowBushChange(!showBush)}>
            {showBush ? 'Hide' : 'Show'} {bushCount} bush meeting{bushCount === 1 ? '' : 's'}
          </Pill>
        )}
        {backedIn.length > 0 && (
          <Pill active={showBackedIn} onClick={() => setShowBackedIn((v) => !v)}>
            {showBackedIn ? 'Hide' : 'Show'} {backedIn.length} backed-in underlay{backedIn.length === 1 ? '' : 's'}
          </Pill>
        )}
      </div>

      {venuesToday.length > 0 && (
        <div className="flex flex-wrap items-center gap-1.5">
          <span className="text-xs font-medium text-ink-mute">Tracks:</span>
          {venuesToday.map((venue) => {
            const excluded = excludedTracks.has(venue)
            return (
              <Pill key={venue} active={!excluded} onClick={() => toggleTrack(venue)}>
                {excluded ? `${venue} ✕` : venue}
              </Pill>
            )
          })}
        </div>
      )}

      <div className="grid grid-cols-2 gap-2 sm:grid-cols-4">
        <StatTile label="Overlays" value={String(overlays.length)} sublabel={date} />
        <StatTile label="Resulted" value={summary ? String(summary.n) : '—'} sublabel="so far today" />
        <StatTile
          label="Strike"
          value={summary ? `${(summary.strike * 100).toFixed(1)}%` : '—'}
          tone={summary ? 'default' : 'muted'}
        />
        <StatTile
          label="ROI"
          value={summary ? `${summary.roi >= 0 ? '+' : ''}${(summary.roi * 100).toFixed(1)}%` : '—'}
          sublabel={summary ? `${summary.profit >= 0 ? '+' : ''}${summary.profit.toFixed(2)}u staked proportionally` : undefined}
          tone={summary ? (summary.roi >= 0 ? 'positive' : 'negative') : 'muted'}
        />
      </div>

      {overlays.length === 0 ? (
        <EmptyState message={`No overlays on ${date} matching the current filters.`} />
      ) : (
        <PriceMoveList rows={groupedOverlays} onSelectRace={onSelectRace} />
      )}

      {showBackedIn && backedIn.length > 0 && (
        <div className="flex flex-col gap-2">
          <div className="flex items-center gap-1.5 text-xs font-medium text-ink-mute">
            <span>▲ Backed-in underlays</span>
            <span className="text-ink-faint">
              (were a material overlay at today's open, since backed in below our fair price - informational, not a
              buy signal)
            </span>
          </div>
          <PriceMoveList rows={groupedBackedIn} onSelectRace={onSelectRace} />
        </div>
      )}
    </div>
  )
}
