import { useEffect, useMemo, useState } from 'react'
import type { Race } from '../../types/domain'
import { Pill } from '../../components/Pill'
import { StatTile } from '../../components/StatTile'
import { EmptyState } from '../../components/EmptyState'
import { fmtPrice, fmtWpr } from '../../lib/format'
import { todayIso } from '../../lib/meetings'
import { formatTimeOfDay } from '../../lib/countdown'
import {
  liveTrackerCandidates,
  pendingWatchCandidates,
  skippedTrackerGroups,
  type TrackerCandidateRow,
  type SkippedGroup,
} from '../../lib/trackerRules'

// Reads the two forward-tracking logs speedmap_jockey_tracker.py writes
// (repo-root CSVs, same static-file-next-to-index.html pattern
// lib/meetingFormHistory.ts already uses for horse_history/*.json) -
// read-only, client-side. Two rules found via session-long backtesting
// against toprate_data.json (Sep 2026), NOT wired into any model, pick, or
// projection logic:
//   - High volume: favoured/neutral speed map, jockey win% (90d) >= 14,
//     within 4 WPR of the race's top-projected runner, $3+ price. A
//     multi-selection race still fires (on all of them) if every one is
//     priced above $6.
//   - Low volume: same, plus the runner must also be #1 in-race by both
//     TopRate's own rating AND the external form-factor score.
// Each row is captured BEFORE the result is known (see the tracker
// script's own docstring) and never re-evaluated, so this tab shows real
// forward performance, not a backtest re-run each time the page loads.
interface TrackerRow {
  runId: string
  raceId: string
  date: string
  venue: string
  raceNo: string
  startTime: string
  tab: string
  horse: string
  silkUrl: string
  tag: string
  wprPrediction: number | null
  gapWpr: number | null
  toprateRating: number | null
  formFactor: number | null
  jw: number | null
  priceAtPick: number | null
  resulted: boolean
  finishPosition: number | null
  won: boolean
  priceFinal: number | null
  // True for a runner that currently qualifies (evaluated live against
  // today's data - see lib/trackerRules.ts) but hasn't been captured into
  // this tracker's CSV log yet - the daily pipeline only runs a handful of
  // fixed times a day, so a runner that starts qualifying in between two
  // runs would otherwise be invisible here until it's too late to bet
  // (real user feedback, 2026-09-16: "tracker does not showing upcoming
  // bets"). Never persisted - recomputed fresh on every page load, and
  // disappears once the real capture (or a condition change) overtakes it.
  live?: boolean
  // Set for a pendingWatchCandidates() row - contested or under $3 RIGHT
  // NOW, but the race hasn't run yet, so it's not a settled skip (real
  // user request, 2026-09-17). Mutually exclusive with `live` (a runner
  // is either currently qualifying or currently not, never both) and with
  // `resulted` (pendingWatchCandidates() never returns one for a resulted
  // race - see that function's own comment).
  watchReason?: 'contested' | 'underPrice'
}

function candidateToRow(c: TrackerCandidateRow): TrackerRow {
  return {
    runId: c.runId,
    raceId: c.raceId,
    date: c.date,
    venue: c.venue,
    raceNo: String(c.raceNo),
    startTime: c.startTime,
    tab: String(c.tab),
    horse: c.horse,
    silkUrl: c.silkUrl,
    tag: c.tag,
    wprPrediction: c.wprPrediction,
    gapWpr: c.gapWpr,
    toprateRating: c.toprateRating,
    formFactor: c.formFactor,
    jw: c.jw,
    priceAtPick: c.priceAtPick,
    resulted: c.resulted,
    finishPosition: c.finishPosition,
    won: c.won,
    priceFinal: c.priceFinal,
    live: c.watchReason == null,
    watchReason: c.watchReason,
  }
}

// Minimal RFC4180 parser (quoted fields, "" escaping) - Python's csv module
// quotes any field containing a comma/quote/newline (QUOTE_MINIMAL), and a
// horse name occasionally does contain a comma, so a naive split(',') would
// silently misalign columns on exactly those rows.
function parseCsv(text: string): string[][] {
  const rows: string[][] = []
  let row: string[] = []
  let field = ''
  let inQuotes = false
  for (let i = 0; i < text.length; i++) {
    const c = text[i]
    if (inQuotes) {
      if (c === '"') {
        if (text[i + 1] === '"') {
          field += '"'
          i++
        } else {
          inQuotes = false
        }
      } else {
        field += c
      }
    } else if (c === '"') {
      inQuotes = true
    } else if (c === ',') {
      row.push(field)
      field = ''
    } else if (c === '\n' || c === '\r') {
      if (c === '\r' && text[i + 1] === '\n') i++
      row.push(field)
      rows.push(row)
      row = []
      field = ''
    } else {
      field += c
    }
  }
  if (field.length > 0 || row.length > 0) {
    row.push(field)
    rows.push(row)
  }
  return rows.filter((r) => r.length > 1 || r[0] !== '')
}

function numOrNull(v: string | undefined): number | null {
  if (v == null || v === '') return null
  const n = Number(v)
  return Number.isNaN(n) ? null : n
}

function parseTrackerCsv(text: string): TrackerRow[] {
  const rows = parseCsv(text)
  if (rows.length === 0) return []
  const header = rows[0]
  const idx = (name: string) => header.indexOf(name)
  return rows.slice(1).map((r) => ({
    runId: r[idx('run_id')] ?? '',
    raceId: r[idx('race_id')] ?? '',
    date: r[idx('date')] ?? '',
    venue: r[idx('venue')] ?? '',
    raceNo: r[idx('race_no')] ?? '',
    startTime: r[idx('start_time')] ?? '',
    tab: r[idx('tab')] ?? '',
    horse: r[idx('horse')] ?? '',
    silkUrl: r[idx('silk_url')] ?? '',
    tag: r[idx('tag')] ?? '',
    wprPrediction: numOrNull(r[idx('wpr_prediction')]),
    gapWpr: numOrNull(r[idx('gap_wpr')]),
    toprateRating: numOrNull(r[idx('toprate_rating')]),
    formFactor: numOrNull(r[idx('form_factor')]),
    jw: numOrNull(r[idx('jw')]),
    priceAtPick: numOrNull(r[idx('price_at_pick')]),
    resulted: r[idx('resulted')] === 'True',
    finishPosition: numOrNull(r[idx('finish_position')]),
    won: r[idx('won')] === '1',
    priceFinal: numOrNull(r[idx('price_final')]),
  }))
}

// Proportional staking: same "size the stake to return a fixed 4 units on a
// win" convention OverlaysTab.tsx used to (before it was replaced by this
// tab) - kept here rather than shared, since a feature owning its own copy
// of this one-liner is the established pattern (see that file's own history
// for the full reasoning on why proportional-to-price, not flat).
function stakeFor(price: number, returnUnits = 4): number {
  return returnUnits / price
}

interface Summary {
  n: number
  winPct: number
  placePct: number
  flatRoiPct: number
  propRoiPct: number
}

function summarize(rows: TrackerRow[]): Summary | null {
  const resulted = rows.filter((r) => r.resulted && r.priceFinal != null)
  if (resulted.length === 0) return null
  let wins = 0
  let places = 0
  let flatStaked = 0
  let flatReturned = 0
  let propStaked = 0
  let propReturned = 0
  for (const r of resulted) {
    const price = r.priceFinal as number
    if (r.won) wins += 1
    if (r.finishPosition != null && r.finishPosition <= 3) places += 1
    flatStaked += 1
    flatReturned += r.won ? price : 0
    const stake = stakeFor(price)
    propStaked += stake
    propReturned += r.won ? stake * price : 0
  }
  return {
    n: resulted.length,
    winPct: (100 * wins) / resulted.length,
    placePct: (100 * places) / resulted.length,
    flatRoiPct: flatStaked > 0 ? (100 * (flatReturned - flatStaked)) / flatStaked : 0,
    propRoiPct: propStaked > 0 ? (100 * (propReturned - propStaked)) / propStaked : 0,
  }
}

function ResultBadge({ row }: { row: { resulted: boolean; won: boolean; finishPosition: number | null } }) {
  if (!row.resulted) {
    return <span className="flex-none text-xs text-ink-faint">pending</span>
  }
  return (
    <span
      className={`inline-flex flex-none min-w-[2.25rem] items-center justify-center rounded-full px-1.5 py-0.5 font-mono text-xs font-semibold ${
        row.won ? 'bg-emerald-bg text-emerald-deep' : 'bg-rose-bg text-rose'
      }`}
    >
      {row.won ? 'WON' : row.finishPosition ?? '—'}
    </span>
  )
}

const TAG_TONE: Record<string, string> = {
  favoured: 'bg-emerald-bg text-emerald-deep',
  neutral: 'bg-bg text-ink-mute',
}

function useTrackerCsv(url: string) {
  const [rows, setRows] = useState<TrackerRow[] | null>(null)
  const [error, setError] = useState(false)
  useEffect(() => {
    let cancelled = false
    fetch(url, { cache: 'no-cache' })
      .then((res) => (res.ok ? res.text() : Promise.reject(new Error(String(res.status)))))
      .then((text) => {
        if (!cancelled) setRows(parseTrackerCsv(text))
      })
      .catch(() => {
        if (!cancelled) setError(true)
      })
    return () => {
      cancelled = true
    }
  }, [url])
  return { rows, error }
}

// One stat, label above value, used inside a pick card's small info grid -
// deliberately not StatTile (that component reads as a page-level headline
// stat; these are dense per-row facts, closer to RunnerDetailModal's own
// small labelled-figure convention).
function Fact({ label, value }: { label: string; value: string }) {
  return (
    <div className="flex flex-col">
      <span className="text-[9px] uppercase tracking-wide text-ink-faint">{label}</span>
      <span className="font-mono text-xs text-ink-mute">{value}</span>
    </div>
  )
}

// One pick, as a self-contained card - every field the user asked to see
// (silk, WPR prediction + gap to top rated, TopRate rating, form-factor
// rating, jockey win%, price, result) fits without any horizontal
// scrolling at any viewport width, unlike the table this replaced (real
// user feedback, 2026-09-16: a table forced a horizontal scroll to see the
// Result column on a phone). The whole card is clickable, same as a
// RunnerRow, and opens the runner detail modal directly (not just the race
// list) via onSelectRace's runId param - RaceDetail already opens
// RunnerDetailModal whenever its initialRunId prop is set.
function PickCard({
  row,
  onSelectRace,
}: {
  row: TrackerRow
  onSelectRace: (raceId: string, date: string, runId?: string) => void
}) {
  // Race summary page, not the horse's own detail modal - deliberately
  // omits runId (real user feedback, 2026-09-16: passing it opened
  // RunnerDetailModal directly via RaceDetail's initialRunId prop, which
  // is one horse zoomed in, not the race overview the user actually
  // wanted from this list).
  return (
    <div
      role="button"
      tabIndex={0}
      onClick={() => onSelectRace(row.raceId, row.date)}
      onKeyDown={(e) => {
        if (e.key === 'Enter' || e.key === ' ') {
          e.preventDefault()
          onSelectRace(row.raceId, row.date)
        }
      }}
      className="flex cursor-pointer flex-col gap-2 rounded-lg border border-line bg-panel p-3 hover:bg-emerald-bg/30"
    >
      <div className="flex items-center gap-2">
        {row.silkUrl ? (
          <img src={row.silkUrl} alt="" className="h-9 w-9 flex-none rounded-sm object-contain" />
        ) : (
          <span className="h-9 w-9 flex-none rounded-sm bg-bg" />
        )}
        <div className="min-w-0 flex-1">
          <div className="flex items-baseline justify-between gap-2">
            <span className="truncate font-medium text-ink">
              {row.tab}. {row.horse}
            </span>
            <ResultBadge row={row} />
          </div>
          <div className="text-xs text-ink-faint">
            {row.venue} R{row.raceNo}
            {row.startTime ? ` · ${formatTimeOfDay(row.startTime)}` : ''}
          </div>
        </div>
      </div>
      <div className="flex flex-wrap items-end gap-x-4 gap-y-1.5">
        <span className={`rounded px-1.5 py-0.5 text-[10px] font-semibold uppercase ${TAG_TONE[row.tag] ?? ''}`}>
          {row.tag}
        </span>
        {row.live && (
          <span
            title="Currently qualifies against live data, but hasn't been captured by the daily pipeline yet - could still change before that happens"
            className="rounded bg-amber-bg px-1.5 py-0.5 text-[10px] font-semibold uppercase text-amber"
          >
            Live
          </span>
        )}
        {row.watchReason && (
          <span
            title={
              row.watchReason === 'contested'
                ? "Meets the tactical criteria but 2+ runners do, so it's not a solo pick right now - the race hasn't run yet, so a scratch could still clear it before the jump"
                : "Meets the tactical criteria as the lone qualifier, but its price is currently under $3 - the race hasn't run yet, so this could still firm up before the jump"
            }
            className="rounded border border-line px-1.5 py-0.5 text-[10px] font-semibold uppercase text-ink-mute"
          >
            Watching · {row.watchReason === 'contested' ? 'Contested' : 'Under $3'}
          </span>
        )}
        <Fact label="WPR proj" value={row.wprPrediction != null ? fmtWpr(row.wprPrediction) : '—'} />
        <Fact label="Gap to top" value={row.gapWpr != null ? row.gapWpr.toFixed(1) : '—'} />
        <Fact label="TopRate" value={row.toprateRating != null ? row.toprateRating.toFixed(1) : '—'} />
        <Fact label="Form factor" value={row.formFactor != null ? row.formFactor.toFixed(0) : '—'} />
        <Fact label="Jockey" value={row.jw != null ? `${row.jw.toFixed(1)}%` : '—'} />
        <Fact label="Price" value={fmtPrice(row.resulted ? row.priceFinal : row.priceAtPick)} />
      </div>
    </div>
  )
}

// One race where a tracker didn't fire despite meeting the tactical
// criteria - either contested (2+ runners qualify, so solo-only fails) or
// a lone qualifier priced under $3 - so the reason is visible rather than
// the race just silently not appearing anywhere (real user feedback,
// 2026-09-16: "for those races with more than 1 horse that fits the
// criteria, these should be flagged as such... also show if there is a
// solo pick under $3"). Same open-the-race-summary click behaviour as
// PickCard.
function SkippedCard({
  group,
  onSelectRace,
}: {
  group: SkippedGroup
  onSelectRace: (raceId: string, date: string, runId?: string) => void
}) {
  return (
    <div
      role="button"
      tabIndex={0}
      onClick={() => onSelectRace(group.raceId, group.date)}
      onKeyDown={(e) => {
        if (e.key === 'Enter' || e.key === ' ') {
          e.preventDefault()
          onSelectRace(group.raceId, group.date)
        }
      }}
      className="flex cursor-pointer flex-col gap-2 rounded-lg border border-line bg-panel p-3 hover:bg-bg"
    >
      <div className="flex items-baseline justify-between gap-2">
        <span className="font-medium text-ink">
          {group.venue} R{group.raceNo}
        </span>
        <div className="flex items-center gap-2">
          <span
            className="rounded bg-bg px-1.5 py-0.5 text-[10px] font-semibold uppercase text-ink-mute"
            title={
              group.reason === 'contested'
                ? '2+ runners meet the criteria - solo-only fails'
                : 'The only runner meeting the criteria was priced under $3'
            }
          >
            {group.reason === 'contested' ? 'Contested' : 'Under $3'}
          </span>
          <span className="text-xs text-ink-faint">{group.startTime ? formatTimeOfDay(group.startTime) : ''}</span>
        </div>
      </div>
      <div className="flex flex-col gap-1.5">
        {group.runners.map((r) => (
          <div key={r.runId} className="flex flex-wrap items-center gap-x-3 gap-y-1 text-xs">
            <span className="min-w-0 flex-1 truncate font-medium text-ink">
              {r.tab}. {r.horse}
            </span>
            <span className={`flex-none rounded px-1.5 py-0.5 text-[10px] font-semibold uppercase ${TAG_TONE[r.tag] ?? ''}`}>
              {r.tag}
            </span>
            <span className="flex-none font-mono text-ink-mute">{r.gapWpr.toFixed(1)} gap</span>
            <span className="flex-none font-mono text-ink-mute">{r.jw.toFixed(1)}% jky</span>
            <span className="flex-none font-mono text-ink-mute">{fmtPrice(r.price)}</span>
            <ResultBadge row={r} />
          </div>
        ))}
      </div>
    </div>
  )
}

const DATE_QUICK_BUTTONS: { label: string; offset: number }[] = [
  { label: 'Yesterday', offset: -1 },
  { label: 'Today', offset: 0 },
  // Races are sometimes pre-fetched days ahead (see daily.yml's days_ahead
  // input) - a live pick can exist for tomorrow before the CSV log has ever
  // run against it, so this needs to be reachable the same way Today is,
  // not just via the raw date picker.
  { label: 'Tomorrow', offset: 1 },
]

function TrackerView({
  rows,
  races,
  trackerKind,
  description,
  onSelectRace,
}: {
  rows: TrackerRow[]
  races: Race[]
  trackerKind: 'high' | 'low'
  description: string
  onSelectRace: (raceId: string, date: string, runId?: string) => void
}) {
  const [date, setDate] = useState(() => todayIso())
  const [showAll, setShowAll] = useState(false)

  // Every distinct date actually present in the log - lets "back to prior
  // days" reach further than yesterday once the daily job has been running
  // a while, without the quick buttons growing unbounded.
  const availableDates = useMemo(() => [...new Set(rows.map((r) => r.date))].sort().reverse(), [rows])

  // The date picker's own max needs to reach as far as whatever race data
  // is actually loaded (sometimes pre-fetched days ahead - see
  // DATE_QUICK_BUTTONS' own comment), not just the latest LOGGED date -
  // otherwise a pre-fetched future day's live-only picks are invisible
  // because the date input itself refuses to go there.
  const maxDate = useMemo(
    () => [...availableDates, todayIso(), ...races.map((r) => r.date)].sort().pop() ?? todayIso(),
    [availableDates, races],
  )

  // Scoped to whatever's currently selected (one date, or every date) -
  // real user feedback (2026-09-16): the summary tiles used to always show
  // all-time totals regardless of the date filter below, which read as
  // "today" or "yesterday" but was actually the whole log.
  const filtered = useMemo(() => (showAll ? rows : rows.filter((r) => r.date === date)), [rows, date, showAll])

  // Every runId this tracker has already logged for the selected date -
  // shared by liveRows and skippedGroups below, both of which re-evaluate
  // the tactical rule live against CURRENT race data (current price,
  // current field of qualifiers) rather than reading it back from the CSV.
  // A runner's live evaluation can flip after it's already fired and been
  // logged (most commonly: its price drifted under $3 after capture,
  // making a now-stale re-evaluation see it as "underPrice" or newly
  // "contested") - real user report, 2026-09-17: Albert Palais showing up
  // as both an actual logged pick AND a "skipped race" the same day.
  const loggedRunIdsToday = useMemo(() => {
    if (showAll || date < todayIso()) return new Set<string>()
    return new Set(rows.filter((r) => r.date === date).map((r) => r.runId))
  }, [rows, date, showAll])

  // Live candidates fill the gap between daily.yml's fixed capture times
  // (see lib/trackerRules.ts's own comment) - only meaningful for a single,
  // not-in-the-past date (showAll already spans every logged date, and a
  // past date's picks are all long since captured), and only added for a
  // runId this tracker hasn't already logged for that date.
  const liveRows = useMemo(() => {
    if (showAll || date < todayIso()) return []
    const candidates = liveTrackerCandidates(races, date)[trackerKind]
    return candidates.filter((c) => !loggedRunIdsToday.has(c.runId)).map(candidateToRow)
  }, [races, date, showAll, trackerKind, loggedRunIdsToday])

  // Contested/under-$3 right now, but the race hasn't run yet - stays in
  // the main list (in race order, alongside real picks) rather than
  // dropping into "Skipped races" below, since price and the field can
  // still move before the jump (real user request, 2026-09-17). Same
  // gating as liveRows - only meaningful for today (or a pre-fetched
  // future day), not showAll or a past date.
  const watchingRows = useMemo(() => {
    if (showAll || date < todayIso()) return []
    const candidates = pendingWatchCandidates(races, date)[trackerKind]
    return candidates.filter((c) => !loggedRunIdsToday.has(c.runId)).map(candidateToRow)
  }, [races, date, showAll, trackerKind, loggedRunIdsToday])

  const combined = useMemo(() => [...filtered, ...liveRows, ...watchingRows], [filtered, liveRows, watchingRows])
  const summary = useMemo(() => summarize(combined), [combined])

  // Races where the tactical criteria were met but the race has ALREADY
  // RESULTED and still no pick fired (contested, or a lone qualifier
  // under $3) - see skippedTrackerGroups()'s own comment for why an
  // upcoming race's contested/under-$3 runners live in watchingRows
  // above instead, not here, until the race actually resolves. Only
  // meaningful for a single selected date (showAll spans the whole log,
  // which has no matching per-day race list to re-derive this from).
  // Still needs loggedRunIdsToday filtered out below though - a runner
  // that DID already fire and get logged is never "skipped", whatever
  // its live re-evaluation says now.
  const skippedGroups = useMemo(() => {
    if (showAll) return []
    const groups = skippedTrackerGroups(races, date)[trackerKind]
    return groups
      .map((g) => ({ ...g, runners: g.runners.filter((r) => !loggedRunIdsToday.has(r.runId)) }))
      .filter((g) => g.runners.length > 0)
  }, [races, date, showAll, trackerKind, loggedRunIdsToday])

  const displayed = useMemo(() => {
    // Race start time, not race number - the picks span every meeting
    // running that day, and each venue numbers its own races independently,
    // so sorting by race_no would interleave venues out of actual running
    // order (real user feedback, 2026-09-16: "should be in order of race
    // time").
    return [...combined].sort((a, b) => {
      if (a.date !== b.date) return a.date < b.date ? 1 : -1
      return a.startTime < b.startTime ? -1 : a.startTime > b.startTime ? 1 : 0
    })
  }, [combined])

  return (
    <div className="flex flex-col gap-3">
      <p className="text-xs text-ink-faint">{description}</p>

      <div className="grid grid-cols-2 gap-2 sm:grid-cols-5">
        <StatTile
          label="Picks logged"
          value={String(filtered.length)}
          sublabel={showAll ? 'all dates' : liveRows.length > 0 ? `${date} · +${liveRows.length} live` : date}
        />
        <StatTile label="Resulted" value={summary ? String(summary.n) : '—'} sublabel="so far" />
        <StatTile label="Win %" value={summary ? `${summary.winPct.toFixed(1)}%` : '—'} tone={summary ? 'default' : 'muted'} />
        <StatTile label="Place %" value={summary ? `${summary.placePct.toFixed(1)}%` : '—'} tone={summary ? 'default' : 'muted'} />
        <StatTile
          label="ROI (flat / prop)"
          value={summary ? `${summary.flatRoiPct >= 0 ? '+' : ''}${summary.flatRoiPct.toFixed(1)}% / ${summary.propRoiPct >= 0 ? '+' : ''}${summary.propRoiPct.toFixed(1)}%` : '—'}
          tone={summary ? (summary.propRoiPct >= 0 ? 'positive' : 'negative') : 'muted'}
        />
      </div>

      <div className="flex flex-wrap items-center gap-2">
        {DATE_QUICK_BUTTONS.map((btn) => {
          const btnDate = todayIso(btn.offset)
          return (
            <Pill
              key={btn.label}
              active={!showAll && date === btnDate}
              onClick={() => {
                setShowAll(false)
                setDate(btnDate)
              }}
            >
              {btn.label}
            </Pill>
          )
        })}
        <input
          type="date"
          value={date}
          max={maxDate}
          onChange={(e) => {
            setShowAll(false)
            setDate(e.target.value)
          }}
          className="rounded-md border border-line bg-panel px-2 py-1 text-sm font-mono"
        />
        <Pill active={showAll} onClick={() => setShowAll((v) => !v)}>
          {showAll ? 'Showing all dates' : 'Show all dates'}
        </Pill>
      </div>

      {displayed.length === 0 ? (
        <EmptyState
          message={
            showAll
              ? 'No picks logged yet - the daily pipeline captures new ones each run.'
              : `No picks logged for ${date}.`
          }
        />
      ) : (
        <div className="flex flex-col gap-2">
          {displayed.map((r) => (
            <PickCard key={r.runId} row={r} onSelectRace={onSelectRace} />
          ))}
        </div>
      )}

      {!showAll && (
        <div className="mt-2 flex flex-col gap-2 border-t border-line-soft pt-3">
          <div>
            <h3 className="text-sm font-semibold text-ink">Skipped races</h3>
            <p className="text-xs text-ink-faint">
              The tactical criteria were met here, but no pick fires - either 2+ runners qualify (contested) or the
              only qualifier was priced under $3. Shown so these aren't just invisible.
            </p>
          </div>
          {skippedGroups.length === 0 ? (
            <EmptyState message={`No skipped races for ${date}.`} />
          ) : (
            <div className="flex flex-col gap-2">
              {skippedGroups.map((g) => (
                <SkippedCard key={`${g.raceId}-${g.reason}`} group={g} onSelectRace={onSelectRace} />
              ))}
            </div>
          )}
        </div>
      )}
    </div>
  )
}

interface TrackersTabProps {
  races: Race[]
  onSelectRace: (raceId: string, date: string, runId?: string) => void
}

export function TrackersTab({ races, onSelectRace }: TrackersTabProps) {
  const [which, setWhich] = useState<'high' | 'low'>('high')
  const high = useTrackerCsv('tracker_high_volume.csv')
  const low = useTrackerCsv('tracker_low_volume.csv')

  const loading = (which === 'high' ? high : low).rows == null && !(which === 'high' ? high : low).error

  return (
    <div className="flex flex-col gap-4">
      <div className="flex flex-wrap items-center gap-2">
        <Pill active={which === 'high'} onClick={() => setWhich('high')}>
          High volume
        </Pill>
        <Pill active={which === 'low'} onClick={() => setWhich('low')}>
          Low volume
        </Pill>
      </div>

      {loading && <EmptyState message="Loading tracker picks..." />}
      {!loading && (which === 'high' ? high.error : low.error) && (
        <EmptyState message="Couldn't load this tracker's log yet." />
      )}
      {!loading && which === 'high' && high.rows && (
        <TrackerView
          rows={high.rows}
          races={races}
          trackerKind="high"
          description="Favoured or neutral speed map, jockey win% (90d) >= 14, within 4 WPR of the race's top-projected runner, and the only runner in its race meeting all of that (solo-only, checked before price) - a second runner meeting everything but priced under $3 still silences this race. That lone qualifier then also needs $3+ price to fire. Exception: if 2+ runners meet the criteria and every one of them is priced above $6, all of them fire instead of staying silent. No rating-agreement requirement - higher volume, weaker edge. A pick tagged Live currently qualifies but hasn't been captured yet."
          onSelectRace={onSelectRace}
        />
      )}
      {!loading && which === 'low' && low.rows && (
        <TrackerView
          rows={low.rows}
          races={races}
          trackerKind="low"
          description="Same base rule, but solo-only means being the only runner #1 in-race by both TopRate's own rating and the external form-factor score - checked independently of the high-volume rule, so a runner can qualify here even on a race where that one stayed silent. Lower volume, stronger edge in backtesting. A pick tagged Live currently qualifies but hasn't been captured yet."
          onSelectRace={onSelectRace}
        />
      )}
    </div>
  )
}
