import { useEffect, useMemo, useState } from 'react'
import { Pill } from '../../components/Pill'
import { StatTile } from '../../components/StatTile'
import { EmptyState } from '../../components/EmptyState'
import { fmtPrice, fmtWpr } from '../../lib/format'
import { todayIso } from '../../lib/meetings'
import { formatTimeOfDay } from '../../lib/countdown'

// Reads the two forward-tracking logs speedmap_jockey_tracker.py writes
// (repo-root CSVs, same static-file-next-to-index.html pattern
// lib/meetingFormHistory.ts already uses for horse_history/*.json) -
// read-only, client-side. Two rules found via session-long backtesting
// against toprate_data.json (Sep 2026), NOT wired into any model, pick, or
// projection logic:
//   - High volume: favoured/neutral speed map, jockey win% (90d) >= 14,
//     within 6 WPR of the race's top-projected runner, $3+ price.
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

function ResultBadge({ row }: { row: TrackerRow }) {
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
  return (
    <div
      role="button"
      tabIndex={0}
      onClick={() => onSelectRace(row.raceId, row.date, row.runId)}
      onKeyDown={(e) => {
        if (e.key === 'Enter' || e.key === ' ') {
          e.preventDefault()
          onSelectRace(row.raceId, row.date, row.runId)
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

const DATE_QUICK_BUTTONS: { label: string; offset: number }[] = [
  { label: 'Yesterday', offset: -1 },
  { label: 'Today', offset: 0 },
]

function TrackerView({
  rows,
  description,
  onSelectRace,
}: {
  rows: TrackerRow[]
  description: string
  onSelectRace: (raceId: string, date: string, runId?: string) => void
}) {
  const summary = useMemo(() => summarize(rows), [rows])
  const [date, setDate] = useState(() => todayIso())
  const [showAll, setShowAll] = useState(false)

  // Every distinct date actually present in the log - lets "back to prior
  // days" reach further than yesterday once the daily job has been running
  // a while, without the quick buttons growing unbounded.
  const availableDates = useMemo(() => [...new Set(rows.map((r) => r.date))].sort().reverse(), [rows])

  const displayed = useMemo(() => {
    const filtered = showAll ? rows : rows.filter((r) => r.date === date)
    // Race start time, not race number - the picks span every meeting
    // running that day, and each venue numbers its own races independently,
    // so sorting by race_no would interleave venues out of actual running
    // order (real user feedback, 2026-09-16: "should be in order of race
    // time").
    return [...filtered].sort((a, b) => {
      if (a.date !== b.date) return a.date < b.date ? 1 : -1
      return a.startTime < b.startTime ? -1 : a.startTime > b.startTime ? 1 : 0
    })
  }, [rows, date, showAll])

  return (
    <div className="flex flex-col gap-3">
      <p className="text-xs text-ink-faint">{description}</p>

      <div className="grid grid-cols-2 gap-2 sm:grid-cols-5">
        <StatTile label="Picks logged" value={String(rows.length)} sublabel="all time" />
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
          max={availableDates[0] ?? todayIso()}
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
    </div>
  )
}

interface TrackersTabProps {
  onSelectRace: (raceId: string, date: string, runId?: string) => void
}

export function TrackersTab({ onSelectRace }: TrackersTabProps) {
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
          description="Favoured or neutral speed map, jockey win% (90d) >= 14, within 6 WPR of the race's top-projected runner, $3+ price. No rating-agreement requirement - higher volume, weaker edge."
          onSelectRace={onSelectRace}
        />
      )}
      {!loading && which === 'low' && low.rows && (
        <TrackerView
          rows={low.rows}
          description="Same rule, plus the runner must also be #1 in-race by both TopRate's own rating and the external form-factor score. Lower volume, stronger edge in backtesting."
          onSelectRace={onSelectRace}
        />
      )}
    </div>
  )
}
