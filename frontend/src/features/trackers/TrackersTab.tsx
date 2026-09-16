import { useEffect, useMemo, useState } from 'react'
import { Pill } from '../../components/Pill'
import { StatTile } from '../../components/StatTile'
import { EmptyState } from '../../components/EmptyState'
import { fmtPrice } from '../../lib/format'

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
  tab: string
  horse: string
  tag: string
  gapWpr: number | null
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
    tab: r[idx('tab')] ?? '',
    horse: r[idx('horse')] ?? '',
    tag: r[idx('tag')] ?? '',
    gapWpr: numOrNull(r[idx('gap_wpr')]),
    jw: numOrNull(r[idx('jw')]),
    priceAtPick: numOrNull(r[idx('price_at_pick')]),
    resulted: r[idx('resulted')] === 'True',
    finishPosition: numOrNull(r[idx('finish_position')]),
    won: r[idx('won')] === '1',
    priceFinal: numOrNull(r[idx('price_final')]),
  }))
}

// Proportional staking: same "size the stake to return a fixed 4 units on a
// win" convention OverlaysTab.tsx already uses - kept in sync with that
// file's own stakeFor() rather than shared, since each feature owns its own
// copy of this one-liner (see that file's own comment for the full
// reasoning on why proportional-to-price, not flat).
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
    return <span className="text-xs text-ink-faint">pending</span>
  }
  return (
    <span
      className={`inline-flex min-w-[2.25rem] items-center justify-center rounded-full px-1.5 py-0.5 font-mono text-xs font-semibold ${
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

function TrackerView({ rows, description }: { rows: TrackerRow[]; description: string }) {
  const summary = useMemo(() => summarize(rows), [rows])
  const sorted = useMemo(
    () => [...rows].sort((a, b) => (a.date < b.date ? 1 : a.date > b.date ? -1 : a.raceNo < b.raceNo ? 1 : -1)),
    [rows],
  )

  return (
    <div className="flex flex-col gap-3">
      <p className="text-xs text-ink-faint">{description}</p>

      <div className="grid grid-cols-2 gap-2 sm:grid-cols-5">
        <StatTile label="Picks logged" value={String(rows.length)} />
        <StatTile label="Resulted" value={summary ? String(summary.n) : '—'} sublabel="so far" />
        <StatTile label="Win %" value={summary ? `${summary.winPct.toFixed(1)}%` : '—'} tone={summary ? 'default' : 'muted'} />
        <StatTile label="Place %" value={summary ? `${summary.placePct.toFixed(1)}%` : '—'} tone={summary ? 'default' : 'muted'} />
        <StatTile
          label="ROI (flat / prop)"
          value={summary ? `${summary.flatRoiPct >= 0 ? '+' : ''}${summary.flatRoiPct.toFixed(1)}% / ${summary.propRoiPct >= 0 ? '+' : ''}${summary.propRoiPct.toFixed(1)}%` : '—'}
          tone={summary ? (summary.propRoiPct >= 0 ? 'positive' : 'negative') : 'muted'}
        />
      </div>

      {rows.length === 0 ? (
        <EmptyState message="No picks logged yet - the daily pipeline captures new ones each run." />
      ) : (
        <div className="overflow-x-auto rounded-lg border border-line bg-panel">
          <table className="w-full min-w-[640px] border-collapse text-sm">
            <thead>
              <tr className="border-b border-line bg-bg text-xs font-medium text-ink-mute">
                <th className="px-3 py-2 text-left">Date</th>
                <th className="px-3 py-2 text-left">Race</th>
                <th className="px-3 py-2 text-left">Horse</th>
                <th className="px-3 py-2 text-left">Tag</th>
                <th className="px-3 py-2 text-right" title="Jockey win% (trailing 90 days)">
                  Jockey
                </th>
                <th className="px-3 py-2 text-right">Price</th>
                <th className="px-3 py-2 text-center">Result</th>
              </tr>
            </thead>
            <tbody>
              {sorted.map((r) => (
                <tr key={r.runId} className="border-b border-line-soft last:border-b-0">
                  <td className="whitespace-nowrap px-3 py-2 font-mono text-xs text-ink-faint">{r.date}</td>
                  <td className="whitespace-nowrap px-3 py-2 text-ink-mute">
                    {r.venue} R{r.raceNo}
                  </td>
                  <td className="px-3 py-2 font-medium text-ink">
                    {r.tab}. {r.horse}
                  </td>
                  <td className="px-3 py-2">
                    <span className={`rounded px-1.5 py-0.5 text-[10px] font-semibold uppercase ${TAG_TONE[r.tag] ?? ''}`}>
                      {r.tag}
                    </span>
                  </td>
                  <td className="px-3 py-2 text-right font-mono text-ink-mute">{r.jw != null ? r.jw.toFixed(1) : '—'}</td>
                  <td className="px-3 py-2 text-right font-mono text-ink-mute">
                    {fmtPrice(r.resulted ? r.priceFinal : r.priceAtPick)}
                  </td>
                  <td className="px-3 py-2 text-center">
                    <ResultBadge row={r} />
                  </td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>
      )}
    </div>
  )
}

export function TrackersTab() {
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
        />
      )}
      {!loading && which === 'low' && low.rows && (
        <TrackerView
          rows={low.rows}
          description="Same rule, plus the runner must also be #1 in-race by both TopRate's own rating and the external form-factor score. Lower volume, stronger edge in backtesting."
        />
      )}
    </div>
  )
}
