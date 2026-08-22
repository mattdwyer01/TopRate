import { useMemo, useState } from 'react'
import type { Race } from '../../types/domain'
import {
  collectAccuracyRows,
  computeAccuracyStats,
  computeBreakdown,
  computeOutcomeStats,
  distanceBand,
  type Period,
} from '../../lib/accuracyStats'
import { fmtWpr } from '../../lib/format'
import { StatTile } from '../../components/StatTile'

interface ReviewTabProps {
  races: Race[]
  onSelectRace: (raceId: string, date: string) => void
}

const PERIODS: { value: Period; label: string }[] = [
  { value: '30', label: 'Last 30 days' },
  { value: '90', label: 'Last 90 days' },
  { value: 'all', label: 'All time' },
]

const MAX_DETAIL_ROWS = 100

function fmtSigned(v: number | null, digits = 1): string {
  if (v == null || Number.isNaN(v)) return '-'
  return `${v > 0 ? '+' : ''}${v.toFixed(digits)}`
}

function fmtPct(v: number | null): string {
  if (v == null || Number.isNaN(v)) return '-'
  return `${v.toFixed(1)}%`
}

// The predicted-vs-actual review: how well does the model's pre-race WPR
// projection line up with what actually happened, across every resulted
// race. Ported from toprate_html_v3.py's WPR Accuracy tab, scoped to what
// this rebuild already has (see lib/accuracyStats.ts for what's deferred).
export function ReviewTab({ races, onSelectRace }: ReviewTabProps) {
  const [period, setPeriod] = useState<Period>('90')
  const [excludeBush, setExcludeBush] = useState(true)
  const [sortBy, setSortBy] = useState<'miss' | 'date'>('miss')

  const rows = useMemo(
    () => collectAccuracyRows(races, { period, excludeBush }),
    [races, period, excludeBush]
  )
  const stats = useMemo(() => computeAccuracyStats(rows), [rows])
  const outcome = useMemo(() => computeOutcomeStats(rows), [rows])
  const distBreakdown = useMemo(
    () => computeBreakdown(rows, (r) => distanceBand(r.distance)),
    [rows]
  )
  const goingBreakdown = useMemo(() => computeBreakdown(rows, (r) => r.going), [rows])

  const detailRows = useMemo(() => {
    const sorted = [...rows]
    if (sortBy === 'miss') sorted.sort((a, b) => Math.abs(b.miss) - Math.abs(a.miss))
    else sorted.sort((a, b) => b.date.localeCompare(a.date))
    return sorted.slice(0, MAX_DETAIL_ROWS)
  }, [rows, sortBy])

  return (
    <div className="flex flex-col gap-4">
      <div className="flex flex-wrap items-center gap-3">
        <div className="flex rounded-md border border-line bg-panel p-0.5">
          {PERIODS.map((p) => (
            <button
              key={p.value}
              type="button"
              onClick={() => setPeriod(p.value)}
              className={
                'rounded px-2.5 py-1 text-xs font-medium transition-colors ' +
                (period === p.value ? 'bg-emerald text-white' : 'text-ink-mute hover:text-ink')
              }
            >
              {p.label}
            </button>
          ))}
        </div>
        <label className="flex items-center gap-1.5 text-xs text-ink-soft">
          <input
            type="checkbox"
            checked={excludeBush}
            onChange={(e) => setExcludeBush(e.target.checked)}
            className="accent-emerald"
          />
          Exclude bush/picnic tracks
        </label>
      </div>

      {stats.n === 0 ? (
        <div className="rounded-lg border border-line bg-panel p-6 text-center text-sm text-ink-mute">
          No resulted, projected races in this window yet.
        </div>
      ) : (
        <>
          <div>
            <h2 className="mb-2 text-sm font-semibold text-ink">Projection accuracy</h2>
            <div className="grid grid-cols-2 gap-2 sm:grid-cols-5">
              <StatTile label="Runners" value={String(stats.n)} />
              <StatTile
                label="Mean abs. error"
                value={fmtWpr(stats.mae)}
                sublabel="typical miss, WPR pts"
              />
              <StatTile
                label="Bias"
                value={fmtSigned(stats.bias)}
                sublabel={stats.bias != null && stats.bias > 0 ? 'under-projects' : 'over-projects'}
                tone={stats.bias != null && Math.abs(stats.bias) >= 1 ? 'negative' : 'default'}
              />
              <StatTile label="Within 3 pts" value={fmtPct(stats.within3Pct)} tone="positive" />
              <StatTile label="Within 6 pts" value={fmtPct(stats.within6Pct)} tone="positive" />
            </div>
          </div>

          <div>
            <h2 className="mb-2 text-sm font-semibold text-ink">Outcomes</h2>
            <div className="grid grid-cols-2 gap-2 sm:grid-cols-4">
              <StatTile
                label="Top pick wins"
                value={fmtPct(outcome.topPickWinPct)}
                sublabel={
                  outcome.fieldAvgWinPct != null
                    ? `field avg ${fmtPct(outcome.fieldAvgWinPct)} (n=${outcome.topPickN})`
                    : `n=${outcome.topPickN}`
                }
                tone="positive"
              />
              <StatTile
                label="Top pick places"
                value={fmtPct(outcome.topPickPlacePct)}
                sublabel={`n=${outcome.topPickN}`}
              />
              <StatTile
                label="Winner's median rank"
                value={outcome.winnerMedianRank != null ? outcome.winnerMedianRank.toFixed(1) : '-'}
                sublabel={`n=${outcome.winnerN} winners`}
              />
              <StatTile
                label="Winner in top 3"
                value={fmtPct(outcome.winnerTop3Pct)}
                sublabel="predicted rank <=3"
              />
            </div>
          </div>

          {(distBreakdown.length > 0 || goingBreakdown.length > 0) && (
            <div className="grid grid-cols-1 gap-4 sm:grid-cols-2">
              {distBreakdown.length > 0 && (
                <BreakdownTable title="By distance" rows={distBreakdown} />
              )}
              {goingBreakdown.length > 0 && (
                <BreakdownTable title="By going" rows={goingBreakdown} />
              )}
            </div>
          )}

          <div>
            <div className="mb-2 flex items-center justify-between">
              <h2 className="text-sm font-semibold text-ink">
                Runner detail{rows.length > MAX_DETAIL_ROWS ? ` (worst ${MAX_DETAIL_ROWS} of ${rows.length})` : ''}
              </h2>
              <div className="flex rounded-md border border-line bg-panel p-0.5">
                <button
                  type="button"
                  onClick={() => setSortBy('miss')}
                  className={
                    'rounded px-2 py-0.5 text-xs font-medium transition-colors ' +
                    (sortBy === 'miss' ? 'bg-emerald text-white' : 'text-ink-mute hover:text-ink')
                  }
                >
                  Biggest miss
                </button>
                <button
                  type="button"
                  onClick={() => setSortBy('date')}
                  className={
                    'rounded px-2 py-0.5 text-xs font-medium transition-colors ' +
                    (sortBy === 'date' ? 'bg-emerald text-white' : 'text-ink-mute hover:text-ink')
                  }
                >
                  Most recent
                </button>
              </div>
            </div>
            <div className="overflow-x-auto rounded-lg border border-line bg-panel">
              <table className="min-w-[640px] w-full text-sm">
                <thead>
                  <tr className="border-b border-line text-left text-xs text-ink-mute">
                    <th className="px-3 py-2 font-medium">Date</th>
                    <th className="px-3 py-2 font-medium">Track</th>
                    <th className="px-3 py-2 font-medium">Horse</th>
                    <th className="px-3 py-2 text-right font-medium">Pred</th>
                    <th className="px-3 py-2 text-right font-medium">Actual</th>
                    <th className="px-3 py-2 text-right font-medium">Miss</th>
                    <th className="px-3 py-2 text-right font-medium">Pred rank</th>
                    <th className="px-3 py-2 text-right font-medium">Finish</th>
                  </tr>
                </thead>
                <tbody className="divide-y divide-line-soft">
                  {detailRows.map((r, i) => (
                    <tr
                      key={`${r.raceId}-${r.horse}-${i}`}
                      onClick={() => onSelectRace(r.raceId, r.date)}
                      className="cursor-pointer hover:bg-bg"
                    >
                      <td className="whitespace-nowrap px-3 py-1.5 text-ink-mute">{r.date}</td>
                      <td className="whitespace-nowrap px-3 py-1.5">{r.venue}</td>
                      <td className="px-3 py-1.5 font-medium">{r.horse}</td>
                      <td className="px-3 py-1.5 text-right font-mono">{fmtWpr(r.predicted)}</td>
                      <td className="px-3 py-1.5 text-right font-mono">{fmtWpr(r.actual)}</td>
                      <td
                        className={
                          'px-3 py-1.5 text-right font-mono font-medium ' +
                          (r.miss > 0 ? 'text-emerald-deep' : r.miss < 0 ? 'text-rose' : 'text-ink-mute')
                        }
                      >
                        {fmtSigned(r.miss)}
                      </td>
                      <td className="px-3 py-1.5 text-right text-ink-mute">{r.predictedRank ?? '-'}</td>
                      <td className="px-3 py-1.5 text-right text-ink-mute">
                        {r.won ? <span className="font-semibold text-emerald-deep">1st</span> : (r.finishPosition ?? '-')}
                      </td>
                    </tr>
                  ))}
                </tbody>
              </table>
            </div>
          </div>
        </>
      )}
    </div>
  )
}

function BreakdownTable({ title, rows }: { title: string; rows: { group: string; n: number; mae: number; bias: number }[] }) {
  return (
    <div className="overflow-hidden rounded-lg border border-line bg-panel">
      <div className="border-b border-line px-3 py-2 text-xs font-semibold text-ink">{title}</div>
      <table className="w-full text-xs">
        <thead>
          <tr className="text-left text-ink-mute">
            <th className="px-3 py-1.5 font-medium">Group</th>
            <th className="px-3 py-1.5 text-right font-medium">n</th>
            <th className="px-3 py-1.5 text-right font-medium">MAE</th>
            <th className="px-3 py-1.5 text-right font-medium">Bias</th>
          </tr>
        </thead>
        <tbody className="divide-y divide-line-soft">
          {rows.map((r) => (
            <tr key={r.group}>
              <td className="px-3 py-1 text-ink">{r.group}</td>
              <td className="px-3 py-1 text-right text-ink-mute">{r.n}</td>
              <td className="px-3 py-1 text-right font-mono">{r.mae.toFixed(1)}</td>
              <td className="px-3 py-1 text-right font-mono">{fmtSigned(r.bias)}</td>
            </tr>
          ))}
        </tbody>
      </table>
    </div>
  )
}
