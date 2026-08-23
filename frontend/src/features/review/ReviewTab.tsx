import { useMemo, useState } from 'react'
import type { Race } from '../../types/domain'
import {
  buildHeadlineSummary,
  collectAccuracyRows,
  computeAccuracyStats,
  computeBreakdown,
  computeCalibrationBins,
  computeMarginStats,
  computeOutcomeStats,
  computeRankStats,
  computeWinnerRankStats,
  distanceBand,
  splitVoided,
  type AccuracyRow,
  type Period,
} from '../../lib/accuracyStats'
import { goingBand } from '../../lib/pace'
import { fmtWpr } from '../../lib/format'
import { StatTile } from '../../components/StatTile'
import { PredictedVsActualChart } from '../../components/PredictedVsActualChart'
import { useScrollShadow } from '../../lib/useScrollShadow'

interface ReviewTabProps {
  races: Race[]
  onSelectRace: (raceId: string, date: string) => void
}

const PERIODS: { value: Period; label: string; sentence: string }[] = [
  { value: '30', label: 'Last 30 days', sentence: 'Over the last 30 days' },
  { value: '90', label: 'Last 90 days', sentence: 'Over the last 90 days' },
  { value: 'all', label: 'All time', sentence: 'Across all time' },
]

const MAX_DETAIL_ROWS = 100

type GroupFilter = { kind: 'distance' | 'going'; value: string } | null

function fmtSigned(v: number | null, digits = 1): string {
  if (v == null || Number.isNaN(v)) return '-'
  return `${v > 0 ? '+' : ''}${v.toFixed(digits)}`
}

function fmtPct(v: number | null): string {
  if (v == null || Number.isNaN(v)) return '-'
  return `${v.toFixed(1)}%`
}

function matchesGroupFilter(r: AccuracyRow, filter: GroupFilter): boolean {
  if (!filter) return true
  if (filter.kind === 'distance') return distanceBand(r.distance) === filter.value
  return goingBand(r.going) === filter.value
}

// The predicted-vs-actual review: how well does the model's pre-race WPR
// projection line up with what actually happened, across every resulted
// race. Ported from toprate_html_v3.py's WPR Accuracy tab, scoped to what
// this rebuild already has (see lib/accuracyStats.ts for what's deferred).
export function ReviewTab({ races, onSelectRace }: ReviewTabProps) {
  const [period, setPeriod] = useState<Period>('90')
  const [excludeBush, setExcludeBush] = useState(true)
  const [excludeVoid, setExcludeVoid] = useState(true)
  const [sortBy, setSortBy] = useState<'miss' | 'date'>('date')
  const [groupFilter, setGroupFilter] = useState<GroupFilter>(null)
  const { ref: tableScrollRef, canScrollRight } = useScrollShadow<HTMLDivElement>()

  const allRows = useMemo(
    () => collectAccuracyRows(races, { period, excludeBush }),
    [races, period, excludeBush]
  )
  // A compromised run (vet, checked, eased, fell, etc - per video/steward
  // comments) isn't a fair test of the model in either direction, so it's
  // excluded from every stat below by default - matching what the
  // retrain's own training-target filter already does (see lib/wprVoid.ts).
  // Kept, not discarded: the toggle below can bring them back into view.
  const { clean, voided } = useMemo(() => splitVoided(allRows), [allRows])
  const rows = excludeVoid ? clean : allRows

  const stats = useMemo(() => computeAccuracyStats(rows), [rows])
  const outcome = useMemo(() => computeOutcomeStats(rows), [rows])
  const rankStats = useMemo(() => computeRankStats(rows), [rows])
  const winnerRankStats = useMemo(() => computeWinnerRankStats(rows), [rows])
  const marginStats = useMemo(() => computeMarginStats(rows), [rows])
  const calibration = useMemo(() => computeCalibrationBins(rows), [rows])
  const distBreakdown = useMemo(
    () => computeBreakdown(rows, (r) => distanceBand(r.distance)),
    [rows]
  )
  // Grouped by going BAND (Firm/Good/Soft/Heavy), matching the WPR model's
  // own own_going term and lib/pace.ts's goingBand() - not the raw going
  // string, which would splinter "Soft 5"/"Soft 6"/"Soft 7" into separate
  // thin groups instead of one reliably-sized "Soft" group.
  const goingBreakdown = useMemo(
    () => computeBreakdown(rows, (r) => goingBand(r.going) ?? ''),
    [rows]
  )

  const periodSentence = PERIODS.find((p) => p.value === period)?.sentence ?? 'Overall'
  const headline = useMemo(
    () => buildHeadlineSummary(periodSentence, outcome, rankStats, marginStats, voided.length, allRows.length),
    [periodSentence, outcome, rankStats, marginStats, voided.length, allRows.length]
  )

  const filteredRows = useMemo(
    () => rows.filter((r) => matchesGroupFilter(r, groupFilter)),
    [rows, groupFilter]
  )
  const detailRows = useMemo(() => {
    const sorted = [...filteredRows]
    if (sortBy === 'miss') sorted.sort((a, b) => Math.abs(b.miss) - Math.abs(a.miss))
    else sorted.sort((a, b) => b.date.localeCompare(a.date))
    return sorted.slice(0, MAX_DETAIL_ROWS)
  }, [filteredRows, sortBy])

  function toggleFilter(kind: 'distance' | 'going', value: string) {
    setGroupFilter((prev) => (prev && prev.kind === kind && prev.value === value ? null : { kind, value }))
  }

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
        <label className="flex items-center gap-1.5 text-xs text-ink-soft">
          <input
            type="checkbox"
            checked={excludeVoid}
            onChange={(e) => setExcludeVoid(e.target.checked)}
            className="accent-emerald"
          />
          Exclude compromised runs (vet/checked/eased/etc)
        </label>
      </div>

      {stats.n === 0 ? (
        <div className="rounded-lg border border-line bg-panel p-6 text-center text-sm text-ink-mute">
          No resulted, projected races in this window yet.
        </div>
      ) : (
        <>
          {headline.length > 0 && (
            <div className="rounded-lg border border-emerald-line bg-emerald-bg p-3 text-sm text-ink">
              <div className="flex flex-col gap-1">
                {headline.map((line, i) => (
                  <p key={i}>{line}</p>
                ))}
              </div>
            </div>
          )}

          <div>
            <h2 className="text-sm font-semibold text-ink">Point accuracy</h2>
            <p className="mb-2 text-xs text-ink-faint">
              Each horse's own predicted WPR vs its own actual WPR, in isolation - not whether it beat the
              others in its race. See rank accuracy below for that.
            </p>
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

          <PredictedVsActualChart bins={calibration} />

          <div>
            <h2 className="text-sm font-semibold text-ink">Rank accuracy</h2>
            <p className="mb-2 text-xs text-ink-faint">
              Did the model order THIS race correctly - not just whether each horse's own number was close. A
              horse predicted 95 that runs 95 but finishes 3rd wasn't a bad prediction on its own; the race went
              to rivals the model under-rated. That's a rank miss, not a point miss.
            </p>
            <div className="grid grid-cols-2 gap-2 sm:grid-cols-4">
              <StatTile
                label="Rank error"
                value={rankStats.rankMae != null ? rankStats.rankMae.toFixed(2) : '-'}
                sublabel={`positions off, avg/race (n=${rankStats.races})`}
              />
              <StatTile
                label="Rank correlation"
                value={rankStats.spearman != null ? rankStats.spearman.toFixed(2) : '-'}
                sublabel="1.0 = perfect order, 0 = random"
                tone="positive"
              />
              <StatTile
                label="Winner's median rank"
                value={outcome.winnerMedianRank != null ? outcome.winnerMedianRank.toFixed(1) : '-'}
                sublabel={`n=${outcome.winnerN} winners`}
              />
              <StatTile
                label="Winner rank error"
                value={
                  winnerRankStats.meanWinnerRankError != null
                    ? winnerRankStats.meanWinnerRankError.toFixed(2)
                    : '-'
                }
                sublabel={`mean, positions above 1st (n=${winnerRankStats.winnerN})`}
              />
            </div>
            <div className="mt-2 grid grid-cols-2 gap-2 sm:grid-cols-4">
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
                label="Rank-win correlation"
                value={
                  winnerRankStats.rankWinCorrelation != null
                    ? winnerRankStats.rankWinCorrelation.toFixed(2)
                    : '-'
                }
                sublabel="better rank -> more likely to win"
                tone="positive"
              />
              <StatTile
                label="Winner in top 3"
                value={fmtPct(outcome.winnerTop3Pct)}
                sublabel="predicted rank <=3"
              />
            </div>
          </div>

          <div>
            <h2 className="text-sm font-semibold text-ink">Margin accuracy</h2>
            <p className="mb-2 text-xs text-ink-faint">
              A horse predicted 5 WPR points behind the top pick, whose actual result also lands about 5 points
              behind the top pick's actual result, had its SPACING to the field leader correctly predicted - a
              third dimension beyond "was the order right" and "was each number close".
            </p>
            <div className="grid grid-cols-2 gap-2 sm:grid-cols-4">
              <StatTile
                label="Margin error"
                value={marginStats.mae != null ? marginStats.mae.toFixed(1) : '-'}
                sublabel={`WPR pts off, vs top pick (n=${marginStats.n})`}
              />
              <StatTile
                label="Margin bias"
                value={fmtSigned(marginStats.bias, 1)}
                sublabel={
                  marginStats.bias != null && Math.abs(marginStats.bias) >= 1
                    ? marginStats.bias > 0
                      ? 'gaps run wider than predicted'
                      : 'gaps run narrower than predicted'
                    : 'roughly unbiased'
                }
                tone={marginStats.bias != null && Math.abs(marginStats.bias) >= 1 ? 'negative' : 'default'}
              />
            </div>
          </div>

          {(distBreakdown.length > 0 || goingBreakdown.length > 0) && (
            <div className="grid grid-cols-1 gap-4 sm:grid-cols-2">
              {distBreakdown.length > 0 && (
                <BreakdownTable
                  title="By distance"
                  rows={distBreakdown}
                  activeValue={groupFilter?.kind === 'distance' ? groupFilter.value : null}
                  onSelect={(value) => toggleFilter('distance', value)}
                />
              )}
              {goingBreakdown.length > 0 && (
                <BreakdownTable
                  title="By going"
                  rows={goingBreakdown}
                  activeValue={groupFilter?.kind === 'going' ? groupFilter.value : null}
                  onSelect={(value) => toggleFilter('going', value)}
                />
              )}
            </div>
          )}

          <div>
            <div className="mb-1 flex flex-wrap items-center justify-between gap-2">
              <h2 className="text-sm font-semibold text-ink">
                Runner detail
                {filteredRows.length > MAX_DETAIL_ROWS ? ` (worst ${MAX_DETAIL_ROWS} of ${filteredRows.length})` : ''}
                {groupFilter && (
                  <button
                    type="button"
                    onClick={() => setGroupFilter(null)}
                    className="ml-2 rounded-full bg-emerald-bg px-2 py-0.5 text-xs font-medium text-emerald-deep hover:opacity-80"
                  >
                    {groupFilter.value} &times;
                  </button>
                )}
              </h2>
              <div className="flex rounded-md border border-line bg-panel p-0.5">
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
              </div>
            </div>
            <p className="mb-2 text-xs text-ink-faint">
              Miss = actual minus predicted WPR: positive (green) means the horse ran better than projected,
              negative (red) means it ran worse.{' '}
              {excludeVoid && voided.length > 0
                ? `Compromised runs (${voided.length}) are hidden - see the toggle above.`
                : voided.length > 0
                  ? 'Rows flagged ⚠ were compromised (vet/checked/eased/etc) - still shown, but not a fair test.'
                  : ''}
            </p>
            <div className="relative">
              <div ref={tableScrollRef} className="overflow-x-auto rounded-lg border border-line bg-panel">
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
                        <td className="px-3 py-1.5 font-medium">
                          {r.horse}
                          {r.voided && (
                            <span className="ml-1 cursor-help text-amber" title={`Compromised: ${r.voidReason}`}>
                              &#9888;
                            </span>
                          )}
                        </td>
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
              {canScrollRight && (
                <div className="pointer-events-none absolute inset-y-0 right-0 w-8 rounded-r-lg bg-gradient-to-l from-panel to-transparent" />
              )}
            </div>
          </div>
        </>
      )}
    </div>
  )
}

function BreakdownTable({
  title,
  rows,
  activeValue,
  onSelect,
}: {
  title: string
  rows: { group: string; n: number; mae: number; bias: number }[]
  activeValue: string | null
  onSelect: (value: string) => void
}) {
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
            <tr
              key={r.group}
              onClick={() => onSelect(r.group)}
              className={
                'cursor-pointer transition-colors hover:bg-bg ' +
                (activeValue === r.group ? 'bg-emerald-bg' : '')
              }
            >
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
