import { useMemo, useState, type ReactNode } from 'react'
import type { OverlayTracker, Race } from '../../types/domain'
import {
  buildHeadlineSummary,
  collectAccuracyRows,
  computeAccuracyStats,
  computeBreakdown,
  computeCalibrationBins,
  computeMarginStats,
  computeOutcomeStats,
  computeRankStats,
  computeStrikeRates,
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
import { collectSignalWatchRows, computeSignalWatchStats, SIGNAL_WATCH_RULE } from '../../lib/signalWatch'

interface ReviewTabProps {
  races: Race[]
  onSelectRace: (raceId: string, date: string, runId?: string) => void
  overlayTracker: OverlayTracker | null
}

const PERIODS: { value: Period; label: string; sentence: string }[] = [
  { value: '30', label: 'Last 30 days', sentence: 'Over the last 30 days' },
  { value: '90', label: 'Last 90 days', sentence: 'Over the last 90 days' },
  { value: 'all', label: 'All time', sentence: 'Across all time' },
]

const MAX_DETAIL_ROWS = 100

type GroupFilter = { kind: 'distance' | 'going' | 'venue'; value: string } | null

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
  if (filter.kind === 'venue') return r.venue === filter.value
  return goingBand(r.going) === filter.value
}

// The predicted-vs-actual review: how well does the model's pre-race WPR
// projection line up with what actually happened, across every resulted
// race. Ported from toprate_html_v3.py's WPR Accuracy tab, scoped to what
// this rebuild already has (see lib/accuracyStats.ts for what's deferred).
//
// Redesigned (Aug 2026, user feedback: "not sure what to do with it") from
// a flat wall of ~15 equal-weight stat tiles into one clear verdict (top
// pick win rate vs a random runner - the single number that actually
// answers "should I trust the model's picks right now") with the rest of
// the analysis - the exact same numbers as before, nothing removed - folded
// into three named, collapsible sections a bettor opens only when they want
// to go deeper. Diagnostics defaults open (it's the real substance); the
// breakdown tables and the individual-runner table default closed - both
// are audit/curiosity tools, not something you need to look at to get the
// tab's answer.
export function ReviewTab({ races, onSelectRace, overlayTracker }: ReviewTabProps) {
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
  const strikeRates = useMemo(() => computeStrikeRates(rows), [rows])
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
  // "By venue" - is the model any good AT THIS TRACK specifically. Same
  // MIN_BREAKDOWN_N=10 floor as distance/going keeps one-off country tracks
  // from cluttering the table with noisy single-digit-n rows.
  const venueBreakdown = useMemo(() => computeBreakdown(rows, (r) => r.venue), [rows])

  // Signal watch: tracks one specific candidate rule found via offline
  // backtesting (not a proven edge - see lib/signalWatch.ts's own comment
  // for the full caveat). Uses the raw races prop directly, independent
  // of the accuracy pipeline above, so this experimental addition can
  // never affect the established accuracy numbers.
  const signalWatchRows = useMemo(
    () => collectSignalWatchRows(races, { period, excludeBush }),
    [races, period, excludeBush]
  )
  const signalWatchStats = useMemo(() => computeSignalWatchStats(signalWatchRows), [signalWatchRows])

  // The hero number: how much better than a coin-flip-against-the-field is
  // the model's top pick, in a single multiplier a non-statistician reads
  // instantly. null when there isn't a sane field average to divide by.
  const winMultiplier =
    outcome.topPickWinPct != null && outcome.fieldAvgWinPct != null && outcome.fieldAvgWinPct > 0
      ? outcome.topPickWinPct / outcome.fieldAvgWinPct
      : null

  const periodSentence = PERIODS.find((p) => p.value === period)?.sentence ?? 'Overall'
  const headline = useMemo(
    () => buildHeadlineSummary(periodSentence, strikeRates, rankStats, marginStats, voided.length, allRows.length),
    [periodSentence, strikeRates, rankStats, marginStats, voided.length, allRows.length]
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

  function toggleFilter(kind: 'distance' | 'going' | 'venue', value: string) {
    setGroupFilter((prev) => (prev && prev.kind === kind && prev.value === value ? null : { kind, value }))
  }

  return (
    <div className="flex flex-col gap-4">
      <OverlayTrackerCard tracker={overlayTracker} onSelectRace={onSelectRace} />

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
          <div className="rounded-lg border border-emerald-line bg-emerald-bg p-4 sm:p-5">
            <div className="text-xs font-semibold uppercase tracking-wide text-emerald-deep">
              Strike rates - how often the winner matched the model's calls
            </div>
            <div className="mt-2 grid grid-cols-2 gap-3 sm:grid-cols-4">
              {strikeRates.map((s) => (
                <div key={s.label}>
                  <div className="text-2xl font-bold text-ink sm:text-3xl">{fmtPct(s.strikePct)}</div>
                  <div className="text-xs text-ink-mute">{s.label}</div>
                  {s.label === 'Top rated' && winMultiplier != null && (
                    <div className="text-xs font-medium text-emerald-deep">
                      {winMultiplier.toFixed(1)}&times; field avg ({fmtPct(outcome.fieldAvgWinPct)})
                    </div>
                  )}
                  <div className="text-[11px] text-ink-faint">n={s.n.toLocaleString()}</div>
                </div>
              ))}
            </div>
            {headline.length > 0 && (
              <div className="mt-3 flex flex-col gap-1 border-t border-emerald-line pt-3 text-sm text-ink">
                {headline.map((line, i) => (
                  <p key={i}>{line}</p>
                ))}
              </div>
            )}
          </div>

          <Disclosure title="Full diagnostics" subtitle="Point, rank, and margin accuracy - depth behind the strike rates above, including the model's typical WPR miss">
            <div className="flex flex-col gap-4">
              <div>
                <h3 className="text-sm font-semibold text-ink">Point accuracy</h3>
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
                <h3 className="text-sm font-semibold text-ink">Rank accuracy</h3>
                <p className="mb-2 text-xs text-ink-faint">
                  Did the model order THIS race correctly - not just whether each horse's own number was close. A
                  horse predicted 95 that runs 95 but finishes 3rd wasn't a bad prediction on its own; the race
                  went to rivals the model under-rated. That's a rank miss, not a point miss.
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
                <div className="mt-2 grid grid-cols-2 gap-2 sm:grid-cols-2">
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
                <h3 className="text-sm font-semibold text-ink">Margin accuracy</h3>
                <p className="mb-2 text-xs text-ink-faint">
                  A horse predicted 5 WPR points behind the top pick, whose actual result also lands about 5
                  points behind the top pick's actual result, had its SPACING to the field leader correctly
                  predicted - a third dimension beyond "was the order right" and "was each number close".
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
            </div>
          </Disclosure>

          {(distBreakdown.length > 0 || goingBreakdown.length > 0 || venueBreakdown.length > 0) && (
            <Disclosure
              title="Where the model struggles"
              subtitle="A weak top-rated strike rate, high MAE, or big bias in a group below means be more skeptical of top picks from there"
            >
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
                {venueBreakdown.length > 0 && (
                  <BreakdownTable
                    title="By venue"
                    rows={venueBreakdown}
                    activeValue={groupFilter?.kind === 'venue' ? groupFilter.value : null}
                    onSelect={(value) => toggleFilter('venue', value)}
                  />
                )}
              </div>
            </Disclosure>
          )}

          <Disclosure
            title="Signal watch: jockey/trainer form (experimental)"
            subtitle="One candidate rule from offline backtesting, tracked here against real results - not a proven edge, not a bet recommendation"
          >
            <p className="mb-3 text-xs text-ink-faint">
              Backtested rule: WPR edge &ge; {(SIGNAL_WATCH_RULE.edgeThreshold * 100).toFixed(0)}pp vs the
              market, price &le; ${SIGNAL_WATCH_RULE.priceCap}, and the jockey's 90-day strike rate &ge;{' '}
              {SIGNAL_WATCH_RULE.jockeyWinPctCut}% or the trainer's 365-day strike rate &ge;{' '}
              {SIGNAL_WATCH_RULE.trainerWinPctCut}%. In offline K-fold backtesting this was the ONE rule (out
              of dozens tried - price caps, market-rank agreement, barrier, distance, class move, and more)
              that came back positive rather than negative, holding up across all 4 held-out folds - but it
              was not statistically significant (t=1.58, short of the usual 1.96 bar) and came from a wide
              search, so real forward results here are the actual test, not the backtest number.
            </p>
            {signalWatchStats.n === 0 ? (
              <div className="rounded-lg border border-line bg-panel p-4 text-center text-sm text-ink-mute">
                No runners have matched this rule in this window yet.
              </div>
            ) : (
              <div className="grid grid-cols-2 gap-2 sm:grid-cols-4">
                <StatTile label="Matches" value={String(signalWatchStats.n)} />
                <StatTile label="Strike rate" value={fmtPct(signalWatchStats.strikePct)} />
                <StatTile
                  label="ROI"
                  value={fmtSigned(signalWatchStats.roiPct, 1) + '%'}
                  tone={signalWatchStats.roiPct != null && signalWatchStats.roiPct > 0 ? 'positive' : 'negative'}
                />
                <StatTile
                  label="Avg price"
                  value={signalWatchStats.avgPrice != null ? `$${signalWatchStats.avgPrice.toFixed(2)}` : '-'}
                />
              </div>
            )}
            {signalWatchRows.length > 0 && (
              <div className="mt-3 max-h-64 overflow-y-auto rounded-lg border border-line">
                <table className="w-full text-xs">
                  <thead className="sticky top-0 bg-panel">
                    <tr className="text-left text-ink-mute">
                      <th className="px-3 py-1.5 font-medium">Date</th>
                      <th className="px-3 py-1.5 font-medium">Track</th>
                      <th className="px-3 py-1.5 font-medium">Horse</th>
                      <th className="px-3 py-1.5 text-right font-medium">Price</th>
                      <th className="px-3 py-1.5 text-right font-medium">Edge</th>
                      <th className="px-3 py-1.5 text-right font-medium">Result</th>
                    </tr>
                  </thead>
                  <tbody className="divide-y divide-line-soft">
                    {[...signalWatchRows]
                      .sort((a, b) => b.date.localeCompare(a.date))
                      .slice(0, MAX_DETAIL_ROWS)
                      .map((r, i) => (
                        <tr
                          key={`${r.raceId}-${r.horse}-${i}`}
                          onClick={() => onSelectRace(r.raceId, r.date, r.runId)}
                          className="cursor-pointer hover:bg-bg"
                        >
                          <td className="whitespace-nowrap px-3 py-1 text-ink-mute">{r.date}</td>
                          <td className="whitespace-nowrap px-3 py-1">{r.venue}</td>
                          <td className="px-3 py-1 font-medium">{r.horse}</td>
                          <td className="px-3 py-1 text-right font-mono">${r.price.toFixed(2)}</td>
                          <td className="px-3 py-1 text-right font-mono">{fmtSigned(r.edge * 100, 1)}pp</td>
                          <td className="px-3 py-1 text-right">
                            {r.won ? (
                              <span className="font-semibold text-emerald-deep">Won</span>
                            ) : (
                              <span className="text-ink-mute">Lost</span>
                            )}
                          </td>
                        </tr>
                      ))}
                  </tbody>
                </table>
              </div>
            )}
          </Disclosure>

          <Disclosure
            title="Explore individual results"
            subtitle={
              `${filteredRows.length.toLocaleString()} runners in this window` +
              (groupFilter ? ` - filtered to ${groupFilter.value}` : '') +
              ' - click a row to jump to that runner'
            }
          >
            <div className="mb-2 flex flex-wrap items-center justify-between gap-2">
              {groupFilter ? (
                <button
                  type="button"
                  onClick={() => setGroupFilter(null)}
                  className="rounded-full bg-emerald-bg px-2 py-0.5 text-xs font-medium text-emerald-deep hover:opacity-80"
                >
                  {groupFilter.value} &times;
                </button>
              ) : (
                <span />
              )}
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
              {filteredRows.length > MAX_DETAIL_ROWS ? ` Showing the worst ${MAX_DETAIL_ROWS}.` : ''}
            </p>
            <div className="relative">
              {/* max-h + overflow-y bounds this to one scrollable panel instead of
                  a 100-row page-length table (this section alone used to push the
                  tab past 5000px tall) - the sticky header keeps column labels in
                  view while scrolling through the rows. */}
              <div
                ref={tableScrollRef}
                className="max-h-[560px] overflow-x-auto overflow-y-auto rounded-lg border border-line bg-panel"
              >
                <table className="min-w-[640px] w-full text-sm">
                  <thead className="sticky top-0 z-10 bg-panel">
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
                        onClick={() => onSelectRace(r.raceId, r.date, r.runId)}
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
          </Disclosure>
        </>
      )}
    </div>
  )
}

// Minimum settled bets before the live tracker's own strike/ROI numbers are
// shown as real figures rather than "too early to read" - a handful of
// results is nearly pure coin-flip noise (see the backtest's own t-stats,
// which needed thousands of bets to clear significance) and displaying a
// confident-looking percentage from n=6 would be actively misleading.
const OVERLAY_MIN_SETTLED_TO_SHOW = 30

function overlaySignificant(tStat: number | null): boolean {
  return tStat != null && Math.abs(tStat) >= 1.96
}

// Overlay ROI tracker: always-visible summary (unlike the collapsed
// "Signal watch" Disclosure below) pairing the offline walk-forward
// validation that justified shipping the no-calibration-slope/trained-
// population-term architecture with an automated, ongoing record of what
// backing every runner the model flags (edge >= threshold) would actually
// return, day by day, as real results land. Explicitly NOT a log of bets
// anyone placed - see toprate_daily.compute_overlay_tracker's own
// docstring for why a real bet-log P&L tab remains a separate, deliberately
// not-built thing (CLAUDE.md).
type OverlayRangePreset = '7' | '30' | 'all' | 'custom'

const OVERLAY_RANGE_PRESETS: { value: OverlayRangePreset; label: string; days?: number }[] = [
  { value: '7', label: 'Last 7 days', days: 7 },
  { value: '30', label: 'Last 30 days', days: 30 },
  { value: 'all', label: 'All' },
]

function daysAgoIso(days: number): string {
  const d = new Date()
  d.setDate(d.getDate() - days)
  return d.toISOString().slice(0, 10)
}

function OverlayTrackerCard({
  tracker,
  onSelectRace,
}: {
  tracker: OverlayTracker | null
  onSelectRace: (raceId: string, date: string, runId?: string) => void
}) {
  const [showBets, setShowBets] = useState(false)
  const [rangePreset, setRangePreset] = useState<OverlayRangePreset>('7')
  const [customFrom, setCustomFrom] = useState('')
  const [customTo, setCustomTo] = useState('')

  const preset = OVERLAY_RANGE_PRESETS.find((p) => p.value === rangePreset)
  const rangeFrom =
    rangePreset === 'custom' ? customFrom : preset?.days != null ? daysAgoIso(preset.days) : ''
  const rangeTo = rangePreset === 'custom' ? customTo : ''

  const filteredBets = useMemo(() => {
    if (!tracker) return []
    return tracker.bets.filter((b) => (!rangeFrom || b.date >= rangeFrom) && (!rangeTo || b.date <= rangeTo))
  }, [tracker, rangeFrom, rangeTo])

  const filteredStats = useMemo(() => {
    if (filteredBets.length === 0) return null
    const n = filteredBets.length
    const wins = filteredBets.filter((b) => b.won).length
    const roi = (filteredBets.reduce((sum, b) => sum + b.profit, 0) / n) * 100
    return { n, strikePct: (wins / n) * 100, roiPct: roi }
  }, [filteredBets])

  if (!tracker) return null
  const { backtest } = tracker
  const liveReady = tracker.nSettled >= OVERLAY_MIN_SETTLED_TO_SHOW

  return (
    <div className="rounded-lg border border-line bg-panel p-4 sm:p-5">
      <div className="text-xs font-semibold uppercase tracking-wide text-ink-mute">
        Overlay ROI tracker
      </div>
      <p className="mt-1 text-xs text-ink-faint">
        Runners where WPR's own fair-value price disagrees with the market by at least{' '}
        {(tracker.threshold * 100).toFixed(0)} percentage points - not a log of bets anyone placed, just what
        backing every one of these at the shown price would actually return.
      </p>

      <div className="mt-3 grid gap-3 sm:grid-cols-2">
        <div className="rounded-md border border-line-soft bg-bg p-3">
          <div className="flex items-center justify-between">
            <div className="text-xs font-semibold text-ink">Backtest validation</div>
            {backtest.validated ? (
              overlaySignificant(backtest.tStat) && backtest.roiPct > 0 && (
                <span className="rounded-full bg-emerald-bg px-1.5 py-0.5 text-[10px] font-medium text-emerald-deep">
                  significant
                </span>
              )
            ) : (
              <span className="rounded-full border border-amber-line bg-amber-bg px-1.5 py-0.5 text-[10px] font-medium text-amber">
                not validated
              </span>
            )}
          </div>
          <div className="mt-0.5 text-[11px] text-ink-faint">
            {backtest.method} &middot; {backtest.period}
          </div>
          <div className="mt-2 grid grid-cols-3 gap-2">
            <StatTile label="Bets" value={backtest.nBets.toLocaleString()} />
            <StatTile label="Strike rate" value={fmtPct(backtest.strikeRate)} />
            <StatTile
              label="ROI"
              value={fmtSigned(backtest.roiPct, 1) + '%'}
              tone={backtest.roiPct > 0 ? 'positive' : 'negative'}
            />
          </div>
          <div className="mt-1 text-[11px] text-ink-faint">t={backtest.tStat.toFixed(2)}</div>
          {!backtest.validated && backtest.note && (
            <div className="mt-2 rounded-md border border-amber-line bg-amber-bg p-2 text-[11px] leading-snug text-amber">
              {backtest.note}
            </div>
          )}
        </div>

        <div className="rounded-md border border-line-soft bg-bg p-3">
          <div className="flex items-center justify-between">
            <div className="text-xs font-semibold text-ink">Live since {tracker.liveSince}</div>
            {overlaySignificant(tracker.tStat) &&
              ((tracker.roiPct ?? 0) > 0 ? (
                <span className="rounded-full bg-emerald-bg px-1.5 py-0.5 text-[10px] font-medium text-emerald-deep">
                  significant
                </span>
              ) : (
                <span className="rounded-full border border-rose-line bg-rose-bg px-1.5 py-0.5 text-[10px] font-medium text-rose">
                  significantly negative
                </span>
              ))}
          </div>
          <div className="mt-0.5 text-[11px] text-ink-faint">
            {tracker.nPending} runner{tracker.nPending === 1 ? '' : 's'} flagged, not yet resulted
          </div>
          {!liveReady ? (
            <div className="mt-2 rounded-md border border-line-soft bg-panel p-2 text-center text-xs text-ink-mute">
              {tracker.nSettled === 0
                ? 'No settled overlay bets yet.'
                : `Only ${tracker.nSettled} settled so far - too few to read yet (needs ${OVERLAY_MIN_SETTLED_TO_SHOW}+).`}
            </div>
          ) : (
            <>
              <div className="mt-2 grid grid-cols-3 gap-2">
                <StatTile label="Bets" value={tracker.nSettled.toLocaleString()} />
                <StatTile label="Strike rate" value={fmtPct(tracker.strikeRate)} />
                <StatTile
                  label="ROI"
                  value={fmtSigned(tracker.roiPct, 1) + '%'}
                  tone={(tracker.roiPct ?? 0) > 0 ? 'positive' : 'negative'}
                />
              </div>
              <div className="mt-1 text-[11px] text-ink-faint">
                {tracker.tStat != null ? `t=${tracker.tStat.toFixed(2)}` : 'n/a'}
              </div>
            </>
          )}
        </div>
      </div>

      {tracker.bets.length > 0 && (
        <div className="mt-3 border-t border-line-soft pt-3">
          <button
            type="button"
            onClick={() => setShowBets((v) => !v)}
            className="text-xs font-medium text-emerald-deep hover:underline"
          >
            {showBets ? 'Hide' : 'View'} individual bets ({tracker.bets.length})
          </button>

          {showBets && (
            <div className="mt-2 flex flex-col gap-2">
              <div className="flex flex-wrap items-center gap-1.5">
                {OVERLAY_RANGE_PRESETS.map((p) => (
                  <button
                    key={p.value}
                    type="button"
                    onClick={() => setRangePreset(p.value)}
                    className={
                      'rounded px-2 py-0.5 text-xs font-medium transition-colors ' +
                      (rangePreset === p.value
                        ? 'bg-emerald text-white'
                        : 'border border-line text-ink-mute hover:text-ink')
                    }
                  >
                    {p.label}
                  </button>
                ))}
                <span className="text-xs text-ink-faint">or</span>
                <input
                  type="date"
                  value={customFrom}
                  min={tracker.liveSince}
                  onChange={(e) => {
                    setCustomFrom(e.target.value)
                    setRangePreset('custom')
                  }}
                  className="rounded-md border border-line bg-panel px-2 py-0.5 text-xs font-mono"
                />
                <span className="text-xs text-ink-faint">to</span>
                <input
                  type="date"
                  value={customTo}
                  min={tracker.liveSince}
                  onChange={(e) => {
                    setCustomTo(e.target.value)
                    setRangePreset('custom')
                  }}
                  className="rounded-md border border-line bg-panel px-2 py-0.5 text-xs font-mono"
                />
              </div>

              {filteredStats ? (
                <div className="text-xs text-ink-mute">
                  {filteredStats.n} bet{filteredStats.n === 1 ? '' : 's'} in range &middot; strike{' '}
                  {fmtPct(filteredStats.strikePct)} &middot; ROI{' '}
                  <span className={filteredStats.roiPct > 0 ? 'text-emerald-deep' : 'text-rose'}>
                    {fmtSigned(filteredStats.roiPct, 1)}%
                  </span>
                </div>
              ) : (
                <div className="text-xs text-ink-faint">
                  No settled bets in this range
                  {rangeTo && rangeTo < tracker.liveSince
                    ? ` (the live tracker only started ${tracker.liveSince} - there's no backfilled history before that).`
                    : '.'}
                </div>
              )}

              {filteredBets.length > 0 && (
                <div className="max-h-72 overflow-y-auto rounded-lg border border-line">
                  <table className="w-full text-xs">
                    <thead className="sticky top-0 bg-panel">
                      <tr className="text-left text-ink-mute">
                        <th className="px-3 py-1.5 font-medium">Date</th>
                        <th className="px-3 py-1.5 font-medium">Venue</th>
                        <th className="px-3 py-1.5 font-medium">Horse</th>
                        <th className="px-3 py-1.5 text-right font-medium">Price</th>
                        <th className="px-3 py-1.5 text-right font-medium">Edge</th>
                        <th className="px-3 py-1.5 text-right font-medium">Result</th>
                        <th className="px-3 py-1.5 text-right font-medium">Profit</th>
                      </tr>
                    </thead>
                    <tbody className="divide-y divide-line-soft">
                      {filteredBets.map((b, i) => (
                        <tr
                          key={`${b.raceId}-${b.horse}-${i}`}
                          onClick={() => onSelectRace(b.raceId, b.date)}
                          className="cursor-pointer hover:bg-bg"
                        >
                          <td className="whitespace-nowrap px-3 py-1 text-ink-mute">{b.date}</td>
                          <td className="whitespace-nowrap px-3 py-1">
                            {b.venue} R{b.race ?? '-'}
                          </td>
                          <td className="px-3 py-1 font-medium">{b.horse}</td>
                          <td className="px-3 py-1 text-right font-mono">${b.price.toFixed(2)}</td>
                          <td className="px-3 py-1 text-right font-mono">
                            {b.edge != null ? fmtSigned(b.edge * 100, 1) + 'pp' : '-'}
                          </td>
                          <td className="px-3 py-1 text-right">
                            {b.won ? (
                              <span className="font-medium text-emerald-deep">Won</span>
                            ) : (
                              <span className="text-ink-mute">{b.finish ? `${b.finish}th` : 'Lost'}</span>
                            )}
                          </td>
                          <td
                            className={`px-3 py-1 text-right font-mono ${b.profit > 0 ? 'text-emerald-deep' : 'text-rose'}`}
                          >
                            {fmtSigned(b.profit, 2)}u
                          </td>
                        </tr>
                      ))}
                    </tbody>
                  </table>
                </div>
              )}
            </div>
          )}
        </div>
      )}
    </div>
  )
}

// A named, collapsible section - the mechanism behind splitting the tab
// into "the answer" (hero card, always visible) and "the depth" (this),
// opened only on request instead of dumped on the page at equal weight.
function Disclosure({
  title,
  subtitle,
  defaultOpen = false,
  children,
}: {
  title: string
  subtitle?: string
  defaultOpen?: boolean
  children: ReactNode
}) {
  const [open, setOpen] = useState(defaultOpen)
  return (
    <div className="rounded-lg border border-line bg-panel">
      <button
        type="button"
        onClick={() => setOpen((o) => !o)}
        aria-expanded={open}
        className="flex w-full items-center justify-between gap-3 px-4 py-3 text-left"
      >
        <div>
          <div className="text-sm font-semibold text-ink">{title}</div>
          {subtitle && <div className="text-xs text-ink-faint">{subtitle}</div>}
        </div>
        <span
          aria-hidden="true"
          className={'shrink-0 text-ink-mute transition-transform ' + (open ? 'rotate-180' : '')}
        >
          &#9662;
        </span>
      </button>
      {open && <div className="border-t border-line p-4">{children}</div>}
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
  rows: { group: string; n: number; mae: number; bias: number; topRatedN: number; topRatedStrikePct: number | null }[]
  activeValue: string | null
  onSelect: (value: string) => void
}) {
  return (
    <div className="overflow-hidden rounded-lg border border-line bg-panel">
      <div className="border-b border-line px-3 py-2 text-xs font-semibold text-ink">{title}</div>
      <div className="max-h-64 overflow-y-auto">
        <table className="w-full text-xs">
          <thead className="sticky top-0 bg-panel">
            <tr className="text-left text-ink-mute">
              <th className="px-3 py-1.5 font-medium">Group</th>
              <th className="px-3 py-1.5 text-right font-medium">n</th>
              <th className="px-3 py-1.5 text-right font-medium">Top-rated strike</th>
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
                <td className="px-3 py-1 text-right font-mono">
                  {fmtPct(r.topRatedStrikePct)}
                  <span className="text-ink-faint"> (n={r.topRatedN})</span>
                </td>
                <td className="px-3 py-1 text-right font-mono">{r.mae.toFixed(1)}</td>
                <td className="px-3 py-1 text-right font-mono">{fmtSigned(r.bias)}</td>
              </tr>
            ))}
          </tbody>
        </table>
      </div>
    </div>
  )
}
