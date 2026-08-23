import type { Race, Runner } from '../../types/domain'
import { computeCareerStats } from '../../lib/careerStats'
import { ADJUSTMENT_LABELS } from '../../lib/adjustmentLabels'
import { Sparkline } from '../../components/Sparkline'

interface CareerStatsProps {
  runner: Runner
  race: Race
}

const MIN_ADJ_SHOWN = 0.05

function fmt(v: number | null): string {
  return v == null ? '—' : v.toFixed(1)
}

function fmtSigned(v: number | null): string {
  if (v == null) return '—'
  const f = v.toFixed(1)
  return v > 0 ? `+${f}` : f
}

// Same threshold and reasoning as ComparisonGrid's MIN_RUNS_TO_COMPARE -
// below this many runs, "vs Career" is 1-2 data points dressed up as a
// confident read. Below the threshold the figure still shows, just without
// the colour that implies a reliable signal.
const MIN_RUNS_TO_COLOR = 3

function vsCareerAvgClass(v: number | null, runs: number): string {
  if (v == null || runs < MIN_RUNS_TO_COLOR) return 'text-ink-mute'
  if (v >= 1) return 'text-emerald-deep font-medium'
  if (v <= -1) return 'text-rose font-medium'
  return 'text-ink-mute'
}

// Career/condition WPR summary shown up top in the runner detail - peak and
// average-vs-career-average across career plus a handful of conditions
// relevant to today's race (including first/second-up history when today
// is itself a first/second-up run), plus - inline, in an "Adj" column - the
// shrunk/capped version of that same delta for whichever rows actually feed
// the projection (own_distance/own_going/own_first_up/own_second_up). This
// used to be two separate tables (this one unshrunk, a second one showing
// the model's applied adjustment) side by side; folding the applied
// adjustment into the matching row removes the duplicate table and lets a
// reader compare "how it's actually run there" against "how much that
// counted" in one glance. Distinct from ComparisonGrid further down, which
// asks a narrower question (does today's specific pace/settle suit it).
export function CareerStats({ runner, race }: CareerStatsProps) {
  if (!runner.formHistory.length) return null
  // Rows with zero matching runs (e.g. "This prep" for a first-up horse)
  // show nothing but dashes - the em-dash IS the information, so drop the
  // row rather than spend a full line saying "no data" (a first-up horse's
  // empty prep is already obvious from the recent-runs table's spell marker).
  const rows = computeCareerStats(runner, race).filter((row) => row.runs > 0)

  const breakdown = runner.adjustmentBreakdown
  const shownAdjKeys = new Set(rows.map((r) => r.adjKey).filter(Boolean))
  // own_trend/own_long_spell have no matching career-stat row (there's no
  // "trend" or "long spell" condition to bucket runs by) - surface them as
  // a compact footer instead of leaving them unexplained.
  const otherAdj = breakdown
    ? Object.entries(breakdown).filter(
        ([key, v]) => key !== 'baseline' && !shownAdjKeys.has(key) && Math.abs(v) >= MIN_ADJ_SHOWN,
      )
    : []

  return (
    <div className="overflow-x-auto rounded-lg border border-line bg-panel p-3 sm:p-4">
      <div className="mb-0.5 text-xs font-semibold text-ink sm:text-sm">WPR by career &amp; condition</div>
      <p className="mb-2 text-[11px] text-ink-faint sm:text-xs">
        Avg vs its own career average, and (where it feeds the rating) the shrunk adjustment actually applied.
      </p>
      {/* table-fixed + explicit column widths so this stretches to fill the
          card on wide screens instead of shrink-wrapping to a fixed max-width
          and leaving a dead gap beside it (that gap used to hold the separate
          adjustment-breakdown table, now folded into the Adj column below). */}
      <table className="w-full table-fixed text-xs sm:text-sm">
        <colgroup>
          <col className="w-[30%]" />
          <col className="w-[14%]" />
          <col className="w-[14%]" />
          <col className="w-[16%]" />
          <col className="w-[12%]" />
          <col />
        </colgroup>
        <thead>
          <tr className="border-b border-line-soft text-ink-faint">
            <th className="pb-1.5 text-left font-normal" />
            <th className="pb-1.5 text-right font-normal">Peak</th>
            <th className="pb-1.5 text-right font-normal">Avg</th>
            <th className="pb-1.5 pl-2 text-right font-normal">vs Career</th>
            <th className="pb-1.5 pl-2 text-right font-normal">Adj</th>
            <th className="pb-1.5 pl-3 text-right font-normal">Trend</th>
          </tr>
        </thead>
        <tbody className="[&_td]:py-1.5 [&_td]:leading-5">
          {rows.map((row) => {
            const adjV = row.adjKey ? breakdown?.[row.adjKey] : undefined
            const isCareer = row.label === 'Career'
            return (
              <tr
                key={row.label}
                className={`border-b border-line-soft/60 last:border-0 ${
                  isCareer ? 'font-medium text-ink' : 'text-ink'
                }`}
              >
                <td className="whitespace-nowrap">
                  {row.label} <span className="font-normal text-ink-faint">&middot; {row.runs}</span>
                </td>
                <td className="text-right font-mono">{fmt(row.peak)}</td>
                <td className="text-right font-mono">{fmt(row.avg)}</td>
                <td className={`pl-2 text-right font-mono ${vsCareerAvgClass(row.vsCareerAvg, row.runs)}`}>
                  {fmtSigned(row.vsCareerAvg)}
                </td>
                <td className="pl-2 text-right font-mono">
                  {adjV != null && Math.abs(adjV) >= MIN_ADJ_SHOWN ? (
                    <span className={adjV > 0 ? 'text-emerald-deep' : 'text-rose'}>{fmtSigned(adjV)}</span>
                  ) : (
                    <span className="text-ink-faint">—</span>
                  )}
                </td>
                <td className="pl-3 text-right">
                  <Sparkline values={row.trend} width={72} height={20} />
                </td>
              </tr>
            )
          })}
        </tbody>
      </table>
      {otherAdj.length > 0 && (
        <p className="mt-1.5 text-[11px] text-ink-faint">
          Also factored:{' '}
          {otherAdj
            .map(
              ([key, v]) =>
                `${ADJUSTMENT_LABELS[key] ?? key} ${v > 0 ? '+' : ''}${v.toFixed(2)}`,
            )
            .join(' · ')}
        </p>
      )}
    </div>
  )
}
