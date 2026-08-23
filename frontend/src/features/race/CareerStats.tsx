import type { Race, Runner } from '../../types/domain'
import { computeCareerStats } from '../../lib/careerStats'
import { Sparkline } from '../../components/Sparkline'

interface CareerStatsProps {
  runner: Runner
  race: Race
}

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
// is itself a first/second-up run). The vs-career-avg read is the same
// calculation as the backend's own_distance/own_going adjustment terms
// (see AdjustmentBreakdown), just unshrunk and over more conditions than
// the 6 that actually feed the projection. Distinct from ComparisonGrid
// further down, which asks a narrower question (does today's specific
// pace/settle suit it).
export function CareerStats({ runner, race }: CareerStatsProps) {
  if (!runner.formHistory.length) return null
  // Rows with zero matching runs (e.g. "This prep" for a first-up horse)
  // show nothing but dashes - the em-dash IS the information, so drop the
  // row rather than spend a full line saying "no data" (a first-up horse's
  // empty prep is already obvious from the recent-runs table's spell marker).
  const rows = computeCareerStats(runner, race).filter((row) => row.runs > 0)

  return (
    <div className="overflow-x-auto rounded-lg border border-line bg-panel p-2">
      <div className="mb-0.5 text-xs font-semibold text-ink">WPR by career &amp; condition</div>
      <p className="mb-1 text-[11px] text-ink-faint">
        Avg vs career average - the same read as "What's driving the adjustment" below, over more conditions.
      </p>
      <table className="w-full max-w-md text-xs">
        <thead>
          <tr className="text-ink-faint">
            <th className="text-left font-normal" />
            <th className="text-right font-normal">Peak</th>
            <th className="text-right font-normal">Avg</th>
            <th className="text-right font-normal">vs Career</th>
            <th className="pl-2 text-right font-normal">Trend</th>
          </tr>
        </thead>
        <tbody className="[&_td]:py-0 [&_td]:leading-5">
          {rows.map((row) => (
            <tr key={row.label} className={row.runs === 0 ? 'text-ink-faint italic' : 'text-ink'}>
              <td className="whitespace-nowrap">
                {row.label} <span className="text-ink-faint">&middot; {row.runs}</span>
              </td>
              <td className="text-right font-mono">{fmt(row.peak)}</td>
              <td className="text-right font-mono">{fmt(row.avg)}</td>
              <td className={`text-right font-mono ${vsCareerAvgClass(row.vsCareerAvg, row.runs)}`}>
                {fmtSigned(row.vsCareerAvg)}
              </td>
              <td className="py-0.5 pl-2 text-right">
                <Sparkline values={row.trend} />
              </td>
            </tr>
          ))}
        </tbody>
      </table>
    </div>
  )
}
