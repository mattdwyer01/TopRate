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

function vsBaseClass(v: number | null): string {
  if (v == null) return 'text-ink-mute'
  if (v >= 1) return 'text-emerald-deep font-medium'
  if (v <= -1) return 'text-rose font-medium'
  return 'text-ink-mute'
}

// Career/condition WPR summary shown up top in the runner detail - peak,
// average and median across career plus a handful of conditions relevant to
// today's race, each read against the model's own base rating (is this
// horse being asked to do something above or below what it normally does).
// Distinct from ComparisonGrid further down, which asks a narrower question
// (does today's specific pace/settle/going/distance suit it).
export function CareerStats({ runner, race }: CareerStatsProps) {
  if (!runner.formHistory.length) return null
  const rows = computeCareerStats(runner, race)

  return (
    <div className="overflow-x-auto rounded-lg border border-line bg-panel p-2">
      <div className="mb-0.5 text-xs font-semibold text-ink">WPR by career &amp; condition</div>
      <table className="w-full max-w-md text-xs">
        <thead>
          <tr className="text-ink-faint">
            <th className="text-left font-normal" />
            <th className="text-right font-normal">Peak</th>
            <th className="text-right font-normal">Avg</th>
            <th className="text-right font-normal">vs Base</th>
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
              <td className={`text-right font-mono ${vsBaseClass(row.vsBase)}`}>{fmtSigned(row.vsBase)}</td>
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
