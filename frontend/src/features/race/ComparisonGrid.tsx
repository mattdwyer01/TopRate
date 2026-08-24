import type { FormHistoryEntry, Race, Runner } from '../../types/domain'
import { estimatePace, settleBand } from '../../lib/pace'

interface ComparisonGridProps {
  runner: Runner
  race: Race
  allRunners: Runner[]
}

function mean(values: number[]): number {
  return values.reduce((s, v) => s + v, 0) / values.length
}

function fmt(v: number | null, plusSign = false): string {
  if (v == null) return '—'
  const f = v.toFixed(1)
  return plusSign && v > 0 ? `+${f}` : f
}

interface CompTableProps {
  title: string
  todayLabel: string
  history: FormHistoryEntry[]
  matches: (r: FormHistoryEntry) => boolean
}

// Below this many runs at today's condition, "vs average" reads as precise
// when it's really 1-2 data points - the same small-sample trap that got
// the old per-venue track-bias chart pulled. Matches the >=3 threshold
// already used for the against-shape tendency figure elsewhere in the
// pipeline (toprate_daily.py's _last5 groupby).
const MIN_RUNS_TO_COMPARE = 3

// One comparison table: how this horse's WPR compares between runs matching
// today's condition (race speed / settling band / going / distance) and its
// full history - a "does this condition suit it" read, not a projection input.
function CompTable({ title, todayLabel, history, matches }: CompTableProps) {
  const allWpr = history.filter((r) => r.wpr != null).map((r) => r.wpr as number)
  const thisWpr = history.filter((r) => r.wpr != null && matches(r)).map((r) => r.wpr as number)
  const allMean = allWpr.length ? mean(allWpr) : null
  const thisMean = thisWpr.length ? mean(thisWpr) : null
  const variance = thisMean != null && allMean != null ? thisMean - allMean : null
  const enoughRuns = thisWpr.length >= MIN_RUNS_TO_COMPARE

  const varClass =
    variance != null
      ? variance >= 1
        ? 'text-emerald-deep font-medium'
        : variance <= -1
          ? 'text-rose font-medium'
          : 'text-ink-mute'
      : 'text-ink-mute'

  return (
    <div className="rounded-lg border border-line bg-panel p-2.5">
      <div className="mb-1 text-xs font-semibold text-ink">{title}</div>
      <table className="w-full text-xs">
        <thead>
          <tr className="text-ink-faint">
            <th className="text-left font-normal" />
            <th className="text-right font-normal">Runs</th>
            <th className="text-right font-normal">WPR</th>
          </tr>
        </thead>
        <tbody className="[&_td]:py-0.5">
          <tr className="font-medium text-ink">
            <td>This race ({todayLabel})</td>
            <td className="text-right font-mono">{thisWpr.length}</td>
            <td className="text-right font-mono">{fmt(thisMean)}</td>
          </tr>
          <tr className="text-ink-mute">
            <td>All races</td>
            <td className="text-right font-mono">{allWpr.length}</td>
            <td className="text-right font-mono">{fmt(allMean)}</td>
          </tr>
          {enoughRuns ? (
            <tr className={varClass}>
              <td>vs average</td>
              <td className="text-right font-mono">—</td>
              <td className="text-right font-mono">{fmt(variance, true)}</td>
            </tr>
          ) : (
            <tr className="text-ink-faint italic">
              <td colSpan={3} className="pt-0.5">
                Only {thisWpr.length} run{thisWpr.length === 1 ? '' : 's'} at this condition - too few to
                compare reliably.
              </td>
            </tr>
          )}
        </tbody>
      </table>
    </div>
  )
}

// How this horse's WPR compares under today's race speed and settling
// position vs. its full history under other conditions - ported from the
// old dashboard's compTable() calls, trimmed to just these two. Going and
// Distance used to have their own tiles here too, but they sliced the
// exact same condition (same ±10%-distance/going-band definitions) already
// shown in CareerStats above, just against career average instead of base
// rating - duplicate information, dropped in favour of owning it there.
export function ComparisonGrid({ runner, race, allRunners }: ComparisonGridProps) {
  const history = runner.formHistory
  if (!history.length) return null

  const pace = estimatePace(race, allRunners)
  const settleToday = runner.predictedSettlingBand || 'unknown'

  return (
    <div>
      <div className="mb-1 text-sm font-semibold text-ink">How today's shape suits this horse</div>
      <div className="grid grid-cols-1 gap-2 sm:grid-cols-2">
        <CompTable
          title="Race speed"
          todayLabel={pace.tempoBucket}
          history={history}
          matches={(r) => r.tempo === pace.tempoBucket}
        />
        <CompTable
          title="Settling position"
          todayLabel={settleToday}
          history={history}
          matches={(r) => settleBand(r.relativeSettlePosition) === settleToday}
        />
      </div>
    </div>
  )
}
