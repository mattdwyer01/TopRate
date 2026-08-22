import type { FormHistoryEntry, Race, Runner } from '../../types/domain'
import { estimatePace, goingBand, settleBand } from '../../lib/pace'

interface ComparisonGridProps {
  runner: Runner
  race: Race
  allRunners: Runner[]
}

function mean(values: number[]): number {
  return values.reduce((s, v) => s + v, 0) / values.length
}

function stddev(values: number[], m: number): number | null {
  if (values.length < 2) return null
  const variance = values.reduce((s, v) => s + (v - m) * (v - m), 0) / (values.length - 1)
  return Math.sqrt(variance)
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

// Below this many runs at today's condition, "vs average" and "Consistency
// (SD)" read as precise when they're really 1-2 data points - the same
// small-sample trap that got the old per-venue track-bias chart pulled.
// Matches the >=3 threshold already used for the against-shape tendency
// figure elsewhere in the pipeline (toprate_daily.py's _last5 groupby).
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
  const thisSd = thisWpr.length ? stddev(thisWpr, thisMean as number) : null
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
            <>
              <tr className={varClass}>
                <td>vs average</td>
                <td className="text-right font-mono">—</td>
                <td className="text-right font-mono">{fmt(variance, true)}</td>
              </tr>
              <tr className="text-ink-mute">
                <td>Consistency (SD)</td>
                <td className="text-right font-mono">—</td>
                <td className="text-right font-mono">{fmt(thisSd)}</td>
              </tr>
            </>
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

// 2x2 grid: how this horse's WPR compares under today's race speed,
// settling band, going, and distance vs. its full history under other
// conditions - ported from the old dashboard's four compTable() calls.
export function ComparisonGrid({ runner, race, allRunners }: ComparisonGridProps) {
  const history = runner.formHistory
  if (!history.length) return null

  const pace = estimatePace(race, allRunners)
  const settleToday = runner.predictedSettlingBand || 'unknown'
  const goingToday = goingBand(race.going)
  const distLo = race.distance * 0.9
  const distHi = race.distance * 1.1

  return (
    <div>
      <div className="mb-1 text-sm font-semibold text-ink">How conditions suit this horse</div>
      <div className="grid grid-cols-1 gap-2 sm:grid-cols-2 lg:grid-cols-4">
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
        <CompTable
          title="Going"
          todayLabel={goingToday || 'unknown'}
          history={history}
          matches={(r) => goingBand(r.going) === goingToday}
        />
        <CompTable
          title="Distance"
          todayLabel={`${race.distance}m`}
          history={history}
          matches={(r) => r.distance >= distLo && r.distance <= distHi}
        />
      </div>
    </div>
  )
}
