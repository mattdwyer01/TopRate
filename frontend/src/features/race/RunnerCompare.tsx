import type { Race, Runner } from '../../types/domain'
import type { EffectiveRunner } from '../../lib/raceModel'
import { fmtInt, fmtPrice, fmtWpr } from '../../lib/format'
import { spellPosition } from '../../lib/spellPosition'
import { modelPrice, type Signal } from '../../lib/betSignals'

interface RunnerCompareProps {
  race: Race
  runners: Runner[]
  effectiveByRunId: Record<string, EffectiveRunner>
  gapByRunId: Record<string, number | null>
  signalByRunId?: Record<string, Signal | null>
  onRemove: (runId: string) => void
  onOpen: (runId: string) => void
  onClear: () => void
}

// The best value in a row gets a subtle highlight. `higher` says which direction is better; ties highlight nothing.
type Row = { label: string; get: (r: Runner) => number | null; fmt: (v: number) => string; higher?: boolean }

const signed = (v: number) => `${v > 0 ? '+' : ''}${v.toFixed(1)}`

// Side-by-side view of 2 to 4 runners from one race. Reads the same effective (override-aware) figures the table shows.
export function RunnerCompare({ race, runners, effectiveByRunId, gapByRunId, signalByRunId, onRemove, onOpen, onClear }: RunnerCompareProps) {
  const eff = (r: Runner) => effectiveByRunId[r.runId]
  const rows: Row[] = [
    { label: 'Rating', get: (r) => eff(r)?.effectiveProjectedWpr ?? null, fmt: fmtWpr, higher: true },
    { label: 'WPR projection', get: (r) => eff(r)?.projectionWpr ?? null, fmt: fmtWpr, higher: true },
    { label: 'Behind top', get: (r) => gapByRunId[r.runId] ?? null, fmt: (v) => (v === 0 ? 'top' : v.toFixed(1)), higher: false },
    { label: 'Likely range +/-', get: (r) => r.projectionSd, fmt: (v) => (v * 0.67).toFixed(1), higher: false },
    { label: 'Base', get: (r) => r.baseWpr, fmt: fmtWpr, higher: true },
    { label: 'Adj', get: (r) => r.wprAdjustment, fmt: signed, higher: true },
    { label: 'SM (vs field)', get: (r) => eff(r)?.speedMapAdj ?? null, fmt: signed, higher: true },
    { label: 'Last run WPR', get: (r) => r.wprLast1, fmt: fmtWpr, higher: true },
    { label: 'Avg last 3', get: (r) => r.wprAvgLast3, fmt: fmtWpr, higher: true },
    { label: 'Peak WPR', get: (r) => r.peakWpr, fmt: fmtWpr, higher: true },
    { label: 'Model $', get: (r) => modelPrice(signalByRunId?.[r.runId]?.m), fmt: fmtPrice },
    { label: 'EV', get: (r) => signalByRunId?.[r.runId]?.e ?? null, fmt: (v) => v.toFixed(2), higher: true },
    { label: 'Fixed $', get: (r) => r.fixedWinPrice, fmt: fmtPrice },
    { label: 'Jockey win% (90d)', get: (r) => r.jockeyWinPct90d, fmt: (v) => `${v.toFixed(0)}%`, higher: true },
    { label: 'Trainer win% (1y)', get: (r) => r.trainerWinPct365d, fmt: (v) => `${v.toFixed(0)}%`, higher: true },
    { label: 'Weight', get: (r) => r.weightCarried, fmt: (v) => `${v}kg` },
    { label: 'Barrier', get: (r) => r.barrier, fmt: fmtInt },
    { label: 'Finish', get: (r) => r.finishPosition, fmt: fmtInt, higher: false },
  ]
  const best = (row: Row): number | null => {
    if (row.higher == null) return null
    const vals = runners.map((r) => row.get(r)).filter((v): v is number => v != null)
    if (vals.length < 2) return null
    const b = row.higher ? Math.max(...vals) : Math.min(...vals)
    return vals.filter((v) => v === b).length === 1 ? b : null
  }

  return (
    <section className="flex flex-col gap-2" aria-label="Runner comparison">
      <div className="flex items-center justify-between gap-2">
        <h3 className="text-sm font-semibold text-ink">Comparing {runners.length} runners</h3>
        <button type="button" onClick={onClear} className="text-xs text-ink-mute hover:text-ink">
          Clear
        </button>
      </div>
      <div className="overflow-x-auto rounded-lg border border-line bg-panel">
        <table className="w-full min-w-[420px] text-xs">
          <thead>
            <tr className="border-b border-line bg-bg text-left">
              <th className="sticky left-0 bg-bg px-2 py-1.5 font-medium text-ink-mute" />
              {runners.map((r) => (
                <th key={r.runId} className="px-2 py-1.5 text-right align-bottom font-medium text-ink">
                  <button type="button" onClick={() => onOpen(r.runId)} className="text-right hover:text-emerald-deep" title="Open runner detail">
                    {r.tabNumber}. {r.horse}
                  </button>
                  <button type="button" onClick={() => onRemove(r.runId)} aria-label={`Remove ${r.horse} from comparison`} className="ml-1 text-ink-faint hover:text-ink">
                    ✕
                  </button>
                  <div className="font-normal text-[11px] text-ink-faint">
                    {r.jockey} · {spellPosition(r.formHistory, race.date).label}
                    {r.predictedSettlingBand ? ` · ${r.predictedSettlingBand.toLowerCase()}` : ''}
                  </div>
                </th>
              ))}
            </tr>
          </thead>
          <tbody className="divide-y divide-line-soft">
            {rows.map((row) => {
              const vals = runners.map((r) => row.get(r))
              if (vals.every((v) => v == null)) return null
              const b = best(row)
              return (
                <tr key={row.label}>
                  <th scope="row" className="sticky left-0 bg-panel px-2 py-1 text-left font-normal text-ink-mute">
                    {row.label}
                  </th>
                  {vals.map((v, i) => (
                    <td key={runners[i].runId} className={`px-2 py-1 text-right font-mono ${b != null && v === b ? 'bg-emerald-bg font-semibold text-emerald-deep' : 'text-ink'}`}>
                      {v == null ? '-' : row.fmt(v)}
                    </td>
                  ))}
                </tr>
              )
            })}
          </tbody>
        </table>
      </div>
      <p className="text-[11px] text-ink-faint">Highlight marks the better figure in each row where one direction is clearly better. It is a reading aid, not a tip.</p>
    </section>
  )
}
