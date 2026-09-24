import { useMemo } from 'react'
import type { Race } from '../../types/domain'
import { blendRace, useRacingModel } from '../../lib/racingModel'

interface RacingModelPanelProps {
  race: Race
  scratched: Set<string>
}

const price = (v: number | null | undefined) => (v == null ? '-' : `$${v >= 100 ? v.toFixed(0) : v.toFixed(2)}`)
const pct = (v: number | null | undefined) => (v == null ? '-' : `${Math.round(v * 100)}%`)
const signed = (v: number | null | undefined, d = 1) => (v == null ? '-' : `${v > 0 ? '+' : ''}${v.toFixed(d)}`)

// Racing Model layer (see lib/racingModel.ts): an independent model's rating, fair prices and speed map
// for this race, shown under TopRate's own panels. Renders nothing when the race has no racing-model
// projection (other states, or the file not loaded).
export function RacingModelPanel({ race, scratched }: RacingModelPanelProps) {
  const rm = useRacingModel()
  const blend = useMemo(() => (rm ? blendRace(race, rm, scratched) : {}), [race, rm, scratched])
  if (!rm) return null
  const meta = rm.races[race.raceId]
  const rows = race.runners
    .filter((r) => !scratched.has(r.runId) && rm.runners[r.runId])
    .map((r) => ({ runner: r, m: rm.runners[r.runId], b: blend[r.runId] }))
  if (!rows.length) return null
  rows.sort((x, y) => (y.m.r ?? -1e9) - (x.m.r ?? -1e9))
  const settleRank = new Map(
    [...rows].sort((x, y) => (x.m.s ?? 1) - (y.m.s ?? 1)).map((x, i) => [x.runner.runId, i + 1] as const),
  )
  const resulted = rows.some((x) => x.runner.finishPosition != null)
  const pace = meta?.pace

  return (
    <div className="rounded-lg border border-line bg-panel p-3">
      <div className="flex flex-wrap items-baseline justify-between gap-2">
        <div className="text-sm font-semibold text-ink">Racing Model</div>
        <div className="text-[11px] text-ink-faint">
          projected {meta?.on ?? '-'}, model trained to {rm.trainEnd}
        </div>
      </div>
      {pace && (
        <div className="mt-1.5 flex flex-wrap items-center gap-3 text-xs text-ink-soft">
          <span>Pace {signed(meta?.pv)} vs distance avg</span>
          <span>slow {pct(pace[0])}</span>
          <span>even {pct(pace[1])}</span>
          <span>fast {pct(pace[2])}</span>
        </div>
      )}
      <div className="mt-2 overflow-x-auto">
        <table className="w-full text-xs tabular-nums">
          <thead>
            <tr className="border-b border-line text-ink-mute">
              <th className="py-1 pr-2 text-left font-semibold">Horse</th>
              <th className="px-1.5 text-right font-semibold">Rating</th>
              <th className="px-1.5 text-right font-semibold">vs field</th>
              <th className="px-1.5 text-right font-semibold">Settle</th>
              <th className="px-1.5 text-right font-semibold">Leads</th>
              <th className="px-1.5 text-right font-semibold">Pos val</th>
              <th className="px-1.5 text-right font-semibold">Model $</th>
              <th className="px-1.5 text-right font-semibold">Blend $</th>
              <th className="px-1.5 text-right font-semibold">Fixed $</th>
              <th className="px-1.5 text-right font-semibold">Edge</th>
              {resulted && <th className="pl-1.5 text-right font-semibold">FP</th>}
            </tr>
          </thead>
          <tbody>
            {rows.map(({ runner, m, b }, i) => {
              const edge = b?.edge ?? null
              return (
                <tr key={runner.runId} className="border-b border-line-soft">
                  <td className="py-1 pr-2 text-left text-ink">
                    <span className="text-ink-faint">{i + 1}.</span> {runner.horse}
                    <span className="text-ink-faint"> ({runner.barrier ?? '-'})</span>
                  </td>
                  <td className="px-1.5 text-right font-semibold text-ink">{m.r == null ? '-' : m.r.toFixed(1)}</td>
                  <td className={`px-1.5 text-right ${m.v != null && m.v > 0 ? 'text-emerald-deep' : m.v != null && m.v < 0 ? 'text-rose' : 'text-ink-soft'}`}>
                    {signed(m.v)}
                  </td>
                  <td className="px-1.5 text-right text-ink-soft">{settleRank.get(runner.runId)}</td>
                  <td className="px-1.5 text-right text-ink-soft">{pct(m.l)}</td>
                  <td className={`px-1.5 text-right ${m.pf ? 'font-semibold text-indigo' : 'text-ink-soft'}`}>
                    {m.pf ? '◆ ' : ''}
                    {signed(m.pv)}
                  </td>
                  <td className="px-1.5 text-right text-ink-soft">{price(m.p ? 1 / m.p : null)}</td>
                  <td className="px-1.5 text-right text-ink">{price(b?.blendPrice)}</td>
                  <td className="px-1.5 text-right text-ink-soft">{price(runner.fixedWinPrice)}</td>
                  <td className={`px-1.5 text-right ${edge != null && edge > 0 ? 'font-semibold text-emerald-deep' : 'text-ink-faint'}`}>
                    {edge == null ? '-' : `${edge > 0 ? '▲ ' : ''}${Math.round(edge * 100)}%`}
                  </td>
                  {resulted && <td className="pl-1.5 text-right font-semibold text-ink">{runner.finishPosition ?? '-'}</td>}
                </tr>
              )
            })}
          </tbody>
        </table>
      </div>
      <div className="mt-1.5 text-[11px] text-ink-faint">
        Rating = projected WPR; Model $ is the model alone, Blend $ combines it with the current fixed price.
        Edge = blend probability x fixed price - 1. Settle = projected position at the 800m (1 = leader). Pos val =
        what the projected position, width and pace are worth (WPR points vs the race); ◆ = top 10%, a group
        that has won more often than its price implied in testing.
      </div>
    </div>
  )
}
