import { useMemo, useState } from 'react'
import type { Race, Runner } from '../../types/domain'
import { blendRace, useRacingModel, type RMBlend, type RMRunner } from '../../lib/racingModel'

interface RacingModelPanelProps {
  race: Race
  scratched: Set<string>
}

const price = (v: number | null | undefined) => (v == null ? '-' : `$${v >= 100 ? v.toFixed(0) : v.toFixed(2)}`)
const pct = (v: number | null | undefined) => (v == null ? '-' : `${Math.round(v * 100)}%`)
const signed = (v: number | null | undefined, d = 1) => (v == null ? '-' : `${v > 0 ? '+' : ''}${v.toFixed(d)}`)

interface Row {
  runner: Runner
  m: RMRunner
  b: RMBlend | undefined
  settleRank: number
}

type Key = 'horse' | 'r' | 'v' | 'settle' | 'l' | 'pv' | 'model' | 'blend' | 'fixed' | 'edge' | 'fp'

// Sort value per column (null sorts last either way) and the direction a first click uses: best first.
const COLS: { key: Key; label: string; title: string; dir: 'asc' | 'desc'; value: (x: Row) => number | string | null }[] = [
  { key: 'horse', label: 'Horse', title: 'Saddlecloth, horse (barrier)', dir: 'asc', value: (x) => x.runner.tabNumber ?? null },
  { key: 'r', label: 'Rtg', title: 'Projected rating (WPR points)', dir: 'desc', value: (x) => x.m.r },
  { key: 'v', label: '±Fld', title: 'Rating vs the field average', dir: 'desc', value: (x) => x.m.v },
  { key: 'settle', label: 'Set', title: 'Projected position at the 800m (1 = leader)', dir: 'asc', value: (x) => x.settleRank },
  { key: 'l', label: 'Lead', title: 'Chance of leading', dir: 'desc', value: (x) => x.m.l },
  { key: 'pv', label: 'PosV', title: 'Position value: WPR points the projected position, width and pace are worth vs the race; ◆ = top 10%', dir: 'desc', value: (x) => x.m.pv ?? null },
  { key: 'model', label: 'Mdl $', title: 'Model alone (no market input)', dir: 'asc', value: (x) => (x.m.p ? 1 / x.m.p : null) },
  { key: 'blend', label: 'Bld $', title: 'Model blended with the current fixed price', dir: 'asc', value: (x) => x.b?.blendPrice ?? null },
  { key: 'fixed', label: 'Fix $', title: 'Current TAB fixed price', dir: 'asc', value: (x) => x.runner.fixedWinPrice ?? null },
  { key: 'edge', label: 'Edge', title: 'Blend probability x fixed price - 1', dir: 'desc', value: (x) => x.b?.edge ?? null },
  { key: 'fp', label: 'FP', title: 'Finish position', dir: 'asc', value: (x) => x.runner.finishPosition ?? null },
]

// Racing Model layer (see lib/racingModel.ts): an independent model's rating, fair prices and position
// value for this race, shown under TopRate's own panels. Its speed map is the "Racing Model" source of the
// speed map above. Renders nothing when the race has no racing-model projection (other states, or the file
// not loaded). Every column sorts (tap the header; tap again to reverse). Rows stay on one line with the
// horse column pinned, so on a phone the numbers scroll sideways under the names instead of wrapping.
export function RacingModelPanel({ race, scratched }: RacingModelPanelProps) {
  const rm = useRacingModel()
  const blend = useMemo(() => (rm ? blendRace(race, rm, scratched) : {}), [race, rm, scratched])
  const [sort, setSort] = useState<{ key: Key; dir: 'asc' | 'desc' }>({ key: 'r', dir: 'desc' })
  if (!rm) return null
  const meta = rm.races[race.raceId]
  const base = race.runners
    .filter((r) => !scratched.has(r.runId) && rm.runners[r.runId])
    .map((r) => ({ runner: r, m: rm.runners[r.runId], b: blend[r.runId] }))
  if (!base.length) return null
  const settleRank = new Map(
    [...base].sort((x, y) => (x.m.s ?? 1) - (y.m.s ?? 1)).map((x, i) => [x.runner.runId, i + 1] as const),
  )
  const resulted = base.some((x) => x.runner.finishPosition != null)
  const cols = COLS.filter((c) => c.key !== 'fp' || resulted)
  const col = cols.find((c) => c.key === sort.key) ?? cols[1]
  const rows: Row[] = base
    .map((x) => ({ ...x, settleRank: settleRank.get(x.runner.runId) ?? 99 }))
    .sort((x, y) => {
      const a = col.value(x)
      const b = col.value(y)
      if (a == null || b == null) return a == null ? (b == null ? 0 : 1) : -1
      const d = typeof a === 'string' || typeof b === 'string' ? String(a).localeCompare(String(b)) : a - b
      return sort.dir === 'asc' ? d : -d
    })
  const pace = meta?.pace

  function onSort(c: (typeof COLS)[number]) {
    setSort((s) => (s.key === c.key ? { key: c.key, dir: s.dir === 'asc' ? 'desc' : 'asc' } : { key: c.key, dir: c.dir }))
  }

  const cell = 'px-1.5 py-1.5 text-right'
  return (
    <div className="rounded-lg border border-line bg-panel p-3">
      <div className="flex flex-wrap items-baseline justify-between gap-x-2">
        <div className="text-sm font-semibold text-ink">Racing Model</div>
        <div className="text-[11px] text-ink-faint">
          projected {meta?.on ?? '-'} · trained to {rm.trainEnd}
        </div>
      </div>
      {pace && (
        <div className="mt-1 flex flex-wrap items-center gap-x-3 text-xs text-ink-soft">
          <span>Pace {signed(meta?.pv)} vs avg</span>
          <span>slow {pct(pace[0])}</span>
          <span>even {pct(pace[1])}</span>
          <span>fast {pct(pace[2])}</span>
        </div>
      )}
      <div className="-mx-3 mt-2 overflow-x-auto">
        <table className="w-full whitespace-nowrap text-xs tabular-nums">
          <thead>
            <tr className="border-b border-line text-ink-mute">
              {cols.map((c) => (
                <th
                  key={c.key}
                  title={c.title}
                  aria-sort={sort.key === c.key ? (sort.dir === 'asc' ? 'ascending' : 'descending') : 'none'}
                  className={`p-0 font-semibold ${c.key === 'horse' ? 'sticky left-0 z-10 bg-panel text-left' : 'text-right'}`}
                >
                  <button
                    type="button"
                    onClick={() => onSort(c)}
                    className={`w-full py-1.5 transition-colors hover:text-ink ${
                      c.key === 'horse' ? 'pl-3 pr-1.5 text-left' : 'px-1.5 text-right'
                    } ${sort.key === c.key ? 'text-emerald-deep' : ''}`}
                  >
                    {c.label}
                    {sort.key === c.key && (sort.dir === 'asc' ? ' ↑' : ' ↓')}
                  </button>
                </th>
              ))}
            </tr>
          </thead>
          <tbody>
            {rows.map(({ runner, m, b, settleRank: sr }) => {
              const edge = b?.edge ?? null
              return (
                <tr key={runner.runId} className="border-b border-line-soft">
                  <td className="sticky left-0 z-10 max-w-[9.5rem] truncate bg-panel py-1.5 pl-3 pr-1.5 text-left text-ink sm:max-w-none">
                    <span className="text-ink-faint">{runner.tabNumber}.</span> {runner.horse}
                    <span className="text-ink-faint"> ({runner.barrier ?? '-'})</span>
                  </td>
                  <td className={`${cell} font-semibold text-ink`}>{m.r == null ? '-' : m.r.toFixed(1)}</td>
                  <td className={`${cell} ${m.v != null && m.v > 0 ? 'text-emerald-deep' : m.v != null && m.v < 0 ? 'text-rose' : 'text-ink-soft'}`}>
                    {signed(m.v)}
                  </td>
                  <td className={`${cell} text-ink-soft`}>{sr}</td>
                  <td className={`${cell} text-ink-soft`}>{pct(m.l)}</td>
                  <td className={`${cell} ${m.pf ? 'font-semibold text-indigo' : 'text-ink-soft'}`}>
                    {m.pf ? '◆' : ''}
                    {signed(m.pv)}
                  </td>
                  <td className={`${cell} text-ink-soft`}>{price(m.p ? 1 / m.p : null)}</td>
                  <td className={`${cell} text-ink`}>{price(b?.blendPrice)}</td>
                  <td className={`${cell} text-ink-soft`}>{price(runner.fixedWinPrice)}</td>
                  <td className={`${cell} ${edge != null && edge > 0 ? 'font-semibold text-emerald-deep' : 'text-ink-faint'} ${resulted ? '' : 'pr-3'}`}>
                    {edge == null ? '-' : `${edge > 0 ? '▲' : ''}${Math.round(edge * 100)}%`}
                  </td>
                  {resulted && <td className={`${cell} pr-3 font-semibold text-ink`}>{runner.finishPosition ?? '-'}</td>}
                </tr>
              )
            })}
          </tbody>
        </table>
      </div>
      <div className="mt-1.5 text-[11px] leading-snug text-ink-faint">
        Tap a header to sort. Rtg = projected WPR; ±Fld = vs the field average; Set = projected position at the 800m
        (1 = leader); Lead = chance of leading; PosV = what the projected position, width and pace are worth (WPR
        points vs the race), ◆ = top 10%, a group that has won more often than its price implied in testing; Mdl $ =
        model alone; Bld $ = model blended with the current fixed price; Edge = blend probability x fixed price - 1.
        The Racing Model speed map is the Racing Model option on the speed map above.
      </div>
    </div>
  )
}
