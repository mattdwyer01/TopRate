import { useMemo, useState } from 'react'
import type { Race, Runner } from '../../types/domain'
import {
  DISTANCE_LABELS,
  GOING_LABELS,
  PACE_LABELS,
  RAIL_LABELS,
  aggregate,
  filterRows,
  raceConditions,
  smoothA2E,
  styleIndex,
  useVenueDraw,
  widen,
  type Cell,
  type Conditions,
} from '../../lib/drawStyle'

// Draw and style card (Oct 2026): how runners from each barrier and running style have won at this venue against what their starting price implied (A2E, 1.00 = as expected),
// for this race's distance, rail, going and number of leaders, with this race's runners marked. A reading aid: the price already covers draw and style, so almost no cell is beyond chance.
const ROWS: { label: string; range: [number, number] }[] = [
  { label: '1-3', range: [1, 3] },
  { label: '4-7', range: [4, 7] },
  { label: '8+', range: [8, 16] },
]
const COLS: { label: string; styles: number[] }[] = [
  { label: 'Forward', styles: [0, 1] },
  { label: 'Midfield', styles: [2, 3] },
  { label: 'Back', styles: [4, 5] },
]
const KEYS = ['d', 'r', 'g', 'p'] as const
const FIELD_LABEL = { d: 'Distance', r: 'Rail', g: 'Going', p: 'Race pace' } as const
const LABELS = { d: DISTANCE_LABELS, r: RAIL_LABELS, g: GOING_LABELS, p: PACE_LABELS } as const
const DROP_NAME = { p: 'pace', g: 'going', r: 'rail' } as const

function tint(c: Cell): string {
  const d = Math.max(-1, Math.min(1, (smoothA2E(c) - 1) / 0.4))
  return d >= 0 ? `rgba(5,150,105,${(d * 0.45).toFixed(2)})` : `rgba(220,38,38,${(-d * 0.45).toFixed(2)})`
}

const fmtNums = (a: number[]) => [...a].sort((x, y) => x - y).map((n) => `#${n}`).join(' ')

export function DrawStyleCard({ race, runners }: { race: Race; runners: Runner[] }) {
  const data = useVenueDraw(race.venue)
  const [open, setOpen] = useState(false)
  const [showFilters, setShowFilters] = useState(false)
  const [showInfo, setShowInfo] = useState(false)
  const [manual, setManual] = useState<Conditions | null>(null)

  const raceCond = useMemo(() => raceConditions(race, runners), [race, runners])
  const view = useMemo(() => {
    if (!data) return null
    const w = manual ? { cond: manual, dropped: [] as ('p' | 'g' | 'r')[] } : widen(data.rows, raceCond)
    const rows = filterRows(data.rows, w.cond)
    const marks = new Map<string, number[]>()
    const noHistory: number[] = []
    for (const r of runners) {
      if (r.styleAvg == null || r.barrier == null) {
        noHistory.push(r.tabNumber)
        continue
      }
      const ri = ROWS.findIndex((x) => r.barrier! >= x.range[0] && r.barrier! <= x.range[1])
      const si = styleIndex(r.styleAvg)
      const ci = COLS.findIndex((x) => x.styles.includes(si))
      const k = `${ri}|${ci}`
      marks.set(k, [...(marks.get(k) ?? []), r.tabNumber])
    }
    const cells = ROWS.map((row) => COLS.map((col) => aggregate(rows, row.range, col.styles)))
    const up: number[] = []
    const dn: number[] = []
    let sig = 0
    cells.forEach((line, ri) =>
      line.forEach((c, ci) => {
        const m = marks.get(`${ri}|${ci}`)
        if (c.n >= 15 && m) {
          const s = smoothA2E(c)
          if (s > 1.1) up.push(...m)
          else if (s < 0.9) dn.push(...m)
          if (Math.abs(c.z) >= 2) sig++
        }
      }),
    )
    return { ...w, rows, marks, cells, up, dn, sig, noHistory }
  }, [data, raceCond, manual, runners])

  if (!data || !view || runners.filter((r) => r.styleAvg != null).length < 3) return null

  const cond = view.cond
  const total = view.rows.length
  const dg = cond.d ?? raceCond.d
  const slope = (dg != null ? data.rating[String(dg)] : undefined) ?? data.rating.all
  const gates = Math.max(0, ...runners.map((r) => r.barrier ?? 0))
  const used = KEYS.filter((k) => cond[k] !== null).map((k) => (LABELS[k] as readonly string[])[cond[k] as number])
  const summary =
    (view.sig ? `${view.sig} cell${view.sig > 1 ? 's' : ''} beyond chance` : 'No clear edge') +
    (view.up.length ? ` · above expected ${fmtNums(view.up)}` : '') +
    (view.dn.length ? ` · below ${fmtNums(view.dn)}` : '')

  const setCond = (k: (typeof KEYS)[number], v: string) => setManual({ ...(manual ?? cond), [k]: v === '' ? null : Number(v) })

  return (
    <section className="rounded-lg border border-line bg-panel shadow-[var(--shadow-1)]" aria-label="Draw and style">
      <button type="button" className="flex w-full items-center gap-2.5 px-3 py-2 text-left" aria-expanded={open} onClick={() => setOpen(!open)}>
        <span className="flex-none text-sm font-semibold text-ink">Draw and style</span>
        <span className="min-w-0 flex-1 truncate text-xs text-ink-mute">{summary}</span>
        <span className={`flex-none text-ink-mute transition-transform ${open ? 'rotate-180' : ''}`} aria-hidden="true">
          ⌄
        </span>
      </button>
      {open && (
        <div className="border-t border-line px-3 pb-2.5 pt-2">
          {showFilters && (
            <div className="mb-2 flex flex-wrap items-end gap-2 rounded-md bg-bg p-2">
              {KEYS.map((k) => (
                <label key={k} className="flex flex-col gap-0.5 text-[10px] font-medium uppercase tracking-wide text-ink-mute">
                  {FIELD_LABEL[k]}
                  <select className="rounded border border-line bg-panel px-1.5 py-1 text-xs normal-case text-ink" value={cond[k] ?? ''} onChange={(e) => setCond(k, e.target.value)}>
                    <option value="">Any</option>
                    {(LABELS[k] as readonly string[]).map((l, i) => (
                      <option key={l} value={i}>
                        {l}
                      </option>
                    ))}
                  </select>
                </label>
              ))}
              <button type="button" className="text-xs text-emerald-deep underline" onClick={() => setManual(null)}>
                Reset to this race
              </button>
            </div>
          )}
          <div className="grid gap-x-4 gap-y-2 sm:grid-cols-[minmax(0,260px)_minmax(0,1fr)]">
            <div className="grid grid-cols-[28px_repeat(3,minmax(0,1fr))] gap-0.5">
              <div />
              {COLS.map((c) => (
                <div key={c.label} className="text-center text-xs font-semibold text-ink-mute">
                  {c.label}
                </div>
              ))}
              {ROWS.map((row, ri) => (
                <div key={row.label} className="contents">
                  <div className="flex items-center text-xs font-semibold text-ink-mute">{row.label}</div>
                  {COLS.map((col, ci) => {
                    const c = view.cells[ri]![ci]!
                    const m = view.marks.get(`${ri}|${ci}`) ?? []
                    const sig = Math.abs(c.z) >= 2
                    return (
                      <div
                        key={col.label}
                        className={`relative flex h-[38px] min-w-0 flex-col items-center justify-center gap-px rounded-[3px] ${c.n < 15 ? 'border border-dashed border-line' : 'bg-bg'} ${c.n < 40 && c.n >= 15 ? 'opacity-60' : ''}`}
                        style={c.n >= 15 ? { background: tint(c) } : undefined}
                        title={c.n ? `${((100 * c.w) / c.n).toFixed(1)}% won vs ${((100 * c.e) / c.n).toFixed(1)}% expected: ${c.w} wins from ${c.n} runners (raw A2E ${(c.w / (c.e || 1)).toFixed(2)})` : 'no runners'}
                      >
                        <span className="text-[13px] font-semibold leading-none text-ink">
                          {c.n >= 15 ? smoothA2E(c).toFixed(2) : '-'}
                          <span className="ml-1 text-[8px] font-normal text-ink-mute">{c.n}</span>
                        </span>
                        <span className="flex min-h-[13px] gap-0.5">
                          {m
                            .slice()
                            .sort((a, b) => a - b)
                            .map((n) => (
                              <i key={n} className="inline-flex h-[13px] min-w-[13px] items-center justify-center rounded-full bg-ink px-0.5 text-[8px] font-semibold not-italic text-panel">
                                {n}
                              </i>
                            ))}
                        </span>
                        {sig && c.n >= 15 && <span className={`absolute right-[3px] top-[3px] h-[5px] w-[5px] rounded-full ${c.z > 0 ? 'bg-emerald' : 'bg-rose'}`} />}
                      </div>
                    )
                  })}
                </div>
              ))}
            </div>
            <div className="flex min-w-0 flex-col gap-1.5 text-xs text-ink-soft">
              {(view.sig > 0 || view.noHistory.length > 0) && (
                <p className="m-0">
                  {view.sig > 0 && <span className="font-semibold text-ink">{`${view.sig} cell${view.sig > 1 ? 's' : ''} beyond chance.`}</span>}
                  {view.noHistory.length > 0 && `${view.sig > 0 ? ' ' : ''}No history: ${fmtNums(view.noHistory)}.`}
                </p>
              )}
              {slope && slope[4] > 0 && (
                <p className="m-0 flex items-baseline gap-2 text-ink-mute">
                  <span className="text-xl font-bold leading-none text-emerald-deep">{`${slope[3] >= 0 ? '+' : ''}${slope[3].toFixed(2)}`}</span>
                  <span>
                    rating points per gate wider{dg != null ? ` (${DISTANCE_LABELS[dg]!.toLowerCase()})` : ''}
                    {gates > 1 ? `, about ${slope[3] * (gates - 1) >= 0 ? '+' : ''}${(slope[3] * (gates - 1)).toFixed(1)} across this field's ${gates} gates` : ''}
                    {Math.abs(slope[3] / slope[4]) < 2 ? ', not reliable' : ''}
                  </span>
                </p>
              )}
              <p className="m-0 font-mono text-[10px] text-ink-mute">
                {used.join(' · ')} · {total.toLocaleString()} runners{view.dropped.length ? ` (no ${view.dropped.map((k) => DROP_NAME[k]).join('/')} filter)` : ''}
                {total < 500 ? ' · thin sample' : ''}
              </p>
              <div className="flex gap-3">
                <button type="button" className="text-emerald-deep underline" onClick={() => setShowFilters(!showFilters)}>
                  Filters
                </button>
                <button type="button" className="text-emerald-deep underline" onClick={() => setShowInfo(!showInfo)}>
                  Info
                </button>
              </div>
            </div>
          </div>
          {showInfo && (
            <div className="mt-2 rounded-md bg-bg p-2 text-xs leading-snug text-ink-mute">
              <p className="m-0 mb-1.5">
                <span className="font-semibold text-ink">Cells</span> show A2E: wins divided by the wins the starting price implied (1.00 is exactly as expected), pulled toward 1 when the sample is small. The small number is runners. Hover for the win rate against expected. Green or red means above or below 1, a corner dot means beyond chance, a faded cell has under 40 runners, numbered dots are this race's runners. {data.venue.replace(/\b\w/g, (c) => c.toUpperCase())}, {data.from.slice(0, 4)} to {data.through.slice(0, 7)}.
              </p>
              <p className="m-0 mb-1.5">
                <span className="font-semibold text-ink">Style</span> is the horse's average position at 800m over its last 6 runs: Forward up to 30% back, Midfield 30 to 55%, Back beyond that. <span className="font-semibold text-ink">Race pace</span> counts the Forward-style runners in this race: few is 0 to 1, some 2 to 3, many 4 or more. Distance, rail and going are this race's; if that leaves under 500 runners the card drops pace, then going, then rail.
              </p>
              <p className="m-0">
                <span className="font-semibold text-ink">Not a betting signal.</span> The price already covers the draw and style. The rating line is the draw slope of the within-race ATW rating at this venue and distance, in rating points per barrier step; a wider field has more steps, so the same slope costs more across it.
              </p>
            </div>
          )}
        </div>
      )}
    </section>
  )
}
