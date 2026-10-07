import { useEffect, useMemo, useRef, useState } from 'react'
import type { Runner } from '../../types/domain'
import type { TripRace } from '../../lib/tripMap'
import { fmtPrice, fmtWpr } from '../../lib/format'
import { computePriceMove, MOVE_DISPLAY_THRESHOLD_PCT } from '../../lib/priceMove'
import { typicalSd, type Ranked } from './raceFacts'

interface RaceGlanceProps {
  ranked: Ranked[]
  allRunners: Runner[]
  scratched: Set<string>
  innerGap: number
  outerGap: number
  trip: TripRace | null
  onSelect: (runId: string) => void
}

const ROW_H = 26
const LABEL_W = 150
const RIGHT_W = 74

// The projection ladder: every runner on one WPR axis, best at the top, with the inside-4 and inside-6 bands shaded, so the shape of the
// field (a standout, a pack, a long tail) reads before any number does.
export function Ladder({ ranked, innerGap, outerGap, onSelect }: Pick<RaceGlanceProps, 'ranked' | 'innerGap' | 'outerGap' | 'onSelect'>) {
  const wrapRef = useRef<HTMLDivElement>(null)
  const [width, setWidth] = useState(640)
  useEffect(() => {
    const el = wrapRef.current
    if (!el) return
    const ro = new ResizeObserver(() => setWidth(Math.max(300, Math.round(el.clientWidth))))
    ro.observe(el)
    setWidth(Math.max(300, Math.round(el.clientWidth)))
    return () => ro.disconnect()
  }, [])

  const top = ranked[0].proj
  // Likely range = the middle half of outcomes (about +-0.67 typical error), so a thin-history horse reads visibly wider than a settled one.
  const half = (r: Ranked) => {
    const sd = typicalSd(r.runner, r.proj)
    return sd != null ? 0.67 * sd : null
  }
  const lows = ranked.map((r) => r.proj - (half(r) ?? 0))
  const highs = ranked.map((r) => r.proj + (half(r) ?? 0))
  const lo = Math.max(Math.min(...lows) - 1, top - 34)
  const hi = Math.max(...highs) + 1.5
  const narrow = width < 480
  const labelW = narrow ? 112 : LABEL_W
  const rightW = narrow ? 52 : RIGHT_W + 56
  const x0 = labelW
  const x1 = width - rightW
  const X = (v: number) => x0 + ((Math.min(Math.max(v, lo), hi) - lo) / (hi - lo)) * (x1 - x0)
  const topPad = 22
  const H = topPad + ranked.length * ROW_H + 22
  // Label spacing grows as the plot narrows (two ladders side by side), so tick labels never run together.
  const tickStep = [2, 4, 5, 10, 20].find((st) => (hi - lo) / st <= (x1 - x0) / 34) ?? 20
  const ticks: number[] = []
  for (let t = Math.ceil(lo / tickStep) * tickStep; t <= hi; t += tickStep) ticks.push(t)

  return (
    <div ref={wrapRef} className="w-full">
      <svg width={width} height={H} viewBox={`0 0 ${width} ${H}`} role="img" aria-label="Projected WPR for each runner, with the inside-4 and inside-6 bands shaded">
        <rect x={X(top - outerGap)} y={topPad - 4} width={X(top - innerGap) - X(top - outerGap)} height={H - topPad - 14} fill="var(--color-amber-tint)" />
        <rect x={X(top - innerGap)} y={topPad - 4} width={X(hi) - X(top - innerGap)} height={H - topPad - 14} fill="var(--color-emerald-tint)" />
        <text x={(X(top - innerGap) + X(hi)) / 2} y={11} textAnchor="middle" fontSize={10} fontWeight={600} fill="var(--color-emerald-deep)">
          inside {innerGap}
        </text>
        <text x={(X(top - outerGap) + X(top - innerGap)) / 2} y={11} textAnchor="middle" fontSize={10} fontWeight={600} fill="var(--color-amber)">
          inside {outerGap}
        </text>
        {ticks.map((t) => (
          <g key={t}>
            <line x1={X(t)} x2={X(t)} y1={topPad - 4} y2={H - 18} stroke="var(--color-line)" strokeWidth={1} />
            <text x={X(t)} y={H - 5} textAnchor="middle" fontSize={10} fill="var(--color-ink-mute)">
              {t}
            </text>
          </g>
        ))}
        {ranked.map((r, i) => {
          const y = topPad + i * ROW_H + ROW_H / 2
          const tone = r.inner ? 'var(--color-emerald-deep)' : r.outer ? 'var(--color-amber)' : 'var(--color-slate)'
          const price = r.runner.fixedWinPrice
          const name = `${r.runner.tabNumber}. ${r.runner.horse}`
          const maxChars = narrow ? 15 : 20
          return (
            <g
              key={r.runner.runId}
              role="button"
              tabIndex={0}
              aria-label={`${name}, projected ${fmtWpr(r.proj)}. Open runner detail`}
              onClick={() => onSelect(r.runner.runId)}
              onKeyDown={(e) => {
                if (e.key === 'Enter' || e.key === ' ') {
                  e.preventDefault()
                  onSelect(r.runner.runId)
                }
              }}
              style={{ cursor: 'pointer' }}
            >
              <title>{`${name}: ${fmtWpr(r.proj)} projected${half(r) != null ? `, likely range ${Math.round(r.proj - half(r)!)} to ${Math.round(r.proj + half(r)!)}` : ''}${r.gap > 0 ? `, ${r.gap.toFixed(1)} behind the top` : ''}${price != null ? `, ${fmtPrice(price)}` : ''}`}</title>
              <rect x={0} y={y - ROW_H / 2} width={width} height={ROW_H} fill="transparent" />
              <text x={0} y={y + 4} fontSize={12} fill="var(--color-ink)" fontWeight={r.inner ? 600 : 400}>
                {name.length > maxChars ? `${name.slice(0, maxChars - 1)}…` : name}
              </text>
              {half(r) != null && (
                <rect x={X(r.proj - half(r)!)} y={y - 5} width={Math.max(2, X(r.proj + half(r)!) - X(r.proj - half(r)!))} height={10} rx={5} fill={tone} fillOpacity={0.16} />
              )}
              <line x1={X(top)} x2={X(r.proj)} y1={y} y2={y} stroke={tone} strokeWidth={2} strokeOpacity={0.35} strokeLinecap="round" />
              <circle cx={X(r.proj)} cy={y} r={r.inner ? 6 : 5} fill={tone} stroke="#fff" strokeWidth={1.5} />
              <text x={width} y={y + 4} textAnchor="end" fontSize={12} fontFamily="var(--font-mono)" fill="var(--color-ink-soft)">
                {fmtWpr(r.proj)}
              </text>
              {!narrow && half(r) != null && (
                <text x={width - 100} y={y + 4} textAnchor="end" fontSize={11} fontFamily="var(--font-mono)" fill="var(--color-ink-faint)">
                  {Math.round(r.proj - half(r)!)}-{Math.round(r.proj + half(r)!)}
                </text>
              )}
              {!narrow && price != null && (
                <text x={width - 44} y={y + 4} textAnchor="end" fontSize={11} fontFamily="var(--font-mono)" fill="var(--color-ink-faint)">
                  {fmtPrice(price)}
                </text>
              )}
            </g>
          )
        })}
      </svg>
    </div>
  )
}

// The 'Mover' chip only names a clear move: three times the threshold at which a price move is shown at all.
const MOVER_CHIP_MIN_PCT = MOVE_DISPLAY_THRESHOLD_PCT * 3

function useGlanceFacts({ ranked, allRunners, scratched, trip }: Pick<RaceGlanceProps, 'ranked' | 'allRunners' | 'scratched' | 'trip'>) {
  return useMemo(() => {
    const inner = ranked.filter((r) => r.inner)
    const outer = ranked.filter((r) => r.inner || r.outer)
    const moves = allRunners
      .filter((r) => !scratched.has(r.runId))
      .map((r) => ({ r, m: computePriceMove(r.openFixedPrice, r.fixedWinPrice) }))
      .filter((x): x is { r: Runner; m: NonNullable<ReturnType<typeof computePriceMove>> } => x.m != null && x.m.pctChange >= MOVER_CHIP_MIN_PCT)
      .sort((a, b) => b.m.pctChange - a.m.pctChange)[0]
    let leader: string | null = null
    if (trip) {
      const lead = trip.runners.filter((t) => t.gap != null && !scratched.has(t.rid)).sort((a, b) => (a.gap as number) - (b.gap as number))[0]
      if (lead) {
        const r = allRunners.find((x) => x.runId === lead.rid)
        leader = `${r ? r.tabNumber : lead.barrier}. ${lead.name}`
      }
    }
    if (!leader) {
      const lead = ranked.map((r) => r.runner).filter((r) => r.predictedRelSettle != null).sort((a, b) => (a.predictedRelSettle as number) - (b.predictedRelSettle as number))[0]
      if (lead) leader = `${lead.tabNumber}. ${lead.horse}`
    }
    const thin = ranked.filter((r) => r.runner.projectionModel === 'light').length
    return { inner, outer, moves, leader, thin }
  }, [ranked, allRunners, scratched, trip])
}

// One line under the header: the answers a reader wants before opening the table.
export function RaceSummaryLine(props: Pick<RaceGlanceProps, 'ranked' | 'allRunners' | 'scratched' | 'innerGap' | 'outerGap' | 'trip' | 'onSelect'>) {
  const { ranked, onSelect, innerGap } = props
  const facts = useGlanceFacts(props)
  if (!ranked.length) return null
  const top = ranked[0]
  const link = 'font-semibold text-ink hover:underline'
  return (
    <section className="flex flex-wrap items-baseline gap-x-5 gap-y-1 rounded-lg border border-line bg-panel px-4 py-2.5 text-sm shadow-[var(--shadow-1)]">
      <span>
        <span className="text-[11px] font-semibold uppercase tracking-wide text-ink-faint">Top rated </span>
        <button type="button" onClick={() => onSelect(top.runner.runId)} className={link}>
          {top.runner.tabNumber}. {top.runner.horse}
        </button>{' '}
        <span className="font-mono text-ink-soft">{fmtWpr(top.proj)}</span>
      </span>
      <span>
        <span className="text-[11px] font-semibold uppercase tracking-wide text-ink-faint">Inside {innerGap} </span>
        <span className="font-semibold">{facts.inner.length}</span> of {ranked.length}
      </span>
      {facts.moves && (
        <span>
          <span className="text-[11px] font-semibold uppercase tracking-wide text-ink-faint">Mover </span>
          <button type="button" onClick={() => onSelect(facts.moves!.r.runId)} className={link}>
            {facts.moves.r.tabNumber}. {facts.moves.r.horse}
          </button>{' '}
          <span className={`font-mono ${facts.moves.m.direction === 'firmed' ? 'text-emerald-deep' : 'text-rose'}`}>
            {facts.moves.m.direction === 'firmed' ? 'firmed' : 'drifted'} {Math.round(facts.moves.m.pctChange)}%
          </span>
        </span>
      )}
      {facts.leader && (
        <span>
          <span className="text-[11px] font-semibold uppercase tracking-wide text-ink-faint">Likely to lead </span>
          {facts.leader}
        </span>
      )}
    </section>
  )
}

// The ladder sits under the field table. Open by default on desktop, collapsed on phones (where the cards already give the order).
export function RaceLadder({ ranked, innerGap, outerGap, onSelect }: Pick<RaceGlanceProps, 'ranked' | 'innerGap' | 'outerGap' | 'onSelect'>) {
  const [open, setOpen] = useState(() => (typeof window === 'undefined' ? true : window.matchMedia('(min-width: 768px)').matches))
  if (!ranked.length) return null
  return (
    <section className="rounded-lg border border-line bg-panel p-4 shadow-[var(--shadow-1)]">
      <button type="button" onClick={() => setOpen((o) => !o)} aria-expanded={open} className="flex w-full flex-wrap items-baseline justify-between gap-2 text-left">
        <h3 className="text-sm font-semibold text-ink">
          Projection ladder <span className="font-normal text-ink-faint">{open ? '▾' : '▸'}</span>
        </h3>
        <span className="text-xs text-ink-faint">Projected WPR, best first &middot; shaded bar is the likely range &middot; tap a runner for detail</span>
      </button>
      {open && (
        <div className="mt-2">
          <Ladder ranked={ranked} innerGap={innerGap} outerGap={outerGap} onSelect={onSelect} />
        </div>
      )}
    </section>
  )
}
