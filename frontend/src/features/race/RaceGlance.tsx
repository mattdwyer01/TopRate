import { useEffect, useMemo, useRef, useState } from 'react'
import type { Runner } from '../../types/domain'
import type { TripRace } from '../../lib/tripMap'
import { fmtPrice, fmtWpr } from '../../lib/format'
import { computePriceMove, MOVE_DISPLAY_THRESHOLD_PCT } from '../../lib/priceMove'
import type { Ranked } from './raceFacts'

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
function Ladder({ ranked, innerGap, outerGap, onSelect }: Pick<RaceGlanceProps, 'ranked' | 'innerGap' | 'outerGap' | 'onSelect'>) {
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
  const lo = Math.max(ranked[ranked.length - 1].proj - 2, top - 24)
  const hi = top + 1.5
  const narrow = width < 480
  const labelW = narrow ? 112 : LABEL_W
  const rightW = narrow ? 52 : RIGHT_W
  const x0 = labelW
  const x1 = width - rightW
  const X = (v: number) => x0 + ((Math.min(Math.max(v, lo), hi) - lo) / (hi - lo)) * (x1 - x0)
  const topPad = 22
  const H = topPad + ranked.length * ROW_H + 22
  const ticks: number[] = []
  for (let t = Math.ceil(lo / 2) * 2; t <= hi; t += 2) ticks.push(t)

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
            <g key={r.runner.runId} onClick={() => onSelect(r.runner.runId)} style={{ cursor: 'pointer' }}>
              <title>{`${name}: ${fmtWpr(r.proj)} projected${r.gap > 0 ? `, ${r.gap.toFixed(1)} behind the top` : ''}${price != null ? `, ${fmtPrice(price)}` : ''}`}</title>
              <rect x={0} y={y - ROW_H / 2} width={width} height={ROW_H} fill="transparent" />
              <text x={0} y={y + 4} fontSize={12} fill="var(--color-ink)" fontWeight={r.inner ? 600 : 400}>
                {name.length > maxChars ? `${name.slice(0, maxChars - 1)}…` : name}
              </text>
              <line x1={X(top)} x2={X(r.proj)} y1={y} y2={y} stroke={tone} strokeWidth={2} strokeOpacity={0.35} strokeLinecap="round" />
              <circle cx={X(r.proj)} cy={y} r={r.inner ? 6 : 5} fill={tone} stroke="#fff" strokeWidth={1.5} />
              <text x={width} y={y + 4} textAnchor="end" fontSize={12} fontFamily="var(--font-mono)" fill="var(--color-ink-soft)">
                {fmtWpr(r.proj)}
              </text>
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

function Fact({ label, children }: { label: string; children: React.ReactNode }) {
  return (
    <div className="border-b border-line-soft py-2 last:border-0">
      <div className="text-[11px] font-semibold uppercase tracking-wide text-ink-faint">{label}</div>
      <div className="mt-0.5 text-sm text-ink">{children}</div>
    </div>
  )
}

export function RaceGlance({ ranked, allRunners, scratched, innerGap, outerGap, trip, onSelect }: RaceGlanceProps) {
  const facts = useMemo(() => {
    const inner = ranked.filter((r) => r.inner)
    const outer = ranked.filter((r) => r.inner || r.outer)
    const value = outer
      .filter((r) => r.eff?.isOverlay && r.runner.fixedWinPrice != null && r.eff.effectivePrice != null)
      .map((r) => ({ r, pct: (r.runner.fixedWinPrice! / r.eff!.effectivePrice! - 1) * 100 }))
      .sort((a, b) => b.pct - a.pct)[0]
    const moves = allRunners
      .filter((r) => !scratched.has(r.runId))
      .map((r) => ({ r, m: computePriceMove(r.openFixedPrice, r.fixedWinPrice) }))
      .filter((x): x is { r: Runner; m: NonNullable<ReturnType<typeof computePriceMove>> } => x.m != null && x.m.pctChange >= MOVE_DISPLAY_THRESHOLD_PCT * 3)
      .sort((a, b) => b.m.pctChange - a.m.pctChange)[0]
    let leader: string | null = null
    if (trip) {
      const lead = trip.runners.filter((t) => t.gap != null && !scratched.has(t.rid)).sort((a, b) => (a.gap as number) - (b.gap as number))[0]
      if (lead) leader = `${lead.barrier}. ${lead.name}`
    }
    if (!leader) {
      const lead = ranked.map((r) => r.runner).filter((r) => r.predictedRelSettle != null).sort((a, b) => (a.predictedRelSettle as number) - (b.predictedRelSettle as number))[0]
      if (lead) leader = `${lead.tabNumber}. ${lead.horse}`
    }
    const thin = ranked.filter((r) => r.runner.projectionModel === 'light').length
    return { inner, outer, value, moves, leader, thin }
  }, [ranked, allRunners, scratched, trip])

  if (!ranked.length) return null
  const top = ranked[0]
  return (
    <section className="grid gap-4 rounded-lg border border-line bg-panel p-4 shadow-[var(--shadow-1)] lg:grid-cols-[minmax(0,1.7fr)_minmax(260px,1fr)]">
      <div className="min-w-0">
        <div className="mb-1 flex flex-wrap items-baseline justify-between gap-2">
          <h3 className="text-sm font-semibold text-ink">Projection ladder</h3>
          <span className="text-xs text-ink-faint">Projected WPR, best first &middot; tap a runner for detail</span>
        </div>
        <Ladder ranked={ranked} innerGap={innerGap} outerGap={outerGap} onSelect={onSelect} />
      </div>
      <div className="min-w-0 lg:border-l lg:border-line-soft lg:pl-4">
        <h3 className="mb-1 text-sm font-semibold text-ink">At a glance</h3>
        <Fact label="Top rated">
          <button type="button" onClick={() => onSelect(top.runner.runId)} className="text-left font-semibold hover:underline">
            {top.runner.tabNumber}. {top.runner.horse}
          </button>{' '}
          <span className="font-mono text-ink-soft">{fmtWpr(top.proj)}</span>
          {top.runner.fixedWinPrice != null && <span className="font-mono text-ink-faint"> &middot; {fmtPrice(top.runner.fixedWinPrice)}</span>}
        </Fact>
        <Fact label={`Inside ${innerGap} · inside ${outerGap}`}>
          <span className="font-semibold">{facts.inner.length}</span> and <span className="font-semibold">{facts.outer.length}</span> of {ranked.length} runners
          <div className="mt-0.5 text-xs text-ink-mute">{facts.inner.map((r) => r.runner.horse).join(', ')}</div>
        </Fact>
        {facts.value && (
          <Fact label="Best value inside the line">
            <button type="button" onClick={() => onSelect(facts.value.r.runner.runId)} className="text-left font-semibold hover:underline">
              {facts.value.r.runner.tabNumber}. {facts.value.r.runner.horse}
            </button>{' '}
            <span className="font-mono text-emerald-deep">{fmtPrice(facts.value.r.runner.fixedWinPrice)}</span>
            <span className="text-xs text-ink-mute"> vs fair {fmtPrice(facts.value.r.eff!.effectivePrice)} ({Math.round(facts.value.pct)}% over)</span>
          </Fact>
        )}
        {facts.moves && (
          <Fact label="Biggest market move">
            <button type="button" onClick={() => onSelect(facts.moves!.r.runId)} className="text-left font-semibold hover:underline">
              {facts.moves.r.tabNumber}. {facts.moves.r.horse}
            </button>{' '}
            <span className={`font-mono ${facts.moves.m.direction === 'firmed' ? 'text-emerald-deep' : 'text-rose'}`}>
              {facts.moves.m.direction === 'firmed' ? 'firmed' : 'drifted'} {Math.round(facts.moves.m.pctChange)}%
            </span>
            <span className="text-xs text-ink-mute"> from {fmtPrice(facts.moves.r.openFixedPrice)}</span>
          </Fact>
        )}
        {facts.leader && <Fact label="Likely to lead">{facts.leader}</Fact>}
        {facts.thin > 0 && (
          <Fact label="Limited form">
            <span className="text-ink-soft">
              {facts.thin} runner{facts.thin === 1 ? '' : 's'} projected by the light-history model (0-2 prior runs), so wider error.
            </span>
          </Fact>
        )}
      </div>
    </section>
  )
}
