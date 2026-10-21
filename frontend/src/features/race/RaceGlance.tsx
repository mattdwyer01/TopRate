import { useEffect, useRef, useState } from 'react'
import type { Runner } from '../../types/domain'
import type { TripRace } from '../../lib/tripMap'
import { fmtPrice, fmtWpr } from '../../lib/format'
import { SPEED_MAP_TINT_THRESHOLD, MAP_POOL_MIN_SM, MAP_VALUE_MIN_SM } from '../../lib/raceModel'
import { fmtAdj } from './rowParts'
import { typicalSd, type Ranked } from './raceFacts'
import { CORE_GAP_FROM_TOP } from '../../lib/raceModel'

interface RaceGlanceProps {
  ranked: Ranked[]
  allRunners: Runner[]
  scratched: Set<string>
  coreGap?: number
  innerGap: number
  outerGap: number
  trip: TripRace | null
  onSelect: (runId: string) => void
}

const smFill = (v: number | null | undefined) =>
  v != null && v >= SPEED_MAP_TINT_THRESHOLD ? 'var(--color-emerald-deep)' : v != null && v <= -SPEED_MAP_TINT_THRESHOLD ? 'var(--color-rose)' : 'var(--color-ink-faint)'

const ROW_H = 26
const LABEL_W = 150
const RIGHT_W = 74

// The projection ladder: every runner on one WPR axis, best at the top, with the inside-2, inside-4 and inside-6 bands shaded, so the shape of the
// field (a standout, a pack, a long tail) reads before any number does.
// showSm adds a speed map adjustment column (green at +0.5 or better, red at -0.5 or worse, the same cut-offs as the race table) and rings
// runners outside the outer line whose adjustment is favourable, the ones the quaddie view adds back to its pool.
export function Ladder({
  ranked,
  coreGap = CORE_GAP_FROM_TOP,
  innerGap,
  outerGap,
  onSelect,
  showSm = false,
  selected,
  showBands = true,
}: Pick<RaceGlanceProps, 'ranked' | 'coreGap' | 'innerGap' | 'outerGap' | 'onSelect'> & { showSm?: boolean; selected?: Set<string>; showBands?: boolean }) {
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
  const smW = showSm ? 36 : 0
  const rightW = (narrow ? 52 : RIGHT_W + 56) + smW
  const x0 = labelW
  const x1 = width - rightW
  const X = (v: number) => x0 + ((Math.min(Math.max(v, lo), hi) - lo) / (hi - lo)) * (x1 - x0)
  const topPad = 22
  // A band label that does not fit its band drops to a short form so the three never run together on a phone.
  const bandLabel = (n: number, w: number) => (w < 56 ? `\u2264${n}` : `inside ${n}`)
  const H = topPad + ranked.length * ROW_H + 22
  // Label spacing grows as the plot narrows (two ladders side by side), so tick labels never run together.
  const tickStep = [2, 4, 5, 10, 20].find((st) => (hi - lo) / st <= (x1 - x0) / 34) ?? 20
  const ticks: number[] = []
  for (let t = Math.ceil(lo / tickStep) * tickStep; t <= hi; t += tickStep) ticks.push(t)

  return (
    <div ref={wrapRef} className="w-full">
      <svg width={width} height={H} viewBox={`0 0 ${width} ${H}`} role="img" aria-label={showBands ? 'Projected WPR for each runner, with the inside-4 and inside-6 bands shaded' : 'Projected WPR for each runner'}>
        {showBands && (
          <>
            <rect x={X(top - outerGap)} y={topPad - 4} width={X(top - innerGap) - X(top - outerGap)} height={H - topPad - 14} fill="var(--color-amber-tint)" />
            <rect x={X(top - innerGap)} y={topPad - 4} width={X(hi) - X(top - innerGap)} height={H - topPad - 14} fill="var(--color-emerald-tint)" />
            <rect x={X(top - coreGap)} y={topPad - 4} width={X(hi) - X(top - coreGap)} height={H - topPad - 14} fill="var(--color-blue-tint)" />
            <text x={(X(top - coreGap) + X(hi)) / 2} y={11} textAnchor="middle" fontSize={10} fontWeight={600} fill="var(--color-blue-deep)">
              {bandLabel(coreGap, X(hi) - X(top - coreGap))}
            </text>
            <text x={(X(top - innerGap) + X(top - coreGap)) / 2} y={11} textAnchor="middle" fontSize={10} fontWeight={600} fill="var(--color-emerald-deep)">
              {bandLabel(innerGap, X(top - coreGap) - X(top - innerGap))}
            </text>
            <text x={(X(top - outerGap) + X(top - innerGap)) / 2} y={11} textAnchor="middle" fontSize={10} fontWeight={600} fill="var(--color-amber)">
              {bandLabel(outerGap, X(top - innerGap) - X(top - outerGap))}
            </text>
          </>
        )}
        {showSm && (
          <text x={width - 40} y={11} textAnchor="end" fontSize={10} fontWeight={600} fill="var(--color-ink-mute)">
            SM
          </text>
        )}
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
          const tone = !showBands ? 'var(--color-slate)' : r.inner ? 'var(--color-emerald-deep)' : r.outer ? 'var(--color-amber)' : 'var(--color-slate)'
          const price = r.runner.fixedWinPrice
          const name = `${r.runner.tabNumber}. ${r.runner.horse}${r.estimated ? ' (est.)' : ''}`
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
              <title>{`${name}: ${fmtWpr(r.proj)} projected${half(r) != null ? `, likely range ${Math.round(r.proj - half(r)!)} to ${Math.round(r.proj + half(r)!)}` : ''}${r.estimated ? ', first starter: figure estimated from the race level and price, not counted in the lines or pools' : r.gap > 0 ? `, ${r.gap.toFixed(1)} behind the top` : ''}${price != null ? `, ${fmtPrice(price)}` : ''}`}</title>
              <rect
                x={0}
                y={y - ROW_H / 2}
                width={width}
                height={ROW_H}
                fill={selected?.has(r.runner.runId) ? 'var(--color-emerald-bg)' : 'transparent'}
                stroke={selected?.has(r.runner.runId) ? 'var(--color-emerald-line)' : 'none'}
              />
              <text x={selected ? 14 : 0} y={y + 4} fontSize={12} fill="var(--color-ink)" fontWeight={(showBands && r.inner) || selected?.has(r.runner.runId) ? 600 : 400}>
                {name.length > maxChars ? `${name.slice(0, maxChars - 1)}…` : name}
              </text>
              {selected?.has(r.runner.runId) && (
                <text x={2} y={y + 4} fontSize={12} fontWeight={700} fill="var(--color-emerald-deep)">
                  ✓
                </text>
              )}
              {half(r) != null && (
                <rect x={X(r.proj - half(r)!)} y={y - 5} width={Math.max(2, X(r.proj + half(r)!) - X(r.proj - half(r)!))} height={10} rx={5} fill={tone} fillOpacity={0.16} />
              )}
              <line x1={X(top)} x2={X(r.proj)} y1={y} y2={y} stroke={tone} strokeWidth={2} strokeOpacity={0.35} strokeLinecap="round" />
              {(() => {
                const mapAdded = showSm && !r.inner && r.outer && !r.eff?.speedMapLight && (r.eff?.speedMapAdj ?? -Infinity) >= MAP_POOL_MIN_SM
                return (
                  <circle
                    cx={X(r.proj)}
                    cy={y}
                    r={showBands && r.inner ? 6 : 5}
                    fill={tone}
                    stroke={mapAdded ? 'var(--color-emerald)' : '#fff'}
                    strokeWidth={mapAdded ? ((r.eff?.speedMapAdj ?? 0) >= MAP_VALUE_MIN_SM ? 3.5 : 2) : 1.5}
                  />
                )
              })()}
              <text x={width} y={y + 4} textAnchor="end" fontSize={12} fontFamily="var(--font-mono)" fill="var(--color-ink-soft)">
                {fmtWpr(r.proj)}
              </text>
              {showSm && (
                <text x={width - 40} y={y + 4} textAnchor="end" fontSize={12} fontFamily="var(--font-mono)" fill={smFill(r.eff?.speedMapAdj)}>
                  {fmtAdj(r.eff?.speedMapAdj)}
                </text>
              )}
              {!narrow && half(r) != null && (
                <text x={width - 100 - smW} y={y + 4} textAnchor="end" fontSize={11} fontFamily="var(--font-mono)" fill="var(--color-ink-faint)">
                  {Math.round(r.proj - half(r)!)}-{Math.round(r.proj + half(r)!)}
                </text>
              )}
              {!narrow && price != null && (
                <text x={width - 44 - smW} y={y + 4} textAnchor="end" fontSize={11} fontFamily="var(--font-mono)" fill="var(--color-ink-faint)">
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
