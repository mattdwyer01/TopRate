import { useEffect, useMemo, useRef, useState } from 'react'
import type { TripRace, TripRunner } from '../../lib/tripMap'

// Trip map: where each runner is projected to be about 800m from home. Horizontal axis = lengths behind the
// leader (front of the field at the right), vertical axis = metres from the inside rail (rail at the top).
// Horses are drawn to scale (about 2.4m nose to tail, 0.75m wide) on one metric scale for both axes, with the
// nose at the projected position. Positions come from analysis/trip_map/build_trip_map.py: a model trained on
// every GPS-tracked run ranks the field, then runners are placed using the spread real fields show.

interface TripMapProps {
  trip: TripRace
  excluded: Set<string> // scratched runners (runId), left off the map
  generated: string
}

const LEN_M = 2.4 // one length in metres
const HORSE_W = 0.75 // metres of width a running horse occupies
const FRONT = [4, 120, 87] // emerald-deep
const BACK = [209, 250, 229] // light emerald

function mix(t: number): string {
  return `rgb(${FRONT.map((v, i) => Math.round(v + (BACK[i] - v) * t)).join(',')})`
}

interface Placed extends TripRunner {
  gx: number // gap in lengths, leader = 0
  t: number // 0 front .. 1 back
  px: number
  py: number
}

export function TripMap({ trip, excluded, generated }: TripMapProps) {
  const wrapRef = useRef<HTMLDivElement>(null)
  const [width, setWidth] = useState(900)
  const [hover, setHover] = useState<string | null>(null)

  useEffect(() => {
    const el = wrapRef.current
    if (!el) return
    const ro = new ResizeObserver(() => {
      setWidth(Math.max(720, Math.round(el.clientWidth - 2)))
      el.scrollLeft = el.scrollWidth // narrow screens: start at the front of the field
    })
    ro.observe(el)
    setWidth(Math.max(720, Math.round(el.clientWidth - 2)))
    return () => ro.disconnect()
  }, [])

  const runners = useMemo(() => trip.runners.filter((r) => !excluded.has(r.rid) && r.gap != null), [trip, excluded])

  const layout = useMemo(() => {
    const m = { l: 44, r: 20, t: 30, b: 44 }
    const iw = width - m.l - m.r
    const minGap = runners.length ? Math.min(...runners.map((r) => r.gap as number)) : 0
    const rows = runners.map((r) => ({ ...r, gx: (r.gap as number) - minGap }))
    const maxG = Math.max(8, Math.ceil((Math.max(0, ...rows.map((r) => r.gx)) + 1.2) / 2) * 2)
    const maxL = Math.max(12, Math.ceil((Math.max(0, ...rows.map((r) => r.lane)) + 1.2) / 2) * 2)
    const GM = -1.2
    const pxm = iw / ((maxG - GM) * LEN_M)
    const ih = Math.round(maxL * pxm)
    const H = m.t + ih + m.b
    const X = (g: number) => m.l + iw - (g - GM) * LEN_M * pxm
    const Y = (l: number) => m.t + l * pxm
    const hw = (LEN_M * pxm) / 2
    const hh = (HORSE_W * pxm) / 2
    const order = [...rows].sort((a, b) => a.gx - b.gx)
    const tOf = new Map(order.map((r, i) => [r.rid, order.length > 1 ? i / (order.length - 1) : 0]))
    const items: Placed[] = rows.map((r) => ({ ...r, t: tOf.get(r.rid) ?? 0, px: X(r.gx) - hw, py: Y(r.lane) }))
    // nudge overlapping horses apart: sideways first, then lengthwise
    for (let it = 0; it < 80; it++) {
      let moved = false
      for (let i = 0; i < items.length; i++) {
        for (let j = i + 1; j < items.length; j++) {
          const a = items[i]
          const b = items[j]
          const dx = b.px - a.px
          const dy = b.py - a.py
          const ox = 2 * hw + 2 - Math.abs(dx)
          const oy = 2 * hh + 3 - Math.abs(dy)
          if (ox > 0 && oy > 0) {
            moved = true
            if (oy <= ox * 0.6 || Math.abs(dy) >= Math.abs(dx) * 0.4) {
              const s = (dy >= 0 ? 1 : -1) * (Math.abs(dy) < 0.01 ? (j % 2 ? 1 : -1) : 1)
              a.py -= (s * oy) / 2
              b.py += (s * oy) / 2
            } else {
              const s = dx >= 0 ? 1 : -1
              a.px -= (s * ox) / 2
              b.px += (s * ox) / 2
            }
          }
        }
      }
      for (const r of items) {
        r.py = Math.min(m.t + ih - hh - 1, Math.max(m.t + hh + 1, r.py))
        r.px = Math.min(m.l + iw - hw - 1, Math.max(m.l + hw + 1, r.px))
      }
      if (!moved) break
    }
    return { m, iw, ih, H, maxG, maxL, pxm, X, Y, hw, hh, items }
  }, [runners, width])

  if (!runners.length) {
    return (
      <div className="rounded-lg border border-line bg-panel p-3 text-sm text-ink-mute">No runners to map.</div>
    )
  }

  const { m, iw, ih, H, maxG, maxL, pxm, X, Y, hw, hh, items } = layout
  const hov = items.find((r) => r.rid === hover) ?? null
  const gridG: number[] = []
  for (let g = 0; g <= maxG; g += 2) gridG.push(g)
  const gridL: number[] = []
  for (let l = 0; l <= maxL; l += 2) gridL.push(l)
  const laneLabel = trip.laneKind === '800m' ? 'width from rail at 800m from home' : 'average width from rail over the whole run'
  const hist = items.filter((r) => r.nHist === 0).length

  return (
    <div className="rounded-lg border border-line bg-panel p-3 shadow-[var(--shadow-1)]">
      <div className="flex flex-wrap items-baseline justify-between gap-2">
        <span className="text-sm font-semibold text-ink">Trip map</span>
        <span className="text-xs text-ink-faint">Projected running line &middot; {laneLabel} &middot; horses drawn to scale</span>
      </div>
      <div ref={wrapRef} className="relative mt-2 overflow-x-auto">
        <svg width={width} height={H} viewBox={`0 0 ${width} ${H}`} role="img" aria-label="Projected trip map: distance behind the leader against width from the rail">
          <rect x={m.l} y={m.t} width={iw} height={ih} fill="var(--color-emerald-tint)" />
          {gridG.map((g) => (
            <g key={`g${g}`}>
              <line x1={X(g)} x2={X(g)} y1={m.t} y2={m.t + ih} stroke="var(--color-line)" />
              <text x={X(g)} y={m.t + ih + 15} textAnchor="middle" fontSize={10} fill="var(--color-ink-mute)">
                {g === 0 ? 'leader' : `${g}L`}
              </text>
            </g>
          ))}
          {gridL.map((l) => (
            <g key={`l${l}`}>
              <line x1={m.l} x2={m.l + iw} y1={Y(l)} y2={Y(l)} stroke="var(--color-line)" />
              <text x={m.l - 6} y={Y(l) + 3} textAnchor="end" fontSize={10} fill="var(--color-ink-mute)">
                {l}m
              </text>
            </g>
          ))}
          <line x1={m.l} x2={m.l + iw} y1={Y(0)} y2={Y(0)} stroke="var(--color-ink)" strokeWidth={3} />
          <text x={m.l + 4} y={m.t - 10} fontSize={10} fill="var(--color-ink-mute)">
            INSIDE RAIL
          </text>
          <text x={m.l + iw} y={m.t - 10} textAnchor="end" fontSize={10} fill="var(--color-ink-mute)">
            front of field &rarr;
          </text>
          <text x={m.l} y={H - 6} fontSize={10} fill="var(--color-ink-mute)">
            &larr; further back (lengths behind the leader, 1 length = {LEN_M}m, drawn to scale)
          </text>
          {hov && (
            <ellipse
              cx={X(hov.gx)}
              cy={Y(hov.lane)}
              rx={trip.err.gap * LEN_M * pxm}
              ry={trip.err.lane * pxm}
              fill={mix(hov.t)}
              fillOpacity={0.25}
              stroke={mix(hov.t)}
            />
          )}
          {items.map((r) => {
            const dark = r.t < 0.55
            const on = r.rid === hover
            return (
              <g key={r.rid} onMouseEnter={() => setHover(r.rid)} onMouseLeave={() => setHover(null)} onClick={() => setHover(on ? null : r.rid)} style={{ cursor: 'pointer' }}>
                <rect
                  x={r.px - hw}
                  y={r.py - hh}
                  width={2 * hw}
                  height={2 * hh}
                  rx={Math.min(hh, 6)}
                  fill={mix(r.t)}
                  stroke={on ? 'var(--color-amber)' : '#ffffff'}
                  strokeWidth={on ? 2.5 : 1.5}
                />
                <rect
                  x={r.px + hw - hh * 1.3}
                  y={r.py - hh * 0.7}
                  width={hh * 1.3}
                  height={hh * 1.4}
                  rx={hh * 0.6}
                  fill="none"
                  stroke={dark ? 'rgba(255,255,255,.55)' : 'rgba(15,23,41,.4)'}
                />
                <text
                  x={r.px - hh * 0.4}
                  y={r.py + 4}
                  textAnchor="middle"
                  fontSize={Math.max(10, Math.min(12, hh * 1.5))}
                  fontWeight={600}
                  fill={dark ? '#ffffff' : '#0f1729'}
                >
                  {r.barrier}
                </text>
              </g>
            )
          })}
        </svg>
        {hov && (
          <div
            className="pointer-events-none absolute z-10 max-w-[260px] rounded-md bg-ink px-2.5 py-2 text-xs leading-snug text-white shadow-[var(--shadow-2)]"
            style={{ left: Math.min(Math.max(hov.px - 60, 0), width - 270), top: hov.py + hh + 8 }}
          >
            <div className="font-semibold">
              {hov.barrier}. {hov.name}
            </div>
            <div>
              Projected {hov.gx.toFixed(1)}L behind the leader, {hov.lane.toFixed(1)}m off the rail
            </div>
            <div className="opacity-75">
              {hov.last
                ? `Last GPS run ${hov.last.track}, ${hov.last.date} (${hov.nHist} on record)`
                : 'No GPS run on record: forecast from the barrier and track only'}
            </div>
          </div>
        )}
      </div>
      <div className="mt-2 flex flex-wrap items-center gap-x-5 gap-y-1 text-xs text-ink-mute">
        <span className="flex items-center gap-1.5">
          <span className="inline-block h-2 w-28 rounded-sm" style={{ background: `linear-gradient(90deg, ${mix(0)}, ${mix(1)})` }} />
          front of field to back
        </span>
        <span>Typical error about {trip.err.gap} lengths and {trip.err.lane}m (hover a runner to see it)</span>
        {hist > 0 && <span>{hist} runner{hist === 1 ? '' : 's'} with no GPS history</span>}
      </div>
      <p className="mt-2 max-w-3xl text-xs leading-relaxed text-ink-faint">
        The model ranks the field on track, distance, going, rail, barrier and each horse&apos;s last GPS runs, then places the
        runners using the spread real fields show, so the order is the forecast and each exact position is uncertain. It does
        not feed Proj or Combo; in testing it added nothing to winner selection beyond the market. Updated {generated.slice(0, 16).replace('T', ' ')} UTC.
      </p>
    </div>
  )
}
