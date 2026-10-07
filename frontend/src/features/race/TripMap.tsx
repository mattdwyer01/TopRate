import { useEffect, useMemo, useRef, useState } from 'react'
import type { TripRace, TripRunner } from '../../lib/tripMap'
import type { Runner } from '../../types/domain'

// Trip map: where each runner is projected to be about 800m from home. Horizontal axis = lengths behind the
// leader (front of the field at the right), vertical axis = metres from the inside rail (rail at the top).
// Each runner is a compact chip (silk, TAB number, name) with its right edge at the projected position. Lengths behind
// the leader are to scale along the bottom axis; the width axis is stretched to keep the chart short, so it is a diagram
// of order and rough width, not an exact plan. Positions come from analysis/trip_map/build_trip_map.py: a model trained on
// every GPS-tracked run ranks the field, then runners are placed using the spread real fields show.

interface TripMapProps {
  trip: TripRace
  excluded: Set<string> // scratched runners (runId), left off the map
  runners: Runner[] // for TAB number and silks (matched on runId)
  generated: string
}

const LEN_M = 2.4 // one length in metres
const CHIP_H = 22
const SILK = 18
const NAME_CHARS = 16

interface Placed extends TripRunner {
  gx: number // gap in lengths, leader = 0
  num: number | string
  silk: string | null
  label: string
  px: number
  py: number
}

export function TripMap({ trip, excluded, runners: field, generated }: TripMapProps) {
  const wrapRef = useRef<HTMLDivElement>(null)
  const [width, setWidth] = useState(900)
  const [hover, setHover] = useState<string | null>(null)

  useEffect(() => {
    const el = wrapRef.current
    if (!el) return
    const fit = () => {
      const w = Math.round(el.clientWidth - 2)
      setWidth(w < 600 ? Math.max(300, w) : Math.max(720, w)) // phones fit the screen, no sideways scroll
    }
    const ro = new ResizeObserver(fit)
    ro.observe(el)
    fit()
    return () => ro.disconnect()
  }, [])

  const byRid = useMemo(() => new Map(field.map((f) => [f.runId, f])), [field])
  const runners = useMemo(() => trip.runners.filter((r) => !excluded.has(r.rid) && r.gap != null), [trip, excluded])

  const layout = useMemo(() => {
    const narrow = width < 600
    const m = narrow ? { l: 34, r: 10, t: 22, b: 34 } : { l: 44, r: 20, t: 30, b: 44 }
    const iw = width - m.l - m.r
    const minGap = runners.length ? Math.min(...runners.map((r) => r.gap as number)) : 0
    const rows = runners.map((r) => ({ ...r, gx: (r.gap as number) - minGap }))
    const maxG = Math.max(8, Math.ceil((Math.max(0, ...rows.map((r) => r.gx)) + 1.2) / 2) * 2)
    const maxL = Math.max(3, Math.ceil(Math.max(0, ...rows.map((r) => r.lane)) + 0.8)) // cut off just past the widest runner
    const GM = -1.2
    const pxm = iw / ((maxG - GM) * LEN_M)
    const hh = CHIP_H / 2
    const hw = narrow ? 24 : 82
    // Compact vertical scale; grows only when a big field needs the room to avoid stacking chips on each other.
    const need = Math.ceil(rows.length * 0.7) * (CHIP_H + 3)
    const ih = Math.max(Math.round(maxL * (narrow ? 11 : 14)), need)
    const ky = ih / maxL
    const H = m.t + ih + m.b
    const X = (g: number) => m.l + iw - (g - GM) * LEN_M * pxm
    const Y = (l: number) => m.t + l * ky
    const items: Placed[] = rows.map((r) => {
      const f = byRid.get(r.rid)
      const num = f?.tabNumber ?? r.barrier
      const nm = f?.horse ?? r.name
      return {
        ...r,
        num,
        silk: f?.silkUrl ?? null,
        label: nm.length > NAME_CHARS ? nm.slice(0, NAME_CHARS - 1) + '…' : nm,
        px: X(r.gx) - hw,
        py: Y(r.lane),
      }
    })
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
    return { m, iw, ih, H, maxG, maxL, pxm, ky, X, Y, hw, hh, items }
  }, [runners, width, byRid])

  if (!runners.length) {
    return (
      <div className="rounded-lg border border-line bg-panel p-3 text-sm text-ink-mute">No runners to map.</div>
    )
  }

  const { m, iw, ih, H, maxG, maxL, pxm, ky, X, Y, hw, hh, items } = layout
  const narrow = width < 600
  const hov = items.find((r) => r.rid === hover) ?? null
  const gridG: number[] = []
  for (let g = 0; g <= maxG; g += 2) gridG.push(g)
  const gridL: number[] = []
  const stepL = maxL > 8 ? 2 : 1
  for (let l = 0; l <= maxL; l += stepL) gridL.push(l)
  const noGps = trip.laneKind === 'est'
  const laneLabel = noGps ? 'estimated width from rail at 800m from home (not measured)' : trip.laneKind === '800m' ? 'width from rail at 800m from home' : 'average width from rail over the whole run'
  const hist = items.filter((r) => r.nHist === 0).length

  return (
    <div className="rounded-lg border border-line bg-panel p-3 shadow-[var(--shadow-1)]">
      <div className="flex flex-wrap items-baseline justify-between gap-2">
        <span className="text-sm font-semibold text-ink">Trip map</span>
        <span className="text-xs text-ink-faint">{narrow ? 'Projected running line' : `Projected running line · ${laneLabel}`}</span>
      </div>
      <div ref={wrapRef} className="relative mt-2 overflow-x-auto">
        <svg width={width} height={H} viewBox={`0 0 ${width} ${H}`} role="img" aria-label="Projected trip map: distance behind the leader against width from the rail">
          <rect x={m.l} y={m.t} width={iw} height={ih} fill="var(--color-bg)" />
          {gridG.map((g) => (
            <g key={`g${g}`}>
              <line x1={X(g)} x2={X(g)} y1={m.t} y2={m.t + ih} stroke="var(--color-line)" />
              <text x={X(g)} y={m.t + ih + 15} textAnchor="middle" fontSize={10} fill="var(--color-ink-mute)">
                {g === 0 ? (narrow ? 'lead' : 'leader') : `${g}L`}
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
            {narrow ? '← further back (lengths behind the leader)' : `← further back (lengths behind the leader, 1 length = ${LEN_M}m)`}
          </text>
          {hov && (
            <ellipse
              cx={X(hov.gx)}
              cy={Y(hov.lane)}
              rx={trip.err.gap * LEN_M * pxm}
              ry={trip.err.lane * ky}
              fill="var(--color-amber)"
              fillOpacity={0.15}
              stroke="var(--color-amber)"
            />
          )}
          {items.map((r) => {
            const on = r.rid === hover
            const x = r.px - hw
            const y = r.py - hh
            const tx = x + SILK + 8
            return (
              <g key={r.rid} onMouseEnter={() => setHover(r.rid)} onMouseLeave={() => setHover(null)} onClick={() => setHover(on ? null : r.rid)} style={{ cursor: 'pointer' }}>
                <rect
                  x={x}
                  y={y}
                  width={2 * hw}
                  height={CHIP_H}
                  rx={5}
                  fill="var(--color-panel)"
                  stroke={on ? 'var(--color-amber)' : 'var(--color-ink-faint)'}
                  strokeWidth={on ? 2 : 1}
                />
                {r.silk && <image href={r.silk} x={x + 3} y={y + (CHIP_H - SILK) / 2} width={SILK} height={SILK} preserveAspectRatio="xMidYMid meet" />}
                <text x={tx} y={r.py + 4} fontSize={11} fontWeight={700} fill="var(--color-ink)">
                  {r.num}
                </text>
                {!narrow && (
                  <text x={tx + 16} y={r.py + 4} fontSize={11} fill="var(--color-ink-mute)">
                    {r.label}
                  </text>
                )}
              </g>
            )
          })}
        </svg>
        {hov && (
          <div
            className="pointer-events-none absolute z-10 max-w-[260px] rounded-md bg-ink px-2.5 py-2 text-xs leading-snug text-white shadow-[var(--shadow-2)]"
            style={{ left: Math.min(Math.max(hov.px - 60, 0), Math.max(0, width - 270)), top: hov.py + hh + 8 }}
          >
            <div className="font-semibold">
              {byRid.get(hov.rid)?.tabNumber ?? hov.barrier}. {hov.name}
            </div>
            <div>
              Barrier {hov.barrier} · projected {hov.gx.toFixed(1)}L behind the leader, {hov.lane.toFixed(1)}m off the rail
            </div>
            <div className="opacity-75">
              {noGps
                ? hov.last
                  ? `Last result ${hov.last.track}, ${hov.last.date} (${hov.nHist} on record). Width is an estimate.`
                  : 'No earlier result on record: forecast from the barrier and track only. Width is an estimate.'
                : hov.last
                  ? `Last GPS run ${hov.last.track}, ${hov.last.date} (${hov.nHist} on record)`
                  : 'No GPS run on record: forecast from the barrier and track only'}
            </div>
          </div>
        )}
      </div>
      <div className="mt-2 flex flex-wrap items-center gap-x-4 gap-y-1 text-xs text-ink-mute">
        <span className="flex items-center gap-1.5">
          Number shown is the TAB number (barrier in the tooltip)
        </span>
        <span>Typical error about {trip.err.gap} lengths and {trip.err.lane}m{narrow ? ' (tap a runner)' : ' (hover a runner to see it)'}</span>
        {hist > 0 && <span>{hist} runner{hist === 1 ? '' : 's'} with no {noGps ? 'earlier result' : 'GPS'} history</span>}
        {noGps && <span className="text-amber">No GPS at this track: gap is forecast from past 800m positions, width is estimated</span>}
      </div>
      <details className="mt-2 text-xs text-ink-faint sm:hidden">
        <summary className="cursor-pointer text-ink-mute">How this is built</summary>
        <p className="mt-1 leading-relaxed">
          The model ranks the field on track, distance, going, rail, barrier and each horse&apos;s last {noGps ? 'results' : 'GPS runs'}, then places the runners using the spread real fields show, so each exact position is uncertain. Width is {laneLabel}. It does not feed Proj. Updated {generated.slice(0, 16).replace('T', ' ')} UTC.
        </p>
      </details>
      <p className="mt-2 hidden max-w-3xl text-xs leading-relaxed text-ink-faint sm:block">
        The model ranks the field on track, distance, going, rail, barrier and each horse&apos;s last {noGps ? 'results' : 'GPS runs'}, then places the
        runners using the spread real fields show, so the order is the forecast and each exact position is uncertain. It does
        not feed Proj; in testing it added nothing to winner selection beyond the market. Updated {generated.slice(0, 16).replace('T', ' ')} UTC.
      </p>
    </div>
  )
}
