import { useEffect, useMemo, useRef, useState } from 'react'
import type { TripRace, TripRunner } from '../../lib/tripMap'
import type { Runner } from '../../types/domain'
import { SPEED_MAP_TINT_THRESHOLD } from '../../lib/raceModel'

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
  smByRunId?: Record<string, number | null> // speed-map suitability vs the field (SM), shown as a dot on each chip
  compact?: boolean // silks and numbers only and always fit the box (a narrow column), whatever its width
  contenders?: Record<string, { rank: number; tier: 'core' | 'inner' }> // runners within the inner gap line of the top Rating, by runId; rank = Rating rank
  innerGap?: number // the gap line the contenders sit inside, for the wording
}

const LEADER_ZONE_L = 1.5 // runners this close to the front are the likely leaders
// A horse drawn outside another cannot settle inside it unless it is clearly ahead (it has crossed in front). Closer than this and the
// lane order has to follow the barrier order.
const CROSS_AHEAD_L = 1.5
const LANE_SEP_M = 0.4

/** Lanes (metres from the rail) with the barrier order enforced between horses that are not clear of each other lengthwise. */
export function enforceBarrierOrder<T extends { barrier: number; gx: number; lane: number }>(rows: T[]): T[] {
  const out = rows.map((r) => ({ ...r }))
  for (let pass = 0; pass < 60; pass++) {
    let moved = false
    for (const a of out) {
      for (const b of out) {
        if (a.barrier >= b.barrier) continue // a is drawn inside b
        if (a.gx - b.gx >= CROSS_AHEAD_L) continue // b is well ahead of a, so it may have crossed in front
        const need = a.lane + LANE_SEP_M - b.lane // b (drawn outside) must sit at least LANE_SEP_M wider than a
        if (need <= 0.001) continue
        moved = true
        const room = a.lane // a cannot go inside the rail
        const takeA = Math.min(need / 2, room)
        a.lane -= takeA
        b.lane += need - takeA
      }
    }
    if (!moved) break
  }
  return out
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

export function TripMap({ trip, excluded, runners: field, smByRunId = {}, compact = false, contenders = {}, innerGap = 4 }: TripMapProps) {
  const wrapRef = useRef<HTMLDivElement>(null)
  const [width, setWidth] = useState(900)
  const [hover, setHover] = useState<string | null>(null)

  useEffect(() => {
    const el = wrapRef.current
    if (!el) return
    const fit = () => {
      const w = Math.round(el.clientWidth - 2)
      setWidth(compact || w < 600 ? Math.max(300, w) : Math.max(720, w)) // phones and narrow columns fit their box, no sideways scroll
    }
    const ro = new ResizeObserver(fit)
    ro.observe(el)
    fit()
    return () => ro.disconnect()
  }, [compact])

  const byRid = useMemo(() => new Map(field.map((f) => [f.runId, f])), [field])
  // trip_map.json is only rebuilt by the daily full run, so it can hold rows the field has since lost (racing.com nominations
  // later scratched or dropped as not in TopRate's field, 15 Oct Warrnambool R5 showed 22 chips for 10 runners). Only draw
  // runners that are in the current field, and never two chips for one horse.
  const runners = useMemo(() => {
    const seen = new Set<string>()
    return trip.runners.filter((r) => {
      const f = byRid.get(r.rid)
      if (!f || f.dataScratched || excluded.has(r.rid) || r.gap == null) return false
      const key = f.horse.toLowerCase()
      if (seen.has(key)) return false
      seen.add(key)
      return true
    })
  }, [trip, excluded, byRid])

  const layout = useMemo(() => {
    const narrow = compact || width < 600
    const m = narrow ? { l: 34, r: 10, t: 22, b: 34 } : { l: 44, r: 20, t: 30, b: 44 }
    const iw = width - m.l - m.r
    const minGap = runners.length ? Math.min(...runners.map((r) => r.gap as number)) : 0
    const rows = enforceBarrierOrder(runners.map((r) => ({ ...r, gx: (r.gap as number) - minGap })))
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
  }, [runners, width, byRid, compact])

  if (!runners.length) {
    return (
      <div className="rounded-lg border border-line bg-panel p-3 text-sm text-ink-mute">No runners to map.</div>
    )
  }

  const { m, iw, ih, H, maxG, maxL, pxm, ky, X, Y, hw, hh, items } = layout
  const narrow = compact || width < 600
  const hov = items.find((r) => r.rid === hover) ?? null
  const gridG: number[] = []
  for (let g = 0; g <= maxG; g += 2) gridG.push(g)
  const gridL: number[] = []
  const stepL = maxL > 8 ? 2 : 1
  for (let l = 0; l <= maxL; l += stepL) gridL.push(l)
  const noGps = trip.laneKind === 'est'
  const cont = items.filter((r) => contenders[r.rid])
  const hasCont = cont.length >= 2
  const best = hasCont ? cont.reduce((a, b) => (b.gx < a.gx ? b : a)) : null
  const topRated = hasCont ? cont.reduce((a, b) => (contenders[b.rid].rank < contenders[a.rid].rank ? b : a)) : null
  const leaders = items.filter((r) => r.gx <= LEADER_ZONE_L)
  const numOf = (r: Placed) => byRid.get(r.rid)?.tabNumber ?? r.barrier
  let summary: string | null = null
  if (best && topRated) {
    if (best.rid === topRated.rid) {
      summary = `Top rated ${numOf(topRated)} ${topRated.name} is the best placed of the ${cont.length} contenders.`
    } else {
      const back = topRated.gx - best.gx
      const wide = topRated.lane - best.lane
      summary = `Top rated ${numOf(topRated)} ${topRated.name} is forecast ${back.toFixed(1)}L behind the best placed contender (${numOf(best)} ${best.name})${Math.abs(wide) >= 1 ? ` and ${Math.abs(wide).toFixed(1)}m ${wide > 0 ? 'wider' : 'closer to the rail'}` : ''}.`
    }
  }
  const laneLabel = noGps ? 'estimated width from rail at 800m from home (not measured)' : trip.laneKind === '800m' ? 'width from rail at 800m from home' : 'average width from rail over the whole run'

  return (
    <div className="rounded-lg border border-line bg-panel p-3 shadow-[var(--shadow-1)]">
      <div className="flex flex-wrap items-baseline justify-between gap-2">
        <span className="text-sm font-semibold text-ink">Trip map</span>
        <span className="text-xs text-ink-faint">{narrow ? (noGps ? 'Width at 800m (estimated)' : trip.laneKind === '800m' ? 'Width at 800m from home' : 'Average width, whole run') : `Projected running line · ${laneLabel}`}</span>
      </div>
      {summary && <div className="mt-1 text-xs text-ink-soft">{summary} Forecast error is about {trip.err.gap.toFixed(1)}L, so small gaps are not reliable.</div>}
      {hasCont && (
        <div className="mt-1 flex flex-wrap items-center gap-x-3 gap-y-1 text-[11px] text-ink-mute">
          <span className="inline-flex items-center gap-1"><span className="inline-block h-3 w-3 rounded-full bg-emerald-deep text-center text-[8px] font-bold leading-3 text-white">1</span>Rating rank (contenders within {innerGap} of the top)</span>
          <span className="inline-flex items-center gap-1"><span className="inline-block h-0 w-4 border-t-2 border-dashed border-emerald" />ground to the best placed contender</span>
          <span className="inline-flex items-center gap-1"><span className="inline-block h-3 w-3 rounded-sm bg-blue-bg" />likely leaders (within {LEADER_ZONE_L}L of the front)</span>
        </div>
      )}
      <div className="mt-1 text-[11px] text-ink-faint">A horse drawn wider cannot settle inside one drawn inside it unless it is {CROSS_AHEAD_L}L or more ahead (crossed in front).</div>
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
          <rect x={X(LEADER_ZONE_L)} y={m.t} width={m.l + iw - X(LEADER_ZONE_L)} height={ih} fill="var(--color-blue-bg)" opacity={0.7} />
          <text x={m.l + iw - 4} y={m.t + ih - 5} textAnchor="end" fontSize={10} fill="var(--color-blue-deep)">
            {leaders.length} likely {leaders.length === 1 ? 'leader' : 'leaders'}
          </text>
          <line x1={m.l} x2={m.l + iw} y1={Y(0)} y2={Y(0)} stroke="var(--color-ink)" strokeWidth={3} />
          {best && (
            <line x1={X(best.gx)} x2={X(best.gx)} y1={m.t} y2={m.t + ih} stroke="var(--color-emerald)" strokeWidth={1.5} strokeDasharray="5 4" />
          )}
          {best &&
            cont
              .filter((r) => r.rid !== best.rid && r.gx - best.gx >= 1.5)
              .map((r) => (
                <g key={`gt${r.rid}`}>
                  <line x1={r.px + hw} x2={X(best.gx)} y1={r.py} y2={r.py} stroke="var(--color-emerald)" strokeWidth={1.5} strokeDasharray="3 3" />
                  {topRated && r.rid === topRated.rid && (
                    <text x={r.px} y={r.py - hh - 5} textAnchor="middle" fontSize={11} fontWeight={700} fill="var(--color-emerald-deep)" stroke="var(--color-panel)" strokeWidth={3} paintOrder="stroke">
                      +{(r.gx - best.gx).toFixed(1)}L
                    </text>
                  )}
                </g>
              ))}
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
            const c = contenders[r.rid]
            return (
              <g key={r.rid} onMouseEnter={() => setHover(r.rid)} onMouseLeave={() => setHover(null)} onClick={() => setHover(on ? null : r.rid)} style={{ cursor: 'pointer' }} opacity={hasCont && !c && !on ? 0.5 : 1}>
                <rect
                  x={x}
                  y={y}
                  width={2 * hw}
                  height={CHIP_H}
                  rx={5}
                  fill={c?.tier === 'core' ? 'var(--color-emerald-tint)' : 'var(--color-panel)'}
                  stroke={on ? 'var(--color-amber)' : c ? 'var(--color-emerald)' : 'var(--color-ink-faint)'}
                  strokeWidth={on || c ? 2 : 1}
                />
                {r.silk && <image href={r.silk} x={x + 3} y={y + (CHIP_H - SILK) / 2} width={SILK} height={SILK} preserveAspectRatio="xMidYMid meet" />}
                <text x={tx} y={r.py + 4} fontSize={11} fontWeight={700} fill="var(--color-ink)">
                  {r.num}
                </text>
                {c && (
                  <g>
                    <circle cx={x} cy={y} r={7} fill="var(--color-emerald-deep)" stroke="var(--color-panel)" strokeWidth={1.5} />
                    <text x={x} y={y + 3} textAnchor="middle" fontSize={9} fontWeight={700} fill="#fff">
                      {c.rank}
                    </text>
                  </g>
                )}
                {(() => {
                  const sm = smByRunId[r.rid]
                  if (sm == null || Math.abs(sm) < SPEED_MAP_TINT_THRESHOLD) return null
                  return <circle cx={x + 2 * hw - 1} cy={y + 1} r={4} fill={sm > 0 ? 'var(--color-emerald)' : 'var(--color-rose)'} stroke="var(--color-panel)" strokeWidth={1.5} />
                })()}
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
            {contenders[hov.rid] && best && (
              <div>
                Rating rank {contenders[hov.rid].rank} (contender)
                {hov.rid === best.rid ? ', best placed of the contenders' : `, ${(hov.gx - best.gx).toFixed(1)}L behind the best placed contender`}
              </div>
            )}
            {smByRunId[hov.rid] != null && (
              <div>
                Speed map (SM) {smByRunId[hov.rid]! >= 0 ? '+' : ''}
                {smByRunId[hov.rid]!.toFixed(1)}
                {Math.abs(smByRunId[hov.rid]!) < SPEED_MAP_TINT_THRESHOLD ? ' (neutral)' : smByRunId[hov.rid]! > 0 ? ' (favourable)' : ' (unfavourable)'}
              </div>
            )}
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
      {noGps && <div className="mt-2 text-xs text-amber">No GPS at this track: gap is forecast from past 800m positions, width is estimated</div>}
    </div>
  )
}
