import { useMemo } from 'react'
import type { Race } from '../../types/domain'
import { findOutline, useTrackOutlines } from '../../lib/trackOutlines'

// Small course outline for the race header (21 Oct 2026): the running rail from OpenStreetMap with the home straight at the bottom, the stretch this race runs
// from its start to the winning post picked out in blue, a green start dot and a black post dot. Needs track_marks for the venue (finish, starts); without a mapped
// start for this distance only the post is drawn.

const W = 150
const H = 76
const PAD = 8

export function TrackMini({ race }: { race: Race }) {
  const payload = useTrackOutlines()
  const outline = findOutline(payload, race.venue)
  const g = useMemo(() => {
    if (!outline || !outline.fin) return null
    const n0 = outline.pts.length
    const a = outline.pts[outline.s0 % n0]
    const b = outline.pts[(outline.s0 + outline.sn) % n0]
    const rot = (p: [number, number], t: number): [number, number] => [p[0] * Math.cos(-t) - p[1] * Math.sin(-t), p[0] * Math.sin(-t) + p[1] * Math.cos(-t)]
    let th = Math.atan2(b[1] - a[1], b[0] - a[0])
    let R = outline.pts.map((p) => rot(p, th))
    const cy = R.reduce((s, p) => s + p[1], 0) / n0
    if ((R[outline.s0 % n0][1] + R[(outline.s0 + outline.sn) % n0][1]) / 2 > cy) {
      th += Math.PI
      R = outline.pts.map((p) => rot(p, th))
    }
    const key = String(race.distance)
    const start = outline.starts?.[key] ?? outline.chutes?.[key]?.[1] ?? null
    const fin = rot(outline.fin, th)
    const st = start ? rot(start, th) : null
    const chute = outline.chutes?.[key] ? ([rot(outline.chutes[key][0], th), rot(outline.chutes[key][1], th)] as [[number, number], [number, number]]) : null
    const allChutes = Object.values(outline.chutes ?? {}).map((c) => [rot(c[0], th), rot(c[1], th)] as [[number, number], [number, number]])
    const xs = [...R.map((p) => p[0]), ...allChutes.map((c) => c[1][0])]
    const ys = [...R.map((p) => p[1]), ...allChutes.map((c) => c[1][1])]
    const minX = Math.min(...xs)
    const maxX = Math.max(...xs)
    const minY = Math.min(...ys)
    const maxY = Math.max(...ys)
    const sc = Math.min((W - 2 * PAD) / (maxX - minX || 1), (H - 2 * PAD) / (maxY - minY || 1))
    const ox = (W - (maxX - minX) * sc) / 2
    const oy = (H - (maxY - minY) * sc) / 2
    const P = (p: [number, number]): [number, number] => [ox + (p[0] - minX) * sc, oy + (maxY - p[1]) * sc]
    const ring = R.map(P)
    const idx = (p: [number, number]) => {
      let best = 0
      let bd = Infinity
      R.forEach((q, i) => {
        const d = (q[0] - p[0]) ** 2 + (q[1] - p[1]) ** 2
        if (d < bd) {
          bd = d
          best = i
        }
      })
      return best
    }
    // racing direction along the ring's point order
    const area = R.reduce((s, p, i) => s + (p[0] * R[(i + 1) % n0][1] - R[(i + 1) % n0][0] * p[1]), 0) / 2
    const ccwOrder = area > 0
    const step = (outline.dir === 'ccw') === ccwOrder ? 1 : -1
    const fi = idx(fin)
    let route = ''
    let line: [number, number][] = []
    if (st) {
      let i = idx(st)
      const pts: [number, number][] = []
      if (chute) pts.push(P(chute[1]), P(chute[0]))
      const toPost = (((fi - i) * step) % n0 + n0) % n0
      const laps = race.distance >= outline.perim * 0.97 ? 1 : 0 // a race of a lap or more: the whole circuit is run
      for (let k = 0; k < laps * n0 + toPost; k++) {
        pts.push(ring[i])
        i = (i + step + n0) % n0
      }
      pts.push(ring[fi])
      line = pts
      route = pts.map(([x, y], j) => `${j ? 'L' : 'M'}${x.toFixed(1)} ${y.toFixed(1)}`).join('')
    }
    // direction arrows: along the run when there is one, otherwise three round the circuit
    if (!line.length) {
      for (let k = 0; k <= n0; k++) line.push(ring[(((fi + k * step) % n0) + n0) % n0])
    }
    const arrows: { x: number; y: number; a: number }[] = []
    const count = route ? Math.max(1, Math.min(4, Math.round(line.length / 18))) : 3
    for (let k = 0; k < count; k++) {
      const j = Math.floor(((k + 0.5) / count) * (line.length - 1))
      const p0 = line[Math.max(j - 1, 0)]
      const p1 = line[Math.min(j + 1, line.length - 1)]
      arrows.push({ x: line[j][0], y: line[j][1], a: (Math.atan2(p1[1] - p0[1], p1[0] - p0[0]) * 180) / Math.PI })
    }
    const chutesDrawn = allChutes.map((c) => `M${P(c[0])[0].toFixed(1)} ${P(c[0])[1].toFixed(1)}L${P(c[1])[0].toFixed(1)} ${P(c[1])[1].toFixed(1)}`).join('')
    const d = ring.map(([x, y], i) => `${i ? 'L' : 'M'}${x.toFixed(1)} ${y.toFixed(1)}`).join('') + 'Z'
    return { d, chutesDrawn, arrows, hasRoute: !!route, route, start: st ? (chute ? P(chute[1]) : P(st)) : null, fin: P(fin) }
  }, [outline, race.distance])
  if (!g) return null
  return (
    <div className="flex-none" title={`${race.venue}: ${race.distance}m from the start to the post. Track outline: Map data © OpenStreetMap contributors`}>
      <svg viewBox={`0 0 ${W} ${H}`} role="img" aria-label={`${race.venue} course outline`} className="h-auto w-[150px]">
        <path d={g.d} fill="none" stroke="var(--color-line)" strokeWidth={5} strokeLinejoin="round" />
        {g.chutesDrawn && <path d={g.chutesDrawn} fill="none" stroke="var(--color-line)" strokeWidth={3} strokeLinecap="butt" />}
        {g.route && <path d={g.route} fill="none" stroke="#2563eb" strokeWidth={2.4} strokeLinejoin="round" strokeLinecap="round" />}
        {g.arrows.map((a, i) => (
          <path key={i} d="M-2.6 -2.4L2.2 0L-2.6 2.4Z" transform={`translate(${a.x.toFixed(1)} ${a.y.toFixed(1)}) rotate(${a.a.toFixed(0)})`} fill={g.hasRoute ? '#fff' : 'var(--color-ink-faint)'} stroke={g.hasRoute ? '#1d4ed8' : 'none'} strokeWidth={0.8} strokeLinejoin="round" />
        ))}
        {g.start && <circle cx={g.start[0]} cy={g.start[1]} r={3.4} fill="#a3e635" stroke="var(--color-ink)" strokeWidth={1} />}
        <circle cx={g.fin[0]} cy={g.fin[1]} r={3.4} fill="var(--color-ink)" stroke="white" strokeWidth={1} />
      </svg>
      <div className="mt-0.5 flex items-center justify-end gap-2 text-[10px] text-ink-faint">
        {g.start && (
          <span className="inline-flex items-center gap-1">
            <i className="inline-block h-2 w-2 rounded-full border border-ink bg-lime-400" />
            Start
          </span>
        )}
        <span className="inline-flex items-center gap-1">
          <i className="inline-block h-2 w-2 rounded-full bg-ink" />
          Post
        </span>
      </div>
    </div>
  )
}
