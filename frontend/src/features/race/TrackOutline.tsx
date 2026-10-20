import { useMemo } from 'react'
import type { Race } from '../../types/domain'
import { findOutline, useTrackOutlines } from '../../lib/trackOutlines'

// The course drawn from OpenStreetMap: the running rail, the longest straight picked out, and how far this race goes round it.
// Turned so the home straight is at the bottom (not north up): the longest straight, or the one the notes name for tracks with start marks. The outline gives the shape of the
// track (tight or sweeping, long or short straight). Where track_marks.json has notes for the course the winning post, the chutes and this race's start are drawn too; those are
// read by hand off plan maps and are approximate.

const W = 300
const H = 190
const PAD = 16
const TRACK_M = 22 // drawn width of the track band, metres

function fmtM(n: number) {
  return `${Math.round(n).toLocaleString('en-AU')}m`
}

export function TrackOutline({ race }: { race: Race }) {
  const payload = useTrackOutlines()
  const outline = findOutline(payload, race.venue)
  const geom = useMemo(() => {
    if (!outline) return null
    // Turn the ring so the longest straight runs along the bottom (rotation only, no mirroring).
    const n0 = outline.pts.length
    const a = outline.pts[outline.s0 % n0]
    const b = outline.pts[(outline.s0 + outline.sn) % n0]
    let th = Math.atan2(b[1] - a[1], b[0] - a[0])
    const rot1 = ([x, y]: [number, number], t: number): [number, number] => [x * Math.cos(-t) - y * Math.sin(-t), x * Math.sin(-t) + y * Math.cos(-t)]
    const rot = (t: number) => outline.pts.map(([x, y]) => [x * Math.cos(-t) - y * Math.sin(-t), x * Math.sin(-t) + y * Math.cos(-t)] as [number, number])
    let R = rot(th)
    const cy = R.reduce((acc, p) => acc + p[1], 0) / n0
    const sy = (R[outline.s0 % n0][1] + R[(outline.s0 + outline.sn) % n0][1]) / 2
    if (sy > cy) {
      th += Math.PI
      R = rot(th)
    }
    const rp = (q: [number, number]) => rot1(q, th)
    const fin = outline.fin ? rp(outline.fin) : null
    const starts: Record<string, [number, number]> = {}
    for (const [k, v] of Object.entries(outline.starts ?? {})) starts[k] = rp(v)
    const chutes: Record<string, [[number, number], [number, number]]> = {}
    for (const [k, v] of Object.entries(outline.chutes ?? {})) chutes[k] = [rp(v[0]), rp(v[1])]
    const extra: [number, number][] = Object.values(chutes).flat()
    const xs = [...R, ...extra].map((p) => p[0])
    const ys = [...R, ...extra].map((p) => p[1])
    const minX = Math.min(...xs)
    const maxX = Math.max(...xs)
    const minY = Math.min(...ys)
    const maxY = Math.max(...ys)
    const scale = Math.min((W - 2 * PAD) / (maxX - minX || 1), (H - 2 * PAD) / (maxY - minY || 1))
    const ox = (W - (maxX - minX) * scale) / 2
    const oy = (H - (maxY - minY) * scale) / 2
    const pt = ([x, y]: [number, number]) => [ox + (x - minX) * scale, oy + (maxY - y) * scale] as const
    const P = R.map(pt)
    const d = P.map(([x, y], i) => `${i ? 'L' : 'M'}${x.toFixed(1)} ${y.toFixed(1)}`).join('') + 'Z'
    const n = P.length
    const run: (readonly [number, number])[] = []
    for (let i = 0; i <= outline.sn; i++) run.push(P[(outline.s0 + i) % n])
    const sd = run.map(([x, y], i) => `${i ? 'L' : 'M'}${x.toFixed(1)} ${y.toFixed(1)}`).join('')
    const q = (p: [number, number]) => pt(p)
    return { d, sd, scale, fin: fin && q(fin), starts: Object.fromEntries(Object.entries(starts).map(([k, v]) => [k, q(v)])), chutes: Object.fromEntries(Object.entries(chutes).map(([k, v]) => [k, [q(v[0]), q(v[1])] as const])) }
  }, [outline])
  if (!outline || !geom) return null
  const key = String(race.distance)
  const ownStart = geom.starts[key] ?? geom.chutes[key]?.[1] ?? null
  const hasMarks = !!geom.fin
  const laps = race.distance / outline.perim
  const lapText = laps < 0.95 ? `${Math.round(laps * 100)}% of a lap` : laps < 1.05 ? 'about one lap' : `${laps.toFixed(1)} laps`
  const scaleBarM = 500
  const sbPx = scaleBarM * geom.scale
  return (
    <section className="rounded-lg border border-line bg-panel px-3 py-2.5 shadow-[var(--shadow-1)] sm:px-4">
      <div className="flex flex-wrap items-baseline justify-between gap-x-3">
        <h3 className="text-sm font-semibold text-ink">Track shape</h3>
        <span className="text-[11px] text-ink-faint">{hasMarks ? 'Outline from OpenStreetMap, home straight at the bottom' : 'Outline from OpenStreetMap, longest straight at the bottom'}</span>
      </div>
      <div className="mt-1.5 flex flex-col gap-3 sm:flex-row sm:items-center">
        <svg viewBox={`0 0 ${W} ${H}`} role="img" aria-label={`${race.venue} track outline`} className="h-auto w-full max-w-[340px] flex-none self-center sm:w-[300px]">
          <path d={geom.d} fill="none" stroke="var(--color-line)" strokeWidth={Math.max(6, TRACK_M * geom.scale)} strokeLinejoin="round" />
          <path d={geom.d} fill="none" stroke="var(--color-ink-mute)" strokeWidth={1.2} strokeLinejoin="round" />
          <path d={geom.sd} fill="none" stroke="var(--color-emerald)" strokeWidth={4} strokeLinecap="round" />
          {Object.entries(geom.chutes).map(([k, c]) => (
            <line key={`c${k}`} x1={c[0][0]} y1={c[0][1]} x2={c[1][0]} y2={c[1][1]} stroke={k === key ? 'var(--color-ink)' : 'var(--color-ink-faint)'} strokeWidth={k === key ? 2 : 1.2} strokeDasharray="3 2" />
          ))}
          {geom.fin && (
            <g>
              <circle cx={geom.fin[0]} cy={geom.fin[1]} r={4.5} fill="var(--color-bad, #dc2626)" stroke="white" strokeWidth={1} />
              <text x={geom.fin[0]} y={geom.fin[1] + 15} fontSize={9} textAnchor="middle" fill="var(--color-ink-mute)">Finish</text>
            </g>
          )}
          {ownStart && (
            <g>
              <rect x={ownStart[0] - 4} y={ownStart[1] - 4} width={8} height={8} rx={1} fill="var(--color-ink)" stroke="white" strokeWidth={1} />
              <text x={ownStart[0] + 7} y={ownStart[1] + 3} fontSize={9} fontWeight={600} fill="var(--color-ink)">
                {fmtM(race.distance)}
              </text>
            </g>
          )}
          <g transform={`translate(${PAD} ${H - 8})`}>
            <line x1={0} x2={sbPx} y1={0} y2={0} stroke="var(--color-ink-mute)" strokeWidth={1.5} />
            <line x1={0} x2={0} y1={-3} y2={3} stroke="var(--color-ink-mute)" strokeWidth={1.5} />
            <line x1={sbPx} x2={sbPx} y1={-3} y2={3} stroke="var(--color-ink-mute)" strokeWidth={1.5} />
            <text x={sbPx + 5} y={3} fontSize={10} fill="var(--color-ink-mute)">
              {scaleBarM}m
            </text>
          </g>
        </svg>
        <dl className="grid min-w-0 flex-1 grid-cols-2 gap-x-4 gap-y-2 text-xs">
          <div>
            <dt className="text-[10px] font-semibold uppercase tracking-wide text-ink-faint">Circuit (rail)</dt>
            <dd className="font-mono text-sm font-semibold text-ink">{fmtM(outline.perim)}</dd>
          </div>
          <div>
            <dt className="text-[10px] font-semibold uppercase tracking-wide text-ink-faint">This race</dt>
            <dd className="font-mono text-sm font-semibold text-ink">
              {fmtM(race.distance)} <span className="font-sans text-xs font-normal text-ink-mute">{lapText}</span>
            </dd>
          </div>
          <div>
            <dt className="flex items-center gap-1 text-[10px] font-semibold uppercase tracking-wide text-ink-faint">
              <span className="inline-block h-1 w-3 rounded-full bg-emerald" />
              Longest straight
            </dt>
            <dd className="font-mono text-sm font-semibold text-ink">about {fmtM(outline.straight)}</dd>
          </div>
          <div>
            <dt className="text-[10px] font-semibold uppercase tracking-wide text-ink-faint">Bend radius</dt>
            <dd className="font-mono text-sm font-semibold text-ink">{outline.radius ? `about ${fmtM(outline.radius)}` : '-'}</dd>
          </div>
          <p className="col-span-2 text-[11px] leading-snug text-ink-faint">
            Shape and length are measured from the mapped rail, so they can be a few percent off.{' '}
            {hasMarks
              ? ownStart
                ? 'The finish, chutes (dashed) and this start are placed by hand from plan maps, so treat them as approximate.'
                : 'The finish and chutes (dashed) are placed by hand from plan maps; this distance has no mapped start.'
              : 'The start and finish are not marked for this course.'}{' '}
            Geometry added almost nothing to the rating model in testing, so this is for reading the course, not part of the projection.
          </p>
        </dl>
      </div>
    </section>
  )
}
