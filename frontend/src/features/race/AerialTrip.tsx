import { useEffect, useMemo, useState } from 'react'
import type { Race } from '../../types/domain'
import { AERIAL_LABELS, AERIAL_LEADER_RIGHT, hkCourse, loadAerialRace, pxPerLength } from '../../lib/hkAerial'
import type { AerialRace } from '../../lib/hkAerial'

// How a Hong Kong race was actually run: four snapshots from HKJC's aerial replay image (lengths behind the leader across,
// metres off the inside rail down). A reading aid for past races, not a projection; the rail distance is measured from the dot
// centre with a scale checked against HKJC's official margins, so treat it as good to about a metre. A horse more than about
// 16 lengths back runs off the picture and is missing from that snapshot.

const W = 300
const H = 130
const M = { l: 26, r: 8, t: 14, b: 18 }

interface Dot {
  num: string
  gap: number
  rail: number
  pla: number | null
}

function frameDots(a: AerialRace, k: number, ppl: number): Dot[] {
  const raw = Object.entries(a.runners ?? {}).flatMap(([num, r]) => {
    const f = r.frames[k]
    return f && f.rail_m != null ? [{ num, x: f.x, rail: f.rail_m, pla: r.pla }] : []
  })
  if (!raw.length) return []
  const right = AERIAL_LEADER_RIGHT[k]
  const lead = right ? Math.max(...raw.map((d) => d.x)) : Math.min(...raw.map((d) => d.x))
  return raw.map((d) => ({ num: d.num, gap: Math.abs(d.x - lead) / ppl, rail: d.rail, pla: d.pla }))
}

export function AerialTrip({ race }: { race: Race }) {
  const [data, setData] = useState<{ race: AerialRace; course: string } | null>(null)
  const eligible = race.allResulted && hkCourse(race.venue) != null

  useEffect(() => {
    let live = true
    setData(null)
    if (eligible) loadAerialRace(race.date, race.venue, race.raceNumber).then((d) => live && setData(d))
    return () => {
      live = false
    }
  }, [eligible, race.date, race.venue, race.raceNumber])

  const panels = useMemo(() => {
    if (!data) return []
    const ppl = pxPerLength(data.course)
    return AERIAL_LABELS.map((label, k) => ({ label, dots: frameDots(data.race, k, ppl) }))
  }, [data])

  if (!data || !panels.some((p) => p.dots.length)) return null

  const maxGap = Math.max(6, Math.ceil(Math.max(...panels.flatMap((p) => p.dots.map((d) => d.gap))) / 2) * 2 + 1)
  const maxRail = Math.max(8, Math.ceil(Math.max(...panels.flatMap((p) => p.dots.map((d) => d.rail))) / 2) * 2 + 1)
  const iw = W - M.l - M.r
  const ih = H - M.t - M.b
  const X = (g: number) => M.l + iw - (g / maxGap) * iw
  const Y = (r: number) => M.t + (r / maxRail) * ih

  return (
    <div className="rounded-lg border border-line bg-panel p-3 shadow-[var(--shadow-1)]">
      <div className="flex flex-wrap items-baseline justify-between gap-2">
        <span className="text-sm font-semibold text-ink">How it ran</span>
        <span className="text-xs text-ink-faint">Hong Kong aerial replay · lengths behind the leader, metres off the rail</span>
      </div>
      <div className="mt-2 grid grid-cols-1 gap-3 sm:grid-cols-2">
        {panels.map((p) => (
          <div key={p.label}>
            <div className="text-xs font-medium text-ink-mute">{p.label}</div>
            <svg viewBox={`0 0 ${W} ${H}`} className="w-full" role="img" aria-label={`${p.label}: positions of each runner`}>
              <rect x={M.l} y={M.t} width={iw} height={ih} fill="var(--color-bg)" />
              {[0, 5, 10, 15].filter((g) => g <= maxGap).map((g) => (
                <g key={g}>
                  <line x1={X(g)} x2={X(g)} y1={M.t} y2={M.t + ih} stroke="var(--color-line)" />
                  <text x={X(g)} y={H - 5} textAnchor="middle" fontSize={9} fill="var(--color-ink-mute)">{g === 0 ? 'lead' : `${g}L`}</text>
                </g>
              ))}
              {[0, 4, 8, 12, 16].filter((r) => r <= maxRail).map((r) => (
                <text key={r} x={M.l - 4} y={Y(r) + 3} textAnchor="end" fontSize={9} fill="var(--color-ink-mute)">{r}m</text>
              ))}
              <line x1={M.l} x2={M.l + iw} y1={Y(0)} y2={Y(0)} stroke="var(--color-ink)" strokeWidth={2} />
              {p.dots.map((d) => (
                <g key={d.num}>
                  <title>{`#${d.num}${d.pla ? `, finished ${d.pla}` : ''}: ${d.gap.toFixed(1)}L behind the leader, ${d.rail.toFixed(1)}m off the rail`}</title>
                  <circle cx={X(d.gap)} cy={Y(d.rail)} r={7} fill={d.pla === 1 ? 'var(--color-emerald)' : 'var(--color-panel)'} stroke={d.pla === 1 ? 'var(--color-emerald)' : 'var(--color-ink-faint)'} />
                  <text x={X(d.gap)} y={Y(d.rail) + 3} textAnchor="middle" fontSize={8} fontWeight={700} fill={d.pla === 1 ? '#fff' : 'var(--color-ink)'}>{d.num}</text>
                </g>
              ))}
            </svg>
          </div>
        ))}
      </div>
    </div>
  )
}
