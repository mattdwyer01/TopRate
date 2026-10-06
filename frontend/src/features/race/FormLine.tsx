import type { FormRun } from '../../types/domain'
import { fmtWpr } from '../../lib/format'

interface FormLineProps {
  runs: FormRun[] // newest first, as stored on the runner
  projected: number | null
  sd: number | null
}

// Recent WPRs oldest to newest, then the projection as a dashed step with its typical-error band, so "is this horse trending into the
// projection or being asked to jump?" is visible at a glance.
export function FormLine({ runs, projected, sd }: FormLineProps) {
  const pts = runs
    .filter((r) => r.wpr != null)
    .slice(0, 8)
    .reverse()
    .map((r) => ({ v: r.wpr as number, d: r.date }))
  if (pts.length < 2) return <div className="text-xs text-ink-faint">Not enough rated runs to draw a form line.</div>
  const W = 420
  const H = 130
  const m = { l: 34, r: 40, t: 12, b: 20 }
  const all = [...pts.map((p) => p.v), ...(projected != null ? [projected - (sd ?? 0) / 2, projected + (sd ?? 0) / 2] : [])]
  const lo = Math.floor((Math.min(...all) - 2) / 5) * 5
  const hi = Math.ceil((Math.max(...all) + 2) / 5) * 5
  const n = pts.length + (projected != null ? 1 : 0)
  const X = (i: number) => m.l + (i / (n - 1)) * (W - m.l - m.r)
  const Y = (v: number) => m.t + (1 - (v - lo) / (hi - lo)) * (H - m.t - m.b)
  const line = pts.map((p, i) => `${i === 0 ? 'M' : 'L'}${X(i).toFixed(1)},${Y(p.v).toFixed(1)}`).join(' ')
  const px = X(n - 1)
  const lastX = X(pts.length - 1)
  const grid: number[] = []
  for (let v = lo; v <= hi; v += 5) grid.push(v)
  return (
    <svg viewBox={`0 0 ${W} ${H}`} className="block h-auto w-full max-w-md" role="img" aria-label="Recent WPRs and the projection">
      {grid.map((v) => (
        <g key={v}>
          <line x1={m.l} x2={W - m.r} y1={Y(v)} y2={Y(v)} stroke="var(--color-line)" strokeWidth={1} />
          <text x={m.l - 6} y={Y(v) + 3} textAnchor="end" fontSize={10} fill="var(--color-ink-mute)">
            {v}
          </text>
        </g>
      ))}
      {projected != null && sd != null && (
        <rect x={px - 7} y={Y(projected + sd / 2)} width={14} height={Math.max(2, Y(projected - sd / 2) - Y(projected + sd / 2))} rx={3} fill="var(--color-emerald)" fillOpacity={0.14} />
      )}
      <path d={line} fill="none" stroke="var(--color-slate)" strokeWidth={2} strokeLinejoin="round" />
      {pts.map((p, i) => (
        <g key={i}>
          <circle cx={X(i)} cy={Y(p.v)} r={3.2} fill="var(--color-panel)" stroke="var(--color-slate)" strokeWidth={1.6} />
          {(i === pts.length - 1 || i === 0) && (
            <text x={X(i)} y={Y(p.v) - 7} textAnchor="middle" fontSize={10} fontFamily="var(--font-mono)" fill="var(--color-ink-soft)">
              {Math.round(p.v)}
            </text>
          )}
        </g>
      ))}
      {projected != null && (
        <g>
          <line x1={lastX} y1={Y(pts[pts.length - 1].v)} x2={px} y2={Y(projected)} stroke="var(--color-emerald-deep)" strokeWidth={2} strokeDasharray="4 3" />
          <circle cx={px} cy={Y(projected)} r={5} fill="var(--color-emerald-deep)" stroke="#fff" strokeWidth={1.5} />
          <text x={px + 9} y={Y(projected) + 4} fontSize={12} fontWeight={600} fontFamily="var(--font-mono)" fill="var(--color-emerald-deep)">
            {fmtWpr(projected)}
          </text>
        </g>
      )}
      <text x={m.l} y={H - 5} fontSize={10} fill="var(--color-ink-mute)">
        oldest
      </text>
      <text x={px} y={H - 5} textAnchor="end" fontSize={10} fill="var(--color-ink-mute)">
        today
      </text>
    </svg>
  )
}
