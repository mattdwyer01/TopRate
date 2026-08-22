import type { Race, Runner } from '../../types/domain'
import { estimatePace } from '../../lib/pace'

interface SpeedMapProps {
  race: Race
  runners: Runner[]
}

// Bar length places the tip inside the settling position's zone (quarter),
// so it reads as "how far into Back/Midfield/On-pace/Lead this horse sits" -
// ported from the old dashboard's renderSpeedMapBars bar-length formula.
function barPct(pos: number | null): number {
  if (pos == null) return 38 // unknown -> mid of Midfield
  let base: number
  let frac: number
  if (pos <= 2) {
    base = 75
    frac = (2 - pos) / 1.5
  } else if (pos <= 4) {
    base = 50
    frac = (4 - pos) / 2
  } else if (pos <= 8) {
    base = 25
    frac = (8 - pos) / 4
  } else {
    base = 0
    frac = Math.max(0, (14 - pos) / 6)
  }
  const pct = base + Math.max(0, Math.min(1, frac)) * 25
  return Math.max(14, Math.min(100, pct + 10))
}

const ZONES = [
  { key: 'back', label: 'Back' },
  { key: 'mid', label: 'Midfield' },
  { key: 'onpace', label: 'On-pace' },
  { key: 'lead', label: 'Lead' },
]

// Horizontal bar chart: one row per runner, ordered by barrier descending so
// the rail (barrier 1) sits at the bottom - reads like the track from the
// inside out. Bar length = early speed via predicted settling position.
export function SpeedMap({ race, runners }: SpeedMapProps) {
  const pace = estimatePace(race, runners)

  if (!runners.length) {
    return (
      <div className="rounded-lg border border-line bg-panel p-3 text-sm text-ink-mute">
        No runners to map.
      </div>
    )
  }

  const sorted = [...runners].sort((a, b) => {
    const ba = a.barrier ?? -1
    const bb = b.barrier ?? -1
    if (ba !== bb) return bb - ba
    return (a.avgSettledPos ?? 99) - (b.avgSettledPos ?? 99)
  })

  return (
    <div className="rounded-lg border border-line bg-panel p-3 shadow-[var(--shadow-1)]">
      <div className="flex flex-wrap items-baseline justify-between gap-2">
        <span className="text-sm font-semibold text-ink">Speed map</span>
        <span className="text-xs text-ink-faint">
          Barrier (rail at base) &middot; bar = early speed &middot; label = predicted WPR
        </span>
        <span className="rounded-full bg-bg px-2 py-0.5 font-mono text-xs text-ink-mute">
          {pace.display}
        </span>
      </div>
      <div className="mt-2 grid grid-cols-4 text-center text-[10px] uppercase tracking-wide text-ink-faint">
        {ZONES.map((z) => (
          <span key={z.key}>{z.label}</span>
        ))}
      </div>
      <div className="relative mt-1 flex flex-col gap-1">
        <div className="pointer-events-none absolute inset-0 grid grid-cols-4">
          {ZONES.map((z) => (
            <div key={z.key} className="border-l border-line-soft first:border-l-0" />
          ))}
        </div>
        {sorted.map((u) => {
          const pct = barPct(u.avgSettledPos)
          return (
            <div key={u.runId} className="relative flex items-center gap-2">
              <span className="w-5 shrink-0 text-right font-mono text-xs text-ink-faint">
                {u.barrier ?? '—'}
              </span>
              <div className="relative h-5 flex-1">
                <div
                  className="flex h-full items-center rounded-sm bg-emerald-bg px-1.5"
                  style={{ width: `${pct.toFixed(1)}%` }}
                >
                  <span className="truncate whitespace-nowrap text-xs font-medium text-emerald-deep">
                    {u.tabNumber}. {u.horse}
                    {u.projectedWpr != null ? `  ${u.projectedWpr.toFixed(1)}` : ''}
                  </span>
                </div>
              </div>
            </div>
          )
        })}
      </div>
    </div>
  )
}
