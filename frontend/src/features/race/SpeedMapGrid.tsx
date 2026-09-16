import type { Race, Runner } from '../../types/domain'
import { estimatePace } from '../../lib/pace'

interface SpeedMapGridProps {
  race: Race
  runners: Runner[]
}

// 6 tactical columns, Backmarker (left) -> Leader (right) - matches the
// Racing NSW speed map layout this was modelled on (rows of silks bucketed
// by predicted running position, not a bar chart). predictedRelSettle is
// continuous 0-1 (0 = leads, 1 = settles last, see toprate_daily.py's
// _settle_rel_lookup) - split into 6 even bands, reversed since column 0
// here is the BACK of the field.
const COLUMNS = [
  { key: 'back', label: 'Backmarker', lo: 5 / 6, hi: 1 },
  { key: 'offmid', label: 'Off Midfield', lo: 4 / 6, hi: 5 / 6 },
  { key: 'mid', label: 'Midfield', lo: 3 / 6, hi: 4 / 6 },
  { key: 'offpace', label: 'Off Pace', lo: 2 / 6, hi: 3 / 6 },
  { key: 'pace', label: 'Pace', lo: 1 / 6, hi: 2 / 6 },
  { key: 'lead', label: 'Leader', lo: 0, hi: 1 / 6 },
]

// predictedRelSettle needs a fresh rebuild to be populated (added Sep 2026 -
// older cached payloads only have the 4-way predictedSettlingBand string).
// Falls back to that band's own midpoint so a stale payload still places
// runners sensibly instead of dumping everyone in one column; total unknown
// falls back to 0.5 (mid of Midfield/Off Pace boundary), same "unknown ->
// middle" convention SpeedMap.tsx's own barPct() uses.
const BAND_MIDPOINT: Record<string, number> = {
  Leader: 0.1,
  'On-pace': 0.325,
  Midfield: 0.575,
  Back: 0.85,
}

function relSettleOf(u: Runner): number {
  if (u.predictedRelSettle != null) return u.predictedRelSettle
  if (u.predictedSettlingBand && BAND_MIDPOINT[u.predictedSettlingBand] != null) {
    return BAND_MIDPOINT[u.predictedSettlingBand]
  }
  return 0.5
}

function columnIndexOf(rel: number): number {
  // Explicit [lo, hi] range check, not "first column whose hi is >= rel" -
  // COLUMNS is ordered for DISPLAY (Backmarker first, Leader last), and
  // Backmarker's own hi is 1, so a naive first-match-on-hi-alone search put
  // every runner in Backmarker regardless of rel (caught in browser
  // testing - a real bug, not a hypothetical one).
  const idx = COLUMNS.findIndex((c) => rel >= c.lo && rel <= c.hi)
  return idx === -1 ? COLUMNS.length - 1 : idx
}

// Highlights the ALREADY-computed speed_map ADJ_TERM (own history + today's
// field/barrier/pace context combined - see wpr_projection.py's
// _SPEED_MAP_FEATURES docstring) rather than re-deriving a cruder inside-
// threats proxy from barrier/position alone: it's the real, validated
// signal for "is today's context helping or hurting this horse", already
// exposed per-runner via adjustmentBreakdown.
const THREAT_THRESHOLD = 0.5

function threatTone(speedMapAdj: number | undefined | null): 'help' | 'hurt' | 'neutral' {
  if (speedMapAdj == null) return 'neutral'
  if (speedMapAdj <= -THREAT_THRESHOLD) return 'hurt'
  if (speedMapAdj >= THREAT_THRESHOLD) return 'help'
  return 'neutral'
}

const TONE_CLASSES: Record<'help' | 'hurt' | 'neutral', string> = {
  help: 'border-emerald-line bg-emerald-bg',
  hurt: 'border-rose-line bg-rose-bg',
  neutral: 'border-line-soft bg-bg',
}

// Grid layout: one card per runner, bucketed into a tactical-position column
// and stacked (ordered by barrier ascending) within it - lets bunching in a
// column read as "contested for that spot", the same way Racing NSW's own
// speed maps do, without inventing a separate crowding metric.
export function SpeedMapGrid({ race, runners }: SpeedMapGridProps) {
  const pace = estimatePace(race, runners)

  if (!runners.length) {
    return (
      <div className="rounded-lg border border-line bg-panel p-3 text-sm text-ink-mute">
        No runners to map.
      </div>
    )
  }

  const columns: Runner[][] = COLUMNS.map(() => [])
  for (const u of runners) {
    columns[columnIndexOf(relSettleOf(u))].push(u)
  }
  for (const col of columns) {
    col.sort((a, b) => (a.barrier ?? 99) - (b.barrier ?? 99))
  }

  return (
    <div className="rounded-lg border border-line bg-panel p-3 shadow-[var(--shadow-1)]">
      <div className="flex flex-wrap items-baseline justify-between gap-2">
        <span className="text-sm font-semibold text-ink">Speed map</span>
        <span className="text-xs text-ink-faint">
          Predicted running position &middot; tint = today&apos;s context (green helps, red hurts)
        </span>
        <span className="rounded-full bg-bg px-2 py-0.5 font-mono text-xs text-ink-mute">
          {pace.display}
        </span>
      </div>
      <div className="mt-2 grid grid-cols-6 gap-1.5">
        {COLUMNS.map((c, i) => (
          <div key={c.key} className="flex flex-col gap-1">
            <div className="text-center text-[10px] font-semibold uppercase tracking-wide text-ink-faint">
              {c.label}
            </div>
            <div className="flex min-h-[3rem] flex-col gap-1">
              {columns[i].map((u) => {
                const tone = threatTone(u.adjustmentBreakdown?.speed_map)
                const title =
                  u.adjustmentBreakdown?.speed_map != null
                    ? `speed_map adjustment: ${u.adjustmentBreakdown.speed_map > 0 ? '+' : ''}${u.adjustmentBreakdown.speed_map.toFixed(1)}`
                    : undefined
                return (
                  <div
                    key={u.runId}
                    title={title}
                    className={`flex flex-col items-center gap-0.5 rounded-md border px-1 py-1 text-center ${TONE_CLASSES[tone]}`}
                  >
                    <div className="relative">
                      {u.silkUrl ? (
                        <img src={u.silkUrl} alt="" className="h-6 w-6 rounded-sm object-cover" />
                      ) : (
                        <div className="flex h-6 w-6 items-center justify-center rounded-sm bg-slate text-[10px] font-semibold text-white">
                          {u.tabNumber}
                        </div>
                      )}
                      <span className="absolute -right-1.5 -top-1.5 rounded-full bg-ink px-1 text-[9px] font-bold leading-tight text-white">
                        {u.barrier ?? '—'}
                      </span>
                    </div>
                    <span className="w-full truncate text-[10px] font-medium leading-tight text-ink">
                      {u.tabNumber}.{u.horse}
                    </span>
                    {u.projectedWpr != null && (
                      <span className="font-mono text-[9px] text-ink-faint">{u.projectedWpr.toFixed(1)}</span>
                    )}
                  </div>
                )
              })}
            </div>
          </div>
        ))}
      </div>
    </div>
  )
}
