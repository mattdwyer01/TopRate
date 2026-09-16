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
//
// NOT necessarily relative to rivals (real user question, 2026-09-16: "how
// does every horse have a positive speed_map in this race?"): two of its
// inputs (track_bias_score, pace_score) are shared/near-shared across a
// race's WHOLE field by construction, and a fix attempted to strip that
// shared component out (per-race demeaning, matching what track_barrier/
// closing_merit/etc already get) was tried and REVERTED after a same-run
// held-out MAE check showed it was a real, meaningful accuracy regression
// (6.039 -> 6.078) - that shared component turned out to be genuine
// predictive signal (e.g. a track/going/rail combo that legitimately runs
// faster than grade norm), not noise to remove. So a uniformly-green (or
// uniformly-red) race is a real, expected outcome sometimes, not a bug -
// see this file's own tooltip/legend text, which says so rather than
// implying a head-to-head comparison that isn't actually being made.
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

// Barrier position, rail (0) to widest (1) - same centring convention
// wpr_projection.py's barrier_nudge()/draw_signal use. Column placement
// alone can't distinguish "sits midfield from an inside gate" (routine)
// from "sits midfield from barrier 14 of 14" (requires either genuine
// early speed to cross rivals, or a hot enough pace that the field
// bunches up) - real user feedback (2026-09-16): a wide-drawn runner
// shown in the same column as an inside-drawn one, with nothing marking
// the difference, reads as a mistake even when the underlying WPR number
// is fine. This surfaces barrier position directly instead of leaving it
// to be inferred from the small badge number alone.
function drawFracOf(u: Runner, fieldSize: number): number {
  if (u.barrier == null || fieldSize < 2) return 0.5
  return Math.max(0, Math.min(1, (u.barrier - 1) / (fieldSize - 1)))
}

function drawToneClass(drawFrac: number): string {
  if (drawFrac >= 2 / 3) return 'bg-rose'
  if (drawFrac >= 1 / 3) return 'bg-amber'
  return 'bg-emerald'
}

// Caution flag: a wide gate (outer third) placed in a column at Midfield
// or more forward (index >= MIDFIELD_IDX - COLUMNS runs Backmarker(0) ->
// Leader(5), so "more forward" means a HIGHER index) is the exact
// scenario that needs either early speed spent crossing rivals or a
// genuinely hot pace to be plausible - see this function's own caller for
// the pace gate. Not flagged on Backmarker/Off Midfield (a wide gate
// settling back is the UNREMARKABLE case, not the one worth flagging).
// BUG (caught in browser testing before shipping): first version compared
// `columnIdx > MIDFIELD_IDX` and returned false (no caution) for exactly
// the forward columns (Off Pace/Pace/Leader) this was meant to catch -
// backwards, since higher index is MORE forward here, not less.
const MIDFIELD_IDX = 2

function needsCaution(drawFrac: number, columnIdx: number, tempoBucket: string): boolean {
  if (drawFrac < 2 / 3 || columnIdx < MIDFIELD_IDX) return false
  return tempoBucket !== 'Fast'
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

  const fieldSize = runners.length
  const columns: Runner[][] = COLUMNS.map(() => [])
  const columnIdxByRunId = new Map<string, number>()
  for (const u of runners) {
    const idx = columnIndexOf(relSettleOf(u))
    columns[idx].push(u)
    columnIdxByRunId.set(u.runId, idx)
  }
  for (const col of columns) {
    col.sort((a, b) => (a.barrier ?? 99) - (b.barrier ?? 99))
  }

  return (
    <div className="rounded-lg border border-line bg-panel p-3 shadow-[var(--shadow-1)]">
      <div className="flex flex-wrap items-baseline justify-between gap-2">
        <span className="text-sm font-semibold text-ink">Speed map</span>
        <span className="text-xs text-ink-faint">
          Predicted running position &middot; tint = today&apos;s pace/barrier/track context (green helps, red
          hurts - can apply to the WHOLE field, not just vs rivals) &middot; bar = barrier (rail to wide) &middot; !
          = wide gate sitting forward
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
                const drawFrac = drawFracOf(u, fieldSize)
                const columnIdx = columnIdxByRunId.get(u.runId) ?? MIDFIELD_IDX
                const caution = needsCaution(drawFrac, columnIdx, pace.tempoBucket)
                const titleParts = [
                  u.barrier != null ? `Barrier ${u.barrier} of ${fieldSize}` : null,
                  u.adjustmentBreakdown?.speed_map != null
                    ? `speed_map adjustment: ${u.adjustmentBreakdown.speed_map > 0 ? '+' : ''}${u.adjustmentBreakdown.speed_map.toFixed(1)}`
                    : null,
                  caution ? "Wide gate for how forward this position is - needs early speed or a hot pace to be plausible" : null,
                ].filter(Boolean)
                return (
                  <div
                    key={u.runId}
                    title={titleParts.join(' · ') || undefined}
                    className={`relative flex flex-col items-center gap-0.5 rounded-md border px-1 py-1 text-center ${TONE_CLASSES[tone]}`}
                  >
                    {caution && (
                      // Positioned INSIDE the card (not overflowing outside it) -
                      // an earlier version used a negative offset that overflowed
                      // into the gap between narrow columns, making the badge
                      // look attached to the wrong neighboring card (caught in
                      // browser testing: the underlying logic was already
                      // correct, only the badge's own placement was ambiguous).
                      <span className="absolute left-0.5 top-0.5 flex h-3 w-3 items-center justify-center rounded-full bg-amber text-[8px] font-bold leading-none text-white">
                        !
                      </span>
                    )}
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
                    {/* Barrier position, rail (left) to widest (right) - see drawFracOf's own comment */}
                    <div className="h-[3px] w-full rounded-full bg-line-soft">
                      <div
                        className={`h-full rounded-full ${drawToneClass(drawFrac)}`}
                        style={{ width: '15%', marginLeft: `${Math.min(85, drawFrac * 100)}%` }}
                      />
                    </div>
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
