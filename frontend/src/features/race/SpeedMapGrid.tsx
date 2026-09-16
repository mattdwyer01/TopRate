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
// _SPEED_MAP_FEATURES docstring), but DEMEANED AGAINST THIS RACE FOR
// DISPLAY ONLY - never fed back into wpr_projection.py or any WPR number
// shown elsewhere on the page.
//
// WHY: real user pushback (2026-09-16), and correct - "every horse having
// a positive speed_map is impossible" if this tile is claiming to show
// tactical/positional advantage, which is inherently zero-sum (there is
// exactly one rail run, one clear passage up the outside, etc; nobody's
// gain there comes for free). speed_map itself is NOT purely that,
// though: two of its inputs (track_bias_score, pace_score) are shared or
// near-shared across a race's WHOLE field by construction - they're a
// genuine correction for how WPR itself rates performances at a specific
// track/going/rail/pace combination, not a claim about who wins the
// tactical battle. That component is real, validated signal for the
// PREDICTION (confirmed the hard way: stripping it out backend-wide via
// per-race demeaning, matching track_barrier/closing_merit/etc, was tried
// and reverted after held-out MAE got meaningfully worse, 6.039 -> 6.078)
// - it should NOT be removed from the number wpr_projection.py actually
// uses. But it has no business being IN a chart that's specifically
// asking "who's advantaged by today's traffic/positioning", which is the
// one thing here that genuinely cannot be true for everyone at once.
// Demeaning against this race's own mean, for this chart's tint only,
// removes exactly that shared component and leaves the genuinely
// relational part - and makes "every tile green" mathematically
// impossible by construction (a race's own values can't all sit above
// their own mean), which is the property being asked for here.
const THREAT_THRESHOLD = 0.5

function threatTone(displaySpeedMap: number | undefined | null): 'help' | 'hurt' | 'neutral' {
  if (displaySpeedMap == null) return 'neutral'
  if (displaySpeedMap <= -THREAT_THRESHOLD) return 'hurt'
  if (displaySpeedMap >= THREAT_THRESHOLD) return 'help'
  return 'neutral'
}

const TONE_CLASSES: Record<'help' | 'hurt' | 'neutral', string> = {
  help: 'border-emerald-line bg-emerald-bg',
  hurt: 'border-rose-line bg-rose-bg',
  neutral: 'border-line-soft bg-bg',
}

// Barrier position, rail (0) to widest (1) - rendered as a vertical gauge
// with the rail at the BOTTOM, to match SpeedMap.tsx's own bar view
// (sorted barrier descending so barrier 1 sits at the base of the list -
// "reads like the track from the inside out"). Real user feedback
// (2026-09-16): the two views used different orientations for the same
// idea (this one ran rail-to-wide left-to-right), which made them harder
// to cross-reference when flicking between Grid and Bar. Column placement
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

// How many side-by-side sub-columns to wrap a tactical column's runners
// into, once there are enough of them that a single-file vertical stack
// gets awkwardly tall (real user feedback, 2026-09-16: an 18-horse field
// crammed 8-deep into Midfield/Pace read as an undifferentiated list, not
// as horses actually running alongside each other at different widths).
// Runners are already sorted by barrier ascending before this is used, and
// CSS grid's default auto-flow (row: fills left-to-right, then wraps) means
// the LEFTMOST card in any given row is always more inside than the one to
// its right - a genuine spatial "how wide" cue, not just a shorter list.
function subColsFor(n: number): number {
  if (n > 6) return 3
  if (n > 3) return 2
  return 1
}

// Fixed per-card pixel width (not a fraction of viewport) - real user
// feedback (2026-09-16): squeezing 6 columns, some wrapped 3-wide, into
// one phone-width row via fractional grid columns made every card too
// small to read (tiny silks, truncated names). Each tactical column now
// gets exactly `subColsFor(n) * CARD_PX + gaps` pixels regardless of
// screen width, and the whole row scrolls horizontally on a narrow
// screen instead of shrinking - same "wider than the viewport on
// purpose, overflow-x-auto scrolls it" pattern RunnerRow/RaceDetail's
// own runner table already uses.
const CARD_PX = 72
const GAP_PX = 6

// Grid layout: one card per runner, bucketed into a tactical-position
// column, wrapped into subColsFor(n) side-by-side sub-columns (ordered by
// barrier ascending, so left-to-right within a row also reads inside-to-
// wide) - lets both "contested for that spot" (bunching) and "how wide
// within that spot" (sub-column position) read visually, the same way
// Racing NSW's own speed maps spread a crowded tactical slot sideways
// rather than stacking it into one long single-file column.
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

  // Display-only demeaning against THIS race's own speed_map values - see
  // threatTone's own comment above for why. Never touches wpr_projection.py
  // or any WPR number shown elsewhere; this Map only feeds the tint below.
  const rawSpeedMaps = runners
    .map((u) => u.adjustmentBreakdown?.speed_map)
    .filter((v): v is number => v != null)
  const raceMean = rawSpeedMaps.length ? rawSpeedMaps.reduce((a, b) => a + b, 0) / rawSpeedMaps.length : 0
  const displaySpeedMapByRunId = new Map<string, number | null>()
  for (const u of runners) {
    const v = u.adjustmentBreakdown?.speed_map
    displaySpeedMapByRunId.set(u.runId, v != null ? v - raceMean : null)
  }

  const colTemplate = columns
    .map((col) => {
      const n = subColsFor(col.length)
      return `${n * CARD_PX + (n - 1) * GAP_PX}px`
    })
    .join(' ')

  // Shared per-runner card, used by both the desktop (fixed CARD_PX,
  // multiple sub-columns side by side, whole row scrolls horizontally) and
  // mobile (compact, single sub-column, fills its 1/6-width grid cell)
  // layouts below - see each layout's own comment for why they differ.
  function renderCard(u: Runner, compact: boolean) {
    const displaySpeedMap = displaySpeedMapByRunId.get(u.runId) ?? null
    const tone = threatTone(displaySpeedMap)
    const drawFrac = drawFracOf(u, fieldSize)
    const columnIdx = columnIdxByRunId.get(u.runId) ?? MIDFIELD_IDX
    const caution = needsCaution(drawFrac, columnIdx, pace.tempoBucket)
    const titleParts = [
      // Name first and always - narrower cards from subColsFor's
      // wrapping (desktop) or the compact mobile size truncate the
      // visible name more aggressively, so the full name needs to be
      // recoverable on hover even when the tabNumber alone isn't enough
      // to place it.
      `${u.tabNumber}. ${u.horse}`,
      u.barrier != null ? `Barrier ${u.barrier} of ${fieldSize}` : null,
      displaySpeedMap != null
        ? `speed_map vs this field's average: ${displaySpeedMap > 0 ? '+' : ''}${displaySpeedMap.toFixed(1)}`
        : null,
      caution ? "Wide gate for how forward this position is - needs early speed or a hot pace to be plausible" : null,
    ].filter(Boolean)
    return (
      <div
        key={u.runId}
        title={titleParts.join(' · ') || undefined}
        style={compact ? undefined : { width: CARD_PX }}
        className={`relative flex flex-col items-center gap-0.5 rounded-md border text-center ${
          compact ? 'w-full py-1 pl-1 pr-2' : 'py-1.5 pl-1.5 pr-3'
        } ${TONE_CLASSES[tone]}`}
      >
        {/* Barrier gauge, rail (bottom) to widest (top) - see drawFracOf's own comment */}
        <div
          className={`pointer-events-none absolute inset-y-1 rounded-full bg-line-soft ${
            compact ? 'right-0.5 w-0.5' : 'inset-y-1.5 right-1 w-1'
          }`}
        >
          <div
            className={`absolute w-full rounded-full ${drawToneClass(drawFrac)}`}
            style={{ height: '15%', bottom: `${Math.min(85, drawFrac * 100)}%` }}
          />
        </div>
        {caution && (
          // Positioned INSIDE the card (not overflowing outside it) -
          // an earlier version used a negative offset that overflowed
          // into the gap between narrow columns, making the badge
          // look attached to the wrong neighboring card (caught in
          // browser testing: the underlying logic was already
          // correct, only the badge's own placement was ambiguous).
          <span
            className={`absolute left-0.5 top-0.5 flex items-center justify-center rounded-full bg-amber font-bold leading-none text-white ${
              compact ? 'h-3 w-3 text-[7px]' : 'h-3.5 w-3.5 text-[9px]'
            }`}
          >
            !
          </span>
        )}
        <div className="relative">
          {u.silkUrl ? (
            <img src={u.silkUrl} alt="" className={compact ? 'h-6 w-6 rounded-sm object-cover' : 'h-8 w-8 rounded-sm object-cover'} />
          ) : (
            <div
              className={`flex items-center justify-center rounded-sm bg-slate font-semibold text-white ${
                compact ? 'h-6 w-6 text-[9px]' : 'h-8 w-8 text-xs'
              }`}
            >
              {u.tabNumber}
            </div>
          )}
          <span
            className={`absolute rounded-full bg-ink font-bold leading-tight text-white ${
              compact ? '-right-1.5 -top-1.5 px-0.5 text-[8px]' : '-right-2 -top-2 px-1 text-[10px]'
            }`}
          >
            {u.barrier ?? '—'}
          </span>
        </div>
        <span className={`w-full truncate font-medium leading-tight text-ink ${compact ? 'text-[8px]' : 'text-[11px]'}`}>
          {compact ? u.horse : `${u.tabNumber}.${u.horse}`}
        </span>
        {u.projectedWpr != null && (
          <span className={`font-mono text-ink-faint ${compact ? 'text-[8px]' : 'text-[10px]'}`}>
            {u.projectedWpr.toFixed(1)}
          </span>
        )}
      </div>
    )
  }

  return (
    <div className="rounded-lg border border-line bg-panel p-3 shadow-[var(--shadow-1)]">
      <div className="flex flex-wrap items-baseline justify-between gap-2">
        <span className="text-sm font-semibold text-ink">Speed map</span>
        <span className="text-xs text-ink-faint">
          Predicted running position &middot; tint = vs the rest of THIS field (green favoured, red hurt) &middot;
          side bar = barrier (rail at base, wide at top) &middot; ! = wide gate sitting forward
        </span>
        <span className="rounded-full bg-bg px-2 py-0.5 font-mono text-xs text-ink-mute">
          {pace.display}
        </span>
      </div>

      {/* Desktop/tablet: unchanged fixed-width sub-column grid, whole row
          scrolls horizontally when it doesn't fit - keeps every card at its
          full, readable CARD_PX size (real user feedback, 2026-09-16: a
          fractional/shrink-to-fit width made silks and names too small to
          read). Hidden below sm since a phone-width viewport can't fit even
          one full row of 6 tactical columns side by side without either
          shrinking cards or scrolling horizontally - both ruled out for
          mobile by this component's own further-below layout instead. */}
      <div className="mt-2 hidden overflow-x-auto sm:block">
        <div className="grid gap-1.5" style={{ gridTemplateColumns: colTemplate }}>
          {COLUMNS.map((c, i) => (
            <div key={c.key} className="flex flex-col gap-1">
              <div className="text-center text-[10px] font-semibold uppercase tracking-wide text-ink-faint">
                {c.label}
              </div>
              <div
                className="grid min-h-[4rem] gap-1.5"
                style={{ gridTemplateColumns: `repeat(${subColsFor(columns[i].length)}, ${CARD_PX}px)` }}
              >
                {columns[i].map((u) => renderCard(u, false))}
              </div>
            </div>
          ))}
        </div>
      </div>

      {/* Mobile: keeps the same 6-columns-side-by-side shape as desktop
          (not stacked into 6 full-width sections - tried that, real user
          pushback: it lost the "who's alongside whom" reading and burned a
          lot of vertical scroll) but as one `grid-cols-6` row that always
          fits the viewport width, so nothing needs horizontal scrolling
          either (real user feedback, 2026-09-16: the desktop grid cut off
          Leader/Pace off-screen on a 390px phone). Gets there by shrinking
          (compact renderCard: smaller silk/text) and dropping the
          sub-column wrapping (always single-file per column, unlike
          desktop's subColsFor) rather than by giving each column more
          width - the two together are what keep 6 real columns on screen
          without either scrolling or losing the side-by-side layout. */}
      <div className="mt-2 grid grid-cols-6 gap-1 sm:hidden">
        {COLUMNS.map((c, i) => (
          <div key={c.key} className="flex flex-col gap-1">
            <div className="text-center text-[7px] font-semibold uppercase leading-tight tracking-wide text-ink-faint">
              {c.label}
            </div>
            <div className="flex flex-col gap-1">
              {columns[i].map((u) => renderCard(u, true))}
            </div>
          </div>
        ))}
      </div>
    </div>
  )
}
