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
// shortLabel is for the mobile header only, where a column can be as
// narrow as ~35px (an empty/light column ceding width to busier ones -
// see the mobile layout's own comment below) - "Backmarker"/"Off
// Midfield" don't fit even wrapped at that width without CSS word-breaking
// mid-word, which read worse than just using a shorter word (real device
// feedback, 2026-09-16: the full labels visually collided with each other).
const COLUMNS = [
  { key: 'back', label: 'Backmarker', shortLabel: 'Back', lo: 5 / 6, hi: 1 },
  { key: 'offmid', label: 'Off Midfield', shortLabel: 'Off Mid', lo: 4 / 6, hi: 5 / 6 },
  { key: 'mid', label: 'Midfield', shortLabel: 'Mid', lo: 3 / 6, hi: 4 / 6 },
  { key: 'offpace', label: 'Off Pace', shortLabel: 'Off Pace', lo: 2 / 6, hi: 3 / 6 },
  { key: 'pace', label: 'Pace', shortLabel: 'Pace', lo: 1 / 6, hi: 2 / 6 },
  { key: 'lead', label: 'Leader', shortLabel: 'Lead', lo: 0, hi: 1 / 6 },
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
// genuinely hot pace to be plausible. Not flagged on Backmarker/Off
// Midfield (a wide gate settling back is the UNREMARKABLE case, not the
// one worth flagging).
// BUG (caught in browser testing before shipping): first version compared
// `columnIdx > MIDFIELD_IDX` and returned false (no caution) for exactly
// the forward columns (Off Pace/Pace/Leader) this was meant to catch -
// backwards, since higher index is MORE forward here, not less.
const MIDFIELD_IDX = 2

// A genuinely hot pace CAN excuse one wide gate crossing over into a
// forward spot without real cost - but real user feedback (2026-09-16)
// correctly points out that reading holds for AT MOST one horse per race:
// two or more wide-drawn runners can't all find a free run forward from
// the gate in the same race, no matter how fast the tempo. Previously
// every qualifying runner got the same blanket "Fast pace forgives it"
// exemption independently, which could silence the caution flag on
// several wide-and-forward runners in one race at once - implausible.
// Only the LEAST wide of the race's own qualifying group (the one most
// plausibly able to actually cross) gets the benefit of the doubt when
// the pace is Fast; every other qualifier is flagged regardless of tempo.
function computeCautionRunIds(
  runners: Runner[],
  fieldSize: number,
  columnIdxByRunId: Map<string, number>,
  tempoBucket: string,
): Set<string> {
  const candidates = runners
    .map((u) => ({
      runId: u.runId,
      drawFrac: drawFracOf(u, fieldSize),
      columnIdx: columnIdxByRunId.get(u.runId) ?? MIDFIELD_IDX,
    }))
    .filter((c) => c.drawFrac >= 2 / 3 && c.columnIdx >= MIDFIELD_IDX)
    .sort((a, b) => a.drawFrac - b.drawFrac)

  const exemptCount = tempoBucket === 'Fast' ? 1 : 0
  return new Set(candidates.slice(exemptCount).map((c) => c.runId))
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
// Widened 72 -> 92 (real user feedback, 2026-09-17: "speed map is very
// small hard to read") - desktop has the room; mobile's own compact
// renderCard path is untouched (sized separately, see its own comment).
const CARD_PX = 92
const GAP_PX = 6

// Places an already barrier-ascending list into EXPLICIT (row, col) grid
// coordinates (0-based, row 0 = TOP) - puts the highest-barrier chunk at
// the top and the rail (lowest barrier) chunk at the bottom, matching the
// barrier gauge's own fill direction and mobile's single-file reversed
// stack (real user feedback, 2026-09-17: "speed map on desktop has
// running rail at the top, not at the bottom like on mobile"). Each
// row's own left-to-right order stays ascending (this file's separate,
// still-intentional "reads inside-to-wide" convention).
//
// MUST use explicit placement, not "reverse the row-chunks and flatten
// back into CSS grid auto-placement" (a first attempt at this did that,
// see git history) - that only works when every row is fully populated.
// The moment the count isn't an exact multiple of subCols (any tactical
// column with 5 or 7+ runners, real user feedback 2026-09-17: "desktop
// speed map still does not equal mobile" on a race with a 5-runner
// bucket), the partial row is always chunked from the ascending list's
// OWN end (byproduct of Math.ceil-style chunking from the front), and
// re-flattening it into a fresh row-major grid re-derives DIFFERENT row
// boundaries than the ones just reversed - silently scrambling which
// cards share a visual row. Explicit gridRow/gridColumn placement makes
// each card's position exact regardless of how the count divides.
interface GridPlacement<T> {
  item: T
  row: number
  col: number
}

function railToBottomLayout<T>(ascending: T[], subCols: number): GridPlacement<T>[] {
  const numRows = Math.ceil(ascending.length / subCols)
  const placed: GridPlacement<T>[] = []
  for (let k = 0; k * subCols < ascending.length; k++) {
    const chunk = ascending.slice(k * subCols, (k + 1) * subCols)
    const row = numRows - 1 - k
    chunk.forEach((item, col) => placed.push({ item, row, col }))
  }
  return placed
}

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

  const cautionRunIds = computeCautionRunIds(runners, fieldSize, columnIdxByRunId, pace.tempoBucket)

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
  function renderCard(u: Runner, compact: boolean, gridPos?: { row: number; col: number }) {
    const displaySpeedMap = displaySpeedMapByRunId.get(u.runId) ?? null
    const tone = threatTone(displaySpeedMap)
    const drawFrac = drawFracOf(u, fieldSize)
    const caution = cautionRunIds.has(u.runId)
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
        style={
          compact
            ? undefined
            : {
                width: CARD_PX,
                // Explicit placement (see railToBottomLayout's own
                // comment for why auto-placement on a reversed/flattened
                // array isn't safe here) - 1-indexed, CSS grid lines
                // start at 1, not 0.
                ...(gridPos ? { gridRow: gridPos.row + 1, gridColumn: gridPos.col + 1 } : {}),
              }
        }
        className={`relative flex flex-col items-center gap-0.5 rounded-md border text-center ${
          compact ? 'w-full py-1 pl-1 pr-2.5' : 'py-1.5 pl-1.5 pr-3'
        } ${TONE_CLASSES[tone]}`}
      >
        {/* Barrier gauge, rail (bottom) to widest (top) - see drawFracOf's own
            comment. A fill growing UP FROM THE RAIL END (bottom), not a small
            floating marker at a height - real user feedback (2026-09-16): a
            short floating segment inside an already-small compact card read
            as ambiguous at a glance (which end is the rail?). A fill's empty
            bottom end IS the rail with nothing to misread, same as a real
            barrier gauge/fuel-gauge convention. */}
        <div className="pointer-events-none absolute inset-y-1 right-1 w-1 overflow-hidden rounded-full bg-line-soft">
          <div
            className={`absolute bottom-0 w-full rounded-full ${drawToneClass(drawFrac)}`}
            style={{ height: `${Math.max(8, drawFrac * 100)}%` }}
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
              compact ? 'h-3.5 w-3.5 text-[8px]' : 'h-4 w-4 text-[10px]'
            }`}
          >
            !
          </span>
        )}
        <div className="relative">
          {/* Silk size deliberately NOT scaled up with CARD_PX (92px) the
              way the rest of this card was - these are small fixed-
              resolution source images (medialityracing.com.au), and
              stretching them past their native size just upscale-blurs
              them (real user feedback, 2026-09-17: "grainy / not as clean
              as mobile" - mobile's compact silks stay at 28px, under the
              source resolution, so they never hit this). 32px (unchanged
              from before the CARD_PX widening) is close to their native
              size and stays crisp; only the card's own padding/text/
              barrier badge got bigger. */}
          {u.silkUrl ? (
            <img src={u.silkUrl} alt="" className={compact ? 'h-7 w-7 rounded-sm object-cover' : 'h-8 w-8 rounded-sm object-cover'} />
          ) : (
            <div
              className={`flex items-center justify-center rounded-sm bg-slate font-semibold text-white ${
                compact ? 'h-7 w-7 text-[10px]' : 'h-8 w-8 text-xs'
              }`}
            >
              {u.tabNumber}
            </div>
          )}
          <span
            className={`absolute rounded-full bg-ink font-bold leading-tight text-white ${
              compact ? '-right-2 -top-2 px-1 text-[9px]' : '-right-2 -top-2 px-1.5 text-xs'
            }`}
          >
            {u.barrier ?? '—'}
          </span>
        </div>
        <span className={`w-full truncate font-medium leading-tight text-ink ${compact ? 'text-[9px]' : 'text-xs'}`}>
          {compact ? u.horse : `${u.tabNumber}.${u.horse}`}
        </span>
        {u.projectedWpr != null && (
          <span className={`font-mono text-ink-faint ${compact ? 'text-[9px]' : 'text-[11px]'}`}>
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
      {/* justify-center: when the whole map is narrower than the panel
          (the common case - most races don't fill every tactical column
          with cards) this centers it instead of pinning it to the left
          edge with a large dead gap on the right (real user feedback,
          2026-09-17: "off centered"). Harmless once it's wider than the
          panel - overflow-x-auto on the parent still scrolls normally,
          justify-center on a scrollable flex container doesn't clip the
          start of the content in any browser Tailwind targets here. */}
      <div className="mt-2 hidden overflow-x-auto sm:block">
        <div className="grid min-w-full justify-center gap-1.5" style={{ gridTemplateColumns: colTemplate }}>
          {COLUMNS.map((c, i) => (
            // Label is the LAST child, after the card grid - not because
            // reading order matters here, but because it's the only way to
            // get every column's label onto the SAME shared line
            // regardless of how many rows that column has. An earlier
            // version put the label first and pushed [label, cards]
            // together as one bottom-anchored unit - that attached each
            // label to its OWN column's cards, so a 3-row column's label
            // sat near the top while a 1-row column's label sat near the
            // bottom, staircased across columns (real user feedback,
            // 2026-09-17, on a screenshot showing exactly that: "some
            // categories now above, and some below. should all be
            // below"). With the label last: the card grid (still bottom-
            // anchored via its own flex-1/justify-end, unchanged) fills
            // every column to the SAME stretched height minus one shared
            // label-row's worth, so it stops at the same line everywhere,
            // and the label - always immediately after it, same fixed
            // size for every column - lands on that same shared line too.
            <div key={c.key} className="flex min-h-[4rem] flex-col gap-1">
              <div className="flex flex-1 flex-col justify-end">
                <div
                  className="grid gap-1.5"
                  style={{ gridTemplateColumns: `repeat(${subColsFor(columns[i].length)}, ${CARD_PX}px)` }}
                >
                  {railToBottomLayout(columns[i], subColsFor(columns[i].length)).map(({ item, row, col }) =>
                    renderCard(item, false, { row, col }),
                  )}
                </div>
              </div>
              <div className="text-center text-[10px] font-semibold uppercase tracking-wide text-ink-faint">
                {c.label}
              </div>
            </div>
          ))}
        </div>
      </div>

      {/* Mobile: keeps the same 6-columns-side-by-side shape as desktop
          (not stacked into 6 full-width sections - tried that, real user
          pushback: it lost the "who's alongside whom" reading and burned a
          lot of vertical scroll) but as one flex row that always fits the
          viewport width, so nothing needs horizontal scrolling either
          (real user feedback, 2026-09-16: the desktop grid cut off
          Leader/Pace off-screen on a 390px phone). Gets there by shrinking
          (compact renderCard: smaller silk/text) and dropping the
          sub-column wrapping (always single-file per column, unlike
          desktop's subColsFor).
          A plain even 6-way split (grid-cols-6) still read too small on a
          real device (user feedback, 2026-09-16: "text is small and very
          hard to read") - an EMPTY tactical column (no runner predicted to
          settle there, common for Backmarker/Leader on a small field) was
          claiming a full 1/6 of the width for nothing. flex-basis below
          gives an empty column only enough width for its own label and
          hands the rest to columns that actually have cards, so those get
          bigger before falling back to shrinking further. On a big field
          where every column has runners this converges back to an even
          split - there's no width left to redistribute - so cards can't
          rely on emptiness alone and are still sized to survive that case. */}
      <div className="mt-2 flex items-stretch gap-1 sm:hidden">
        {COLUMNS.map((c, i) => (
          <div
            key={c.key}
            className="flex min-w-0 flex-col"
            style={{ flex: columns[i].length > 0 ? '1 1 0%' : '0.55 1 0%' }}
          >
            <div className="truncate text-center text-[8px] font-semibold uppercase leading-tight text-ink-faint">
              {c.shortLabel}
            </div>
            {/* justify-end (not just a reversed order): pins every column's
                rail card to the SAME bottom baseline regardless of how many
                cards it holds. A light column (fewer runners predicted to
                settle there) is naturally shorter than a busy one - with
                plain top-down stacking (flex-col alone, no justify-end) a
                light column's cards start level with the busy column's but
                run out early, leaving empty space at ITS bottom instead -
                which reads as "no horse near the rail here" even though
                that's just an artifact of card count, not a real gap in
                barrier draws (real user feedback, 2026-09-16: this looked
                like horses "avoiding the inside rail", which doesn't happen
                in a real barrier draw). Anchoring to the bottom instead
                means any leftover space sits at the TOP (under the label),
                and every column's rail-most card lines up on one shared
                inside-rail line. */}
            <div className="mt-1 flex flex-1 flex-col justify-end gap-1">
              {/* Reversed from columns[i]'s own ascending order (kept as-is
                  for the desktop sub-column wrapping above, where ascending
                  reads left-to-right as inside-to-wide) - this is a single
                  top-to-bottom stack instead, and real user feedback
                  (2026-09-16) wants the rail at the BOTTOM of that stack,
                  same as SpeedMap.tsx's own bar view (sorted descending so
                  barrier 1 is the last/bottom row) and this file's own
                  per-card barrier gauge (fills up from the bottom). Without
                  this, the two views agreed on the gauge/fill direction but
                  still disagreed on card ORDER - ascending put the rail
                  card at the TOP of the stack instead. */}
              {[...columns[i]].reverse().map((u) => renderCard(u, true))}
            </div>
          </div>
        ))}
      </div>
    </div>
  )
}
