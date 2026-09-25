import type { Runner } from '../../types/domain'
import { compositeScore, SPEED_MAP_TINT_THRESHOLD, type EffectiveRunner } from '../../lib/raceModel'
import type { TrackerQualifier } from '../../lib/trackerRules'
import { fmtInt, fmtPrice, fmtWpr } from '../../lib/format'
import { computePriceMove, MOVE_DISPLAY_THRESHOLD_PCT } from '../../lib/priceMove'
import { spellPosition } from '../../lib/spellPosition'

interface RunnerRowProps {
  runner: Runner
  raceDate: string
  compact: boolean
  selected: boolean
  effective?: EffectiveRunner
  trackerQualifier?: TrackerQualifier
  onClick: () => void
}

// Low-volume (Tracker B) implies the stronger, more selective edge in
// backtesting (see speedmap_jockey_tracker.py's own docstring) - shown in
// green to read as the "better" of the two when a runner qualifies for
// both, same visual convention as a WON result badge elsewhere in the app.
// High-volume-only (Tracker A) gets a distinct colour (indigo) rather than
// a fainter version of the same one, so the two are easy to tell apart at a
// glance, not just by tooltip.
function trackerFireTitle(q: TrackerQualifier): string {
  const which = q.qualifiesB ? 'Low-volume tracker pick (stronger edge)' : 'High-volume tracker pick'
  const price = q.price != null ? `, $${q.price.toFixed(2)}+` : ''
  return `${which}: ${q.tag}, ${q.gapWpr.toFixed(1)} WPR off top rated, jockey ${q.jw.toFixed(1)}% (90d)${price}`
}

// Meets the tactical criteria but no pick fires here, for one of two
// reasons (real user feedback, 2026-09-16: "for those races with more
// than 1 horse that fits the criteria, these should be flagged as such...
// also show if there is a solo pick under $3"):
//   - contested: another runner in the race meets the criteria too, so
//     solo-only fails.
//   - underPrice: this IS the only runner meeting the criteria, but its
//     own price is under the $3 floor.
// Shown outlined rather than filled - "almost, not actually" - so it's
// never mistaken for an actual pick at a glance.
function trackerSkippedTitle(q: TrackerQualifier): string {
  const isB = q.contestedB || q.underPriceB
  const which = isB ? 'low-volume' : 'high-volume'
  const reason =
    q.contestedA || q.contestedB
      ? 'another runner in this race meets it too (contested)'
      : "it's the only runner meeting it, priced under $3"
  return `Meets the ${which} tracker criteria, but ${reason} - no pick fires (solo-only)`
}

function fmtJockeyWin(v: number | null): string {
  if (v == null) return '—'
  return `${Math.round(v)}%`
}

function fmtAdj(v: number | null): string {
  if (v == null) return '—'
  const f = v.toFixed(1)
  return v > 0 ? `+${f}` : f
}

// Connections' own rating, shown inline after their name rather than
// buried at the bottom of the runner detail - omitted entirely (not "(—)")
// when absent so a name without a rating doesn't grow an empty parenthetical.
function ratingSuffix(v: number | null): string {
  return v == null ? '' : ` (${Math.round(v)})`
}

// A single responsive row - NOT a separate desktop-table/mobile-card pair
// (the current dashboard dual-renders every data grid; this is the
// consolidation the rebuild plan calls for). Both breakpoints are a real
// CSS grid with columns - the same shape RaceDetail's header row uses -
// they just use a different grid-template. Below sm, Proj/TopRate/Form/
// Jockey Win%/Fixed $/FP (Full) or just Proj/TopRate/Fixed $/FP (Compact)
// are real columns - Base/Adj/RTS/Actual stay desktop-only (see
// COMPACT_MOBILE/FULL_MOBILE grid-cols below and RaceDetail's matching
// MOBILE_COLUMN_LABELS_COMPACT/_FULL). Real user feedback (2026-09-16,
// after Peak/Adj were first dropped from this summary view entirely):
// "remove base from mobile race summary, re-add adj to desktop" - so Base
// is desktop-only like RTS/Actual, Adj is back but desktop-only too,
// neither ever shows on mobile in either density. Silk+name are `sticky
// left-0`/`left-12` so they stay in view (frozen) while the stat columns
// that don't fit scroll underneath (Full only - Compact fits without
// scrolling entirely, see its own grid-cols comment), same "frozen first
// column" pattern MeetingsGrid already uses for its own wide table.
export function RunnerRow({
  runner,
  raceDate,
  compact,
  selected,
  effective,
  trackerQualifier,
  onClick,
}: RunnerRowProps) {
  const rowPadding = compact ? 'py-1.5' : 'py-2.5'
  const scratched = effective?.scratched ?? false
  const isOverlay = effective?.isOverlay ?? false
  // driftedToOverlay is always a subset of isOverlay (see raceModel.ts), so
  // it takes over that row's tint (amber, a warning) rather than adding to
  // it. firmedToUnderlay never overlaps isOverlay (by definition it's priced
  // under our fair value), so it gets its own green tint on rows that would
  // otherwise have none. Badges used to carry this instead of the row tint
  // itself - moved to a highlight (Sep 2026) so it reads at a glance across
  // a whole race rather than needing to spot small text next to each name.
  const drifted = effective?.driftedToOverlay ?? false
  const backedIn = effective?.firmedToUnderlay ?? false
  const spell = spellPosition(runner.formHistory, raceDate)
  // Scratched: force to null rather than falling back to the model's raw
  // (pre-scratch) projectedWpr - a scratched runner has no live rating any
  // more, it shouldn't look like it's still rated just because
  // effective.effectiveProjectedWpr is explicitly null (which ?? would
  // otherwise treat the same as "no override, use the raw value").
  const displayProj = scratched ? null : (effective?.effectiveProjectedWpr ?? runner.projectedWpr)
  const displayComposite = scratched ? null : compositeScore(runner, effective?.effectiveProjectedWpr)
  const overridden = effective?.hasOverride ?? false
  const priceMove = computePriceMove(runner.openFixedPrice, runner.fixedWinPrice)
  const showMove = priceMove != null && priceMove.pctChange >= MOVE_DISPLAY_THRESHOLD_PCT

  // RTS isn't worth its own sortable mobile column (it's not something
  // anyone sorts by day-to-day, unlike Proj/TopRate) - on mobile it rides
  // along with the name/jockey-trainer text instead to save a column's
  // worth of scroll width; desktop keeps its own dedicated column, shared
  // styling/tooltip extracted here so the two don't drift apart.
  const rtsColorClass =
    spell.label === 'FU'
      ? 'font-semibold text-amber'
      : spell.label === 'FS'
        ? 'font-semibold text-indigo'
        : 'text-ink-mute'
  const rtsTitle =
    spell.label === 'FS'
      ? 'First starter - no prior race starts'
      : spell.daysSince != null
        ? `${spell.daysSince} days since last run`
        : undefined

  // The two sticky (frozen) cells need a background that matches the row's
  // own state, not a fixed one - otherwise a selected/hovered row would
  // visibly split as soon as you scroll it sideways. `group` + group-hover
  // carries the row's :hover state down to them (JS can't see :hover).
  // Real user feedback (2026-09-16): the overlay/drift/backed-in row tint
  // removed below (see the row className's own comment) - selected/
  // scratched are the only states with a background left.
  const stickyBg = selected ? 'bg-emerald-bg' : 'bg-panel group-hover:bg-bg'

  return (
    // A div, not a button - a real scratch-toggle <button> needs to nest
    // inside this row (invalid HTML and unpredictable click behaviour
    // inside a native <button>), so this is role=button + keyboard handling
    // instead, to keep the same click-anywhere-to-open-modal behaviour and
    // accessibility a real button gave for free.
    <div
      role="button"
      tabIndex={0}
      onClick={onClick}
      onKeyDown={(e) => {
        if (e.key === 'Enter' || e.key === ' ') {
          e.preventDefault()
          onClick()
        }
      }}
      title={
        drifted
          ? 'Was a material underlay at today\'s open price, has since drifted into an overlay - a possible bad sign (market may know something the model doesn\'t), not a validated buy signal'
          : backedIn
            ? 'Was a material overlay at today\'s open price, has since been backed into an underlay - the market has grown more confident in this runner than it started (and than our own price)'
            : isOverlay
              ? 'Overlay: market price is longer than our fair price'
              : undefined
      }
      className={`group grid min-w-full cursor-pointer items-center gap-y-0.5 border-b border-line-soft px-2 text-left text-sm transition-colors sm:gap-x-2 sm:grid-cols-[44px_36px_1fr_56px_56px_60px_60px_56px_52px_44px_56px_60px_68px_52px] ${
        // Neither mobile density ever shows Base/Adj (desktop-only, see
        // sm:grid-cols above - real user feedback, 2026-09-16: "remove base
        // from mobile race summary, re-add adj to desktop"). Compact drops
        // Form/Jockey Win% too and uses the tightest gap, fitting within a
        // phone's own width with no horizontal scroll at all (verified down
        // to 360px). Fixed $'s own track was too narrow (42px, then 56px on
        // a first attempt) for a real 2-decimal price like "$41.00"/
        // "$101.00" plus the move-arrow slot - real user feedback
        // (2026-09-17, screenshots on two separate races): "mobile layout
        // broken" / "not fixed". Measured the actual rendered gap via
        // Playwright bounding boxes rather than guessing again: the price
        // text doesn't overflow its own cell (box model is exactly right),
        // but a 6+ character price consumes almost the entire track with
        // nothing left over, so the visual gap to the Jockey Win% column
        // beside it collapses to ~3px (illegible, reads as touching) vs
        // ~11px for a short price like "$1.35" - the box was technically
        // correct but too tight to read. Widened to 68px (matching
        // desktop's own width) first - measured gap for a 6-char price
        // improved (~15px) but a rarer 7-char price like "$101.00" was
        // still only ~7px - widened again to 76px, giving every realistic
        // price a consistently comfortable gap.
        //
        // That 76px Fixed $ fix was verified in isolation and shipped, but
        // never re-checked against the FULL row's total width - it wasn't:
        // measured via Playwright at a real 393px viewport (2026-09-17,
        // "you have still not fixed the mobile layout"), Full's row was
        // 31px wider than its own scroll container, forcing every viewer
        // to scroll to see FP at all - and scrolling that far pushed Proj
        // back UNDER the sticky silk/name cells instead of just revealing
        // FP, which looks broken rather than merely tight. Recovered that
        // 31px+ from the columns that don't need to hold a wide value
        // (Horse 84->68, Proj 40->36, TopRate/Form 28->26, Jockey Win%
        // 30->28, gap 4px->2px) rather than re-touching Fixed $ - verified
        // via the same Playwright measurement that the full row now fits
        // with zero scroll at 393px (a small margin to spare) and only a
        // few px at 360px, matching Compact's own standard.
        //
        // That fix was ALSO only verified at narrow widths (360-430px) and
        // shipped as "fixed" a 4th time before actually being fixed (real
        // user feedback, 2026-09-17, with a screenshot on a wider phone):
        // every column above was a bare fixed px track under a `w-max` row
        // (a block element pinned to exactly its content's width, not
        // `auto`), so on ANY viewport wider than the fixed-column total
        // (~390-639px - most large phones, not just tablets) the row just
        // stopped growing, leaving the rest of the card blank instead of
        // using the space - confirmed via Playwright at 430-639px, an
        // EXACT visual match to the reported screenshot (table occupying
        // only the left third of the card). Fixed by making the Horse
        // column `minmax(Npx, 1fr)` instead of a bare px value, and the
        // row `min-w-full` instead of `w-max`, on BOTH densities - below
        // the min, it holds its floor and the row overflows into the
        // existing horizontal scroll exactly as before (verified: 360px
        // behaviour unchanged); above it, the grid now actually fills the
        // container and the slack goes into the one column that can
        // usefully absorb it (longer horse names show), instead of empty
        // space.
        //
        // While checking that fix at a range of widths, found Compact
        // (the DEFAULT density, not Full) had its OWN long-standing Fixed $
        // overflow: its track was still 44px, the exact "too narrow for a
        // real price" size Full started at and had to widen to 76px after
        // three rounds. Every one of those rounds only ever tested Full,
        // so Compact's own copy of the same bug went unnoticed - confirmed
        // by cropping a screenshot to exactly the TopRate cell's own box at
        // a completely ordinary 393px width: a 2-digit TopRate value like
        // "96" rendered as "9$", the "6" invisible - not touching, gone -
        // because Fixed $'s own content (needs ~70px+ for "$101.00" plus
        // the arrow slot) overflows its 44px box (overflow: visible, so it
        // renders, just backward over whatever painted before it) far
        // enough to fully cover the previous cell's last character. Fixed
        // the same way as Full: widened Fixed $ to the same proven 76px,
        // recovered the difference from Horse's own floor/Proj/TopRate
        // (each has real slack - a 2-3 digit rating/percent doesn't need
        // as much room as this cost).
        //
        // The header labels reusing the desktop words (TopRate/Form/Jky
        // Win%) were never actually readable in these tracks either -
        // `truncate` just turned them into "To...''/"Fo...''/"Jky...''
        // fragments (real user feedback, 2026-09-17: "columns aren't
        // readable"). Given their own short mobile-only labels instead
        // (see MOBILE_COLUMN_LABELS_FULL/_COMPACT: TR/Fm/J%) - free, no
        // width cost, since the DATA cells were already sized to their
        // actual content, only the header text was the problem.
        //
        // While checking that, found the accepted "a few px of scroll at
        // 360px" from the earlier fix was not actually harmless: scrolled
        // all the way to reveal FP, Proj's own value was partially covered
        // by the sticky name cell (e.g. "72.2" rendered as "2.2") - the
        // same failure mode as the wider-viewport bug this session already
        // fixed, just smaller. Recovered the remaining ~16px purely from
        // Horse's own floor (68->52) - it only matters on the narrowest
        // phones in the first place (1fr already overrides it everywhere
        // else), and the name span already truncates with an ellipsis, so
        // a few more px of a long name/jockey line truncating is a much
        // smaller cost than a WPR figure silently losing a digit. Verified
        // zero scroll needed now at 360px too, not just 393px+.
        //
        // Still not enough (real user feedback, 2026-09-17, on a wide
        // phone where Horse had plenty of room via 1fr): TopRate/Form/Jky%
        // sit right next to Fixed $, which is 76px wide to survive a rare
        // "$101.00" - three ~26-28px columns packed at a 2px gap read as
        // visibly cramped next to it regardless of how much slack Horse
        // itself has, since gap and column width are independent of 1fr.
        // Checked alignment first (exact per-column pixel match, header vs
        // data, at 430/480/540px) to rule out an actual bug before
        // touching anything - this was purely a density complaint.
        // AskUserQuestion on the tradeoff (real user choice, confirmed):
        // widen TopRate/Form/Jky% and the gap between them, recovered from
        // Horse's floor again (52->39) rather than dropping Form from
        // mobile Full - horse names already truncate with an ellipsis, so
        // truncating a bit sooner there is the smaller cost. Must match
        // RaceDetail's own compact/full mobile grid-cols/gap and
        // MOBILE_COLUMN_LABELS_COMPACT/_FULL exactly.
        //
        // TR swapped for Combo, both densities (2026-09-19, real user
        // request: "sort by combo by default... on mobile show combo
        // column, hide TR" - see raceModel.ts's own compositeScore()
        // comment for what Combo is). Combo shows a decimal WPR-scale
        // value like Proj (e.g. "76.6"), not a bare 2-3 digit integer
        // like TR - given its own track the same width as Proj's rather
        // than TR's narrower one (compact 30->40, full 29->36), recovered
        // from Horse's own floor again (compact 90->80, full 50->43) per
        // this file's own established pattern above, rather than
        // reopening the Fixed $/Jky%/Fm width fights already settled.
        // Full mobile gained a 9th track for SM Adj (2026-09-19, direct
        // follow-up: "not seeing it" on mobile - see the SM Adj cell's own
        // comment above). Compact's own grid-cols is untouched - SM Adj
        // stays hidden there, same as Form/Jockey Win% already are.
        // Horse's floor trimmed 43->38 (a smaller cut than this file's
        // usual "recover it all from Horse" pattern - the remaining width
        // is left to the row's existing horizontal-scroll fallback at the
        // very narrowest phones rather than squeezing the name column to
        // the point of being unreadable) to make room for a new 30px SM
        // Adj track. Positioned between J% and Fixed $ (moved here
        // 2026-09-19, direct follow-up: "sm should be between j% and
        // fixed" - was originally right after Horse).
        compact
          ? 'gap-x-1 grid-cols-[40px_minmax(80px,1fr)_40px_40px_76px_20px]'
          : 'gap-x-[3px] grid-cols-[40px_minmax(38px,1fr)_36px_36px_29px_31px_30px_76px_20px]'
      } ${rowPadding} ${
        // Overlay/drift/backed-in row tint removed (real user feedback,
        // 2026-09-16) - the tooltip above still explains a row's overlay
        // state on hover, this just stops highlighting it visually across
        // the whole race table.
        scratched
          ? 'opacity-50'
          : selected
            ? 'bg-emerald-bg'
            : 'hover:bg-bg'
      }`}
    >
      <span className={`sticky left-0 z-10 -ml-2 pl-2 sm:static sm:z-auto sm:m-0 sm:p-0 ${stickyBg}`}>
        {runner.silkUrl ? (
          <img src={runner.silkUrl} alt="" className="h-9 w-9 flex-none rounded-sm object-contain" />
        ) : (
          <span className="block h-9 w-9 flex-none sm:h-auto sm:w-auto" />
        )}
      </span>
      <span className="hidden font-mono text-ink-mute sm:inline">{runner.tabNumber}</span>
      {/* left-12 (48px), not left-10 (40px) - the silk cell above is 40px
          per its grid track, but its own -ml-2 pl-2 (to flush it against
          the row's true left edge, cancelling the row's px-2 padding for
          just that cell) makes its RENDERED width 48px, not 40. Offsetting
          this cell by only 40px made it stick 8px too far left, overlapping
          the silk cell and, more importantly, covering the first ~8-20px of
          whatever column comes right after it once scrolled all the way -
          found via measuring actual rendered positions, not a hunch. */}
      <span className={`sticky left-12 z-10 min-w-0 sm:static sm:z-auto ${stickyBg}`}>
        <span className="flex items-center gap-1">
          <span className={`truncate font-medium text-ink ${scratched ? 'line-through' : ''}`}>
            <span className="font-mono text-ink-mute sm:hidden">{runner.tabNumber}. </span>
            {runner.horse}
          </span>
          {/* Compact mode has no jockey/trainer subtitle line for RTS to
              ride along with (see below) - it rides the name line instead,
              mobile-only, so it's still visible in every density like
              before, just not as its own scrollable column any more. */}
          {compact && (
            <span className={`flex-none font-mono text-[11px] sm:hidden ${rtsColorClass}`} title={rtsTitle}>
              {spell.label}
            </span>
          )}
          {runner.dataScratched && (
            // A real, data-confirmed scratch (see toprate_price_refresh.py) -
            // not a toggle, just a fact. The manual what-if toggle used to
            // live here too (a button, easy to fat-finger while just trying
            // to open the row) - it's in the runner detail modal now, a
            // deliberate tap rather than an inline hazard next to the name.
            <span
              title="Scratched (confirmed by TopRate)"
              className="flex-none rounded bg-rose px-1 text-[10px] font-semibold text-white"
            >
              SCR
            </span>
          )}
          {trackerQualifier && !scratched && (trackerQualifier.qualifiesA || trackerQualifier.qualifiesB) && (
            // Live flag, not read from the Trackers tab's CSV log - see
            // lib/trackerRules.ts for why it's computed fresh here instead
            // (real user feedback, 2026-09-16: the log can lag an upcoming
            // race by hours).
            <span
              title={trackerFireTitle(trackerQualifier)}
              className={`flex-none rounded px-1 text-[10px] font-semibold text-white ${
                trackerQualifier.qualifiesB ? 'bg-emerald' : 'bg-indigo'
              }`}
            >
              {trackerQualifier.qualifiesB ? 'B' : 'A'}
            </span>
          )}
          {trackerQualifier &&
            !scratched &&
            !trackerQualifier.qualifiesA &&
            !trackerQualifier.qualifiesB &&
            (trackerQualifier.contestedA ||
              trackerQualifier.contestedB ||
              trackerQualifier.underPriceA ||
              trackerQualifier.underPriceB) && (
              <span
                title={trackerSkippedTitle(trackerQualifier)}
                className={`flex-none rounded border px-1 text-[10px] font-semibold ${
                  trackerQualifier.contestedB || trackerQualifier.underPriceB
                    ? 'border-emerald text-emerald'
                    : 'border-indigo text-indigo'
                }`}
              >
                {trackerQualifier.contestedB || trackerQualifier.underPriceB ? 'B' : 'A'}
              </span>
            )}
        </span>
        {!compact && (
          <span className="block truncate text-xs text-ink-faint">
            {/* Mobile-only RTS prefix (desktop already has its own column,
                see below - this would double it up there). "Put with
                jockey/trainer to save width" - user request, Sep 2026. */}
            <span className="sm:hidden">
              <span className={`font-mono ${rtsColorClass}`} title={rtsTitle}>
                {spell.label}
              </span>
              {' · '}
            </span>
            {runner.jockey}
            {ratingSuffix(runner.jockeyRating)} / {runner.trainer}
            {ratingSuffix(runner.trainerRating)}
          </span>
        )}
      </span>
      <span className={`hidden text-right font-mono sm:inline ${rtsColorClass}`} title={rtsTitle}>
        {spell.label}
      </span>
      <span className="hidden text-right font-mono text-ink-mute sm:inline">
        {fmtWpr(runner.baseWpr)}
      </span>
      <span
        className={`hidden text-right font-mono sm:inline ${
          runner.wprAdjustment != null && runner.wprAdjustment > 0
            ? 'text-emerald-deep'
            : runner.wprAdjustment != null && runner.wprAdjustment < 0
              ? 'text-rose'
              : 'text-ink-mute'
        }`}
      >
        {fmtAdj(runner.wprAdjustment)}
      </span>
      {/* Combo now leads (2026-09-19, real user request: "combo should be
          the bold number, not proj... have combo to the left of proj") -
          it's the headline figure now, Proj demoted to the plain/muted
          style below it (TopRate's own style). No confidence sub-line or
          override asterisk here - those are specifically about the raw
          WPR projection's own model confidence/override, not the blend,
          so they stay attached to the Proj cell they've always described. */}
      <span className="text-right font-mono font-semibold text-emerald-deep">
        {scratched ? 'SCR' : fmtWpr(displayComposite)}
      </span>
      <span className="text-right font-mono text-ink-mute">
        {/* sm:contents on mobile-only stack: confidence sits under the WPR
            figure (not inline after it) to keep this column narrow on
            small screens - at sm+ the wrapper disappears (display:contents)
            so the two lines rejoin the parent's inline flow exactly as
            before, unstacked. */}
        <span className="flex flex-col items-end gap-0.5 sm:contents">
          <span>
            {/* Whole number (2026-09-19, real user request: "change proj
                to be a whole number") - Combo above keeps its own decimal
                (fmtWpr), this is Proj-specific. */}
            {scratched ? <span className="text-ink-faint">SCR</span> : fmtInt(displayProj)}
            {overridden && (
              <span className="ml-0.5 text-amber" title="Manually adjusted">
                *
              </span>
            )}
          </span>
          {runner.projectionConfidence !== null && !compact && (
            <span className="text-[10px] font-normal leading-none text-ink-faint sm:ml-1 sm:text-xs">
              {fmtInt(runner.projectionConfidence)}%
            </span>
          )}
        </span>
      </span>
      <span className="hidden text-right font-mono text-ink-mute sm:inline">
        {scratched ? 'SCR' : fmtInt(runner.toprateRating)}
      </span>
      <span className={`text-right font-mono text-ink-mute ${compact ? 'hidden sm:inline' : ''}`}>
        {scratched ? 'SCR' : fmtInt(runner.formFactor)}
      </span>
      <span className={`text-right font-mono text-ink-mute ${compact ? 'hidden sm:inline' : ''}`}>
        {scratched ? 'SCR' : fmtJockeyWin(runner.jockeyWinPct90d)}
      </span>
      {/* Speed Map ADJ_TERM, demeaned against this race (2026-09-19, real
          user request: "add a column for speed map adj, with green and red
          colour") - the exact same number SpeedMapGrid's own tile tint is
          built from (see raceModel.ts's speedMapDemeanedByRunId), not the
          raw wpjcb value: two of speed_map's own inputs are shared across
          the whole field by construction, so the raw number alone can't
          tell "favoured vs this field" from "a generally easy speed_map
          day" the way the demeaned value does. Shown on Full mobile too
          (2026-09-19, direct follow-up: "not seeing it" on mobile) - same
          `compact ? 'hidden sm:inline' : ''` trick Form/Jockey Win% already
          use to appear on Full mobile + desktop but not Compact.
          Positioned between Jky Win%/J% and Fixed $ (moved here 2026-09-19,
          direct follow-up: "sm should be between j% and fixed", was
          originally between Adj and Combo). Green/red at +-0.5, not a bare
          sign check (2026-09-19, same follow-up: "green and red colours
          should be +/- 0.5") - matches SpeedMapGrid's own tile tint
          threshold exactly (SPEED_MAP_TINT_THRESHOLD, shared from
          raceModel.ts) rather than the plain Adj column's sign-only
          convention, so a near-zero value here reads as neutral the same
          way its tile does, instead of the two disagreeing on borderline
          cases. */}
      <span
        className={`text-right font-mono ${compact ? 'hidden sm:inline' : ''} ${
          effective?.speedMapAdj != null && effective.speedMapAdj >= SPEED_MAP_TINT_THRESHOLD
            ? 'text-emerald-deep'
            : effective?.speedMapAdj != null && effective.speedMapAdj <= -SPEED_MAP_TINT_THRESHOLD
              ? 'text-rose'
              : 'text-ink-mute'
        }`}
      >
        {fmtAdj(effective?.speedMapAdj ?? null)}
      </span>
      {/* FP's own content (a 20px circle badge) never needed more than its
          20px track. This column - and the sticky silk/name cells to the
          left of it - is why scrolling to reveal it used to be actively
          harmful, not just tight: once the row was wider than its
          container (see the grid-cols comment above), scrolling far enough
          to reach FP also scrolled Proj back UNDER the sticky cells instead
          of just revealing FP (verified by measuring real rendered
          positions - originally found against the old WPR $ column this
          replaced). Shrinking the row to fit without scrolling at all
          (see above) sidesteps that entirely rather than fighting it. */}
      <span className="flex items-center justify-end font-mono text-ink-mute">
        <span>{scratched ? 'SCR' : fmtPrice(runner.fixedWinPrice)}</span>
        {/* Fixed-width slot, always rendered (just invisible when there's no
            move) - an inline-appended arrow used to change how much content
            sat inside this right-aligned cell, so the price digits landed in
            a different horizontal spot on rows with a move vs rows without,
            and nothing in the column actually lined up. Reserving the same
            width every row regardless of content keeps the price flush
            right consistently. */}
        <span
          className={`ml-1 w-2.5 flex-none text-center text-[10px] leading-none ${
            !scratched && showMove
              ? priceMove.direction === 'firmed'
                ? 'text-emerald-deep'
                : 'text-rose'
              : 'invisible'
          }`}
          title={
            !scratched && showMove
              ? `Opened ${fmtPrice(runner.openFixedPrice)} - ${priceMove.direction} ${priceMove.pctChange.toFixed(0)}%`
              : undefined
          }
        >
          {!scratched && showMove ? (priceMove.direction === 'firmed' ? '▼' : '▲') : '▲'}
        </span>
      </span>
      <span className="text-right">
        {/* Same h-5 w-5 inline-flex box for every position, winner or not -
            the winner's circle badge used to be the only entry with a fixed-
            width box, so its centred glyph sat visibly left of the other
            positions' plain right-aligned text. One shared box keeps every
            row's number in a straight column. */}
        <span
          className={`inline-flex h-5 w-5 items-center justify-center rounded-full font-mono text-ink-mute ${
            runner.finishPosition === 1 ? 'border border-amber-line bg-amber-bg font-semibold text-amber' : ''
          }`}
        >
          {runner.finishPosition !== null ? fmtInt(runner.finishPosition) : ''}
        </span>
      </span>
    </div>
  )
}
