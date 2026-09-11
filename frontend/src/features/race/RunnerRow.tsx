import type { Runner } from '../../types/domain'
import type { EffectiveRunner } from '../../lib/raceModel'
import { fmtInt, fmtPrice, fmtWpr } from '../../lib/format'
import { computePriceMove, MOVE_DISPLAY_THRESHOLD_PCT } from '../../lib/priceMove'
import { spellPosition } from '../../lib/spellPosition'

interface RunnerRowProps {
  runner: Runner
  raceDate: string
  compact: boolean
  selected: boolean
  effective?: EffectiveRunner
  onClick: () => void
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
// consolidation the rebuild plan calls for). The grid's column template
// itself changes at the sm breakpoint via Tailwind classes, so the same
// DOM/children just reflow rather than existing twice.
export function RunnerRow({
  runner,
  raceDate,
  compact,
  selected,
  effective,
  onClick,
}: RunnerRowProps) {
  const rowPadding = compact ? 'py-1.5' : 'py-2.5'
  const scratched = effective?.scratched ?? false
  const spell = spellPosition(runner.formHistory, raceDate)
  // Scratched: force both to null rather than falling back to the model's
  // raw (pre-scratch) projectedWpr/wprPrice - a scratched runner has no
  // live rating any more, it shouldn't look like it's still rated just
  // because effective.effectiveProjectedWpr is explicitly null (which ??
  // would otherwise treat the same as "no override, use the raw value").
  const displayProj = scratched ? null : (effective?.effectiveProjectedWpr ?? runner.projectedWpr)
  const displayPrice = scratched ? null : (effective?.effectivePrice ?? runner.wprPrice)
  const overridden = effective?.hasOverride ?? false
  const priceMove = computePriceMove(runner.openFixedPrice, runner.fixedWinPrice)
  const showMove = priceMove != null && priceMove.pctChange >= MOVE_DISPLAY_THRESHOLD_PCT

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
      // Mobile: a plain flex column of two stacked lines (name, then stats) -
      // a flat 6-column grid never had room for a variable-length horse name
      // once the four price/rating columns each claim their own fixed width,
      // measured in practice down to an unreadable ~18px. Desktop keeps the
      // original single-row grid; sm:contents on the two wrapper divs below
      // dissolves them back into plain grid-item siblings at that breakpoint,
      // so the desktop column order/behaviour is unchanged.
      className={`flex w-full cursor-pointer flex-col gap-y-1 border-b border-line-soft px-2 text-left text-sm transition-colors sm:grid sm:grid-cols-[44px_36px_1fr_56px_56px_56px_56px_60px_68px_70px_48px_52px] sm:items-center sm:gap-x-2 sm:gap-y-0.5 ${rowPadding} ${
        scratched ? 'opacity-50' : selected ? 'bg-emerald-bg' : 'hover:bg-bg'
      }`}
    >
      <div className="flex items-center gap-2 sm:contents">
        {runner.silkUrl ? (
          <img src={runner.silkUrl} alt="" className="h-9 w-9 flex-none rounded-sm object-contain" />
        ) : (
          <span className="w-9 flex-none sm:w-auto" />
        )}
        <span className="hidden font-mono text-ink-mute sm:inline">{runner.tabNumber}</span>
        <span className="min-w-0 flex-1 sm:flex-initial">
          <span className="flex items-center gap-1">
            <span className={`truncate font-medium text-ink ${scratched ? 'line-through' : ''}`}>
              <span className="font-mono text-ink-mute sm:hidden">{runner.tabNumber}. </span>
              {runner.horse}
            </span>
            {/* FP is desktop-only (see the dedicated column below) - mobile
                hides that column for space, so the win needs its own inline
                marker or a mobile reader can no longer tell who won at all.
                Outside the truncating span above so a long name can never
                clip it away. */}
            {runner.finishPosition === 1 && (
              <span className="inline-flex h-4 w-4 flex-none items-center justify-center rounded-full border border-amber-line bg-amber-bg font-mono text-[10px] font-semibold text-amber sm:hidden">
                1
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
          </span>
          {!compact && (
            <span className="block truncate text-xs text-ink-faint">
              {runner.jockey}
              {ratingSuffix(runner.jockeyRating)} / {runner.trainer}
              {ratingSuffix(runner.trainerRating)}
            </span>
          )}
        </span>
      </div>
      {/* Mobile-only second line: RTS/Proj/WPR $/Fixed $ - the stats that
          used to share the cramped single-row grid with the name. No column
          header lines up with these on mobile any more (see RaceDetail's
          mobile header, now a plain sort-button bar), so each value gets its
          own short inline label here; sm:hidden drops the labels once the
          real grid header takes over at sm+. */}
      <div className="flex items-center gap-3 pl-11 text-xs sm:contents sm:pl-0 sm:text-sm">
        <span
          className={`font-mono ${
            spell.label === 'FU'
              ? 'font-semibold text-amber'
              : spell.label === 'FS'
                ? 'font-semibold text-indigo'
                : 'text-ink-mute'
          }`}
          title={
            spell.label === 'FS'
              ? 'First starter - no prior race starts'
              : spell.daysSince != null
                ? `${spell.daysSince} days since last run`
                : undefined
          }
        >
          <span className="text-ink-faint sm:hidden">RTS </span>
          {spell.label}
        </span>
        <span className="hidden text-right font-mono text-ink-mute sm:inline">
          {fmtWpr(runner.peakWpr)}
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
        <span className="font-mono font-semibold text-emerald-deep sm:text-right">
          {/* sm:contents on mobile-only stack: confidence sits under the WPR
              figure (not inline after it) to keep this column narrow on
              small screens - at sm+ the wrapper disappears (display:contents)
              so the two lines rejoin the parent's inline flow exactly as
              before, unstacked. */}
          <span className="flex items-center gap-1 sm:contents">
            <span className="text-ink-faint sm:hidden">Proj </span>
            <span>
              {scratched ? <span className="text-ink-faint">SCR</span> : fmtWpr(displayProj)}
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
        <span className="font-mono text-ink-mute sm:text-right">
          <span className="text-ink-faint sm:hidden">WPR </span>
          {scratched ? 'SCR' : fmtPrice(displayPrice)}
        </span>
        <span className="flex items-center font-mono text-ink-mute sm:justify-end">
          {/* mr-1 (not a trailing space in the string): this label is its
              own flex item, sitting next to the price as a sibling box, not
              inline text before it - a trailing space inside the string
              collapses at that box edge and produced "Fixed$4.20" with no
              gap at all. */}
          <span className="mr-1 text-ink-faint sm:hidden sm:mr-0">Fixed</span>
          <span>{scratched ? 'SCR' : fmtPrice(runner.fixedWinPrice)}</span>
          {/* Fixed-width slot, always rendered (just invisible when there's no
              move) - an inline-appended arrow used to change how much content
              sat inside this right-aligned cell, so the price digits landed in
              a different horizontal spot on rows with a move vs rows without,
              and nothing in the column actually lined up. Reserving the same
              width every row regardless of content keeps the price flush
              right consistently. */}
          <span
            className={`ml-0.5 w-2.5 flex-none text-center text-[10px] leading-none ${
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
      </div>
      <span className="hidden text-right sm:inline">
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
      <span className="hidden text-right font-mono text-ink-mute sm:inline">
        {runner.actualWpr != null ? fmtWpr(runner.actualWpr) : ''}
      </span>
    </div>
  )
}
