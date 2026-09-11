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
// consolidation the rebuild plan calls for). Both breakpoints are a real
// CSS grid with columns - the same shape RaceDetail's header row uses -
// they just use a different grid-template. Below sm, Base/Adj/Proj/WPR $/
// Fixed $/FP are all still real columns (not hidden or stacked onto a
// second line) - Peak/Actual stay desktop-only, and RTS isn't a column at
// all on mobile (not worth a sortable column of its own - it rides along
// with the name/jockey-trainer text instead, see rtsColorClass/rtsTitle
// below). That's still more columns than a phone's width can show without
// squeezing the name unreadable (measured previously: ~18px), so the row
// is wider than the viewport on purpose and the shared overflow-x-auto
// wrapper in RaceDetail scrolls it horizontally - silk+name are `sticky
// left-0`/`left-10` so they stay in view (frozen) while the stat columns
// scroll underneath, same "frozen first column" pattern MeetingsGrid
// already uses for its own wide table.
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

  // RTS isn't worth its own sortable mobile column (it's not something
  // anyone sorts by day-to-day, unlike Proj/WPR $) - on mobile it rides
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
  // visibly split into "green here, not green under the frozen name" as
  // soon as you scroll it sideways. `group` + group-hover carries the
  // row's :hover state down to them (JS can't see :hover); scratched/
  // selected are already computed here, so those branch directly.
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
      className={`group grid w-max cursor-pointer grid-cols-[40px_150px_52px_52px_58px_64px_68px_44px] items-center gap-x-2 gap-y-0.5 border-b border-line-soft px-2 text-left text-sm transition-colors sm:w-full sm:grid-cols-[44px_36px_1fr_56px_56px_56px_56px_60px_68px_70px_48px_52px] ${rowPadding} ${
        scratched ? 'opacity-50' : selected ? 'bg-emerald-bg' : 'hover:bg-bg'
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
      <span className={`sticky left-10 z-10 min-w-0 sm:static sm:z-auto ${stickyBg}`}>
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
        {fmtWpr(runner.peakWpr)}
      </span>
      <span className="text-right font-mono text-ink-mute">
        {fmtWpr(runner.baseWpr)}
      </span>
      <span
        className={`text-right font-mono ${
          runner.wprAdjustment != null && runner.wprAdjustment > 0
            ? 'text-emerald-deep'
            : runner.wprAdjustment != null && runner.wprAdjustment < 0
              ? 'text-rose'
              : 'text-ink-mute'
        }`}
      >
        {fmtAdj(runner.wprAdjustment)}
      </span>
      <span className="text-right font-mono font-semibold text-emerald-deep">
        {/* sm:contents on mobile-only stack: confidence sits under the WPR
            figure (not inline after it) to keep this column narrow on
            small screens - at sm+ the wrapper disappears (display:contents)
            so the two lines rejoin the parent's inline flow exactly as
            before, unstacked. */}
        <span className="flex flex-col items-end gap-0.5 sm:contents">
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
      <span className="text-right font-mono text-ink-mute">
        {scratched ? 'SCR' : fmtPrice(displayPrice)}
      </span>
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
      <span className="hidden text-right font-mono text-ink-mute sm:inline">
        {runner.actualWpr != null ? fmtWpr(runner.actualWpr) : ''}
      </span>
    </div>
  )
}
