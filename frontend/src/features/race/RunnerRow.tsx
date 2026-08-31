import type { Runner } from '../../types/domain'
import type { EffectiveRunner } from '../../lib/raceModel'
import { fmtInt, fmtPrice } from '../../lib/format'
import { computePriceMove, MOVE_DISPLAY_THRESHOLD_PCT } from '../../lib/priceMove'
import { spellPosition } from '../../lib/spellPosition'

interface RunnerRowProps {
  runner: Runner
  raceDate: string
  compact: boolean
  selected: boolean
  effective?: EffectiveRunner
  onClick: () => void
  onToggleScratch: () => void
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
//
// Aug 2026 redesign: the WPR-points breakdown (Peak/Base/Adj/Proj) and the
// post-race Actual WPR column were dropped from this row - the blend score
// (Model $) is the primary ranking now (see RaceDetail.tsx's COLUMN_LABELS
// comment), and WPR points on their own no longer earn a column here. The
// WPR breakdown and the manual override controls both still exist, moved
// into RunnerDetailModal's "WPR rating detail" section.
export function RunnerRow({
  runner,
  raceDate,
  compact,
  selected,
  effective,
  onClick,
  onToggleScratch,
}: RunnerRowProps) {
  const rowPadding = compact ? 'py-1.5' : 'py-2.5'
  const scratched = effective?.scratched ?? false
  const spell = spellPosition(runner.formHistory, raceDate)
  // Scratched: no live price any more, regardless of the model's raw
  // (pre-scratch) blendPrice - matches the SCR text this cell renders below.
  const displayPrice = scratched ? null : runner.blendPrice
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
      className={`grid w-full cursor-pointer grid-cols-[40px_1fr_44px_64px_60px_44px] items-center gap-x-2 gap-y-0.5 border-b border-line-soft px-2 text-left text-sm transition-colors sm:grid-cols-[44px_36px_1fr_56px_64px_60px_48px] ${rowPadding} ${
        scratched ? 'opacity-50' : selected ? 'bg-emerald-bg' : 'hover:bg-bg'
      }`}
    >
      {runner.silkUrl ? (
        <img src={runner.silkUrl} alt="" className="h-9 w-9 rounded-sm object-contain" />
      ) : (
        <span />
      )}
      <span className="hidden font-mono text-ink-mute sm:inline">{runner.tabNumber}</span>
      <span className="min-w-0">
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
          {runner.dataScratched ? (
            // A real, data-confirmed scratch (see toprate_price_refresh.py) -
            // not a toggle, since there's nothing to un-scratch here (the
            // effective state can't be undone by clicking - see RaceDetail's
            // effectiveScratched). Solid fill (same treatment as the "about
            // to jump" ticker state) so it reads as a fact, distinct from
            // the quiet manual what-if toggle below.
            <span
              title="Scratched (confirmed by TopRate)"
              className="flex-none rounded bg-rose px-1 text-[10px] font-semibold text-white"
            >
              SCR
            </span>
          ) : (
            <button
              type="button"
              onClick={(e) => {
                e.stopPropagation()
                onToggleScratch()
              }}
              title={scratched ? 'Un-scratch this runner' : 'Mark this runner as scratched'}
              // Always visible, not hover-only - on a phone (exactly where a
              // late scratch is likely to be entered, at the track with no
              // hover state at all) a hover-revealed button is invisible and
              // undiscoverable. Quiet (faint border, muted text) until
              // scratched, so it doesn't compete with the horse name at rest.
              className={`flex-none rounded border px-1 text-[10px] font-semibold transition-colors ${
                scratched
                  ? 'border-rose-line bg-rose-bg text-rose'
                  : 'border-line-soft text-ink-faint hover:border-line hover:text-ink-mute'
              }`}
            >
              SCR
            </button>
          )}
          {/* Edge score: only surfaces once it clears the margin a single
              70/30 holdout showed ROI at (see calibrate_edge_score.py) - but
              a proper walk-forward check (30 daily refits, Aug 2026) came
              back statistically indistinguishable from break-even (95% CI
              on ROI roughly -19% to +22%). Experimental, not a proven edge -
              see the runner detail panel. Still a bet-selection flag only,
              not shown for every priced runner. */}
          {!scratched && runner.edgeScore != null && runner.edgeScore >= 0.08 && (
            <span
              title={`Model ${(runner.edgeModelProb! * 100).toFixed(0)}% vs market ${(runner.edgeMarketProb! * 100).toFixed(0)}% implied win chance - experimental signal, not proven profitable (see runner detail)`}
              className="flex-none rounded bg-emerald px-1 text-[10px] font-semibold text-white"
            >
              +{(runner.edgeScore * 100).toFixed(0)}% EDGE
            </span>
          )}
          {/* Manual WPR override no longer changes Model $ (it blends other
              signals too) - a quiet marker so the row doesn't look silently
              wrong to someone who set one, full explanation lives in the
              modal's WPR rating detail section. */}
          {overridden && (
            <span
              title="You've set a manual WPR override for this runner - see its detail for why Model $ doesn't move with it"
              className="flex-none text-amber"
            >
              ✎
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
      <span
        className={`text-right font-mono ${
          spell.label === 'FU' ? 'font-semibold text-amber' : 'text-ink-mute'
        }`}
        title={spell.daysSince != null ? `${spell.daysSince} days since last run` : undefined}
      >
        {spell.label}
      </span>
      <span className="text-right font-mono font-semibold text-emerald-deep">
        {scratched ? <span className="text-ink-faint">SCR</span> : fmtPrice(displayPrice)}
      </span>
      <span className="text-right font-mono text-ink-mute">
        {scratched ? 'SCR' : fmtPrice(runner.fixedWinPrice)}
        {!scratched && showMove && (
          <span
            className={priceMove.direction === 'firmed' ? 'text-emerald-deep' : 'text-rose'}
            title={`Opened ${fmtPrice(runner.openFixedPrice)} - ${priceMove.direction} ${priceMove.pctChange.toFixed(0)}%`}
          >
            {priceMove.direction === 'firmed' ? ' ▼' : ' ▲'}
          </span>
        )}
      </span>
      <span className="text-right">
        {runner.finishPosition === 1 ? (
          <span className="inline-flex h-5 w-5 items-center justify-center rounded-full border border-amber-line bg-amber-bg font-mono font-semibold text-amber">
            1
          </span>
        ) : (
          <span className="font-mono text-ink-mute">
            {runner.finishPosition !== null ? fmtInt(runner.finishPosition) : ''}
          </span>
        )}
      </span>
    </div>
  )
}
