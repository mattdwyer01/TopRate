import type { Runner } from '../../types/domain'
import { fmtPrice } from '../../lib/format'
import type { PriceMove } from '../../lib/priceMove'

function fmt(v: number | null): string {
  return v == null ? '—' : v.toFixed(1)
}

function ordinal(n: number): string {
  const v = n % 100
  if (v >= 11 && v <= 13) return `${n}th`
  switch (n % 10) {
    case 1:
      return `${n}st`
    case 2:
      return `${n}nd`
    case 3:
      return `${n}rd`
    default:
      return `${n}th`
  }
}

interface ResultVsProjectionProps {
  runner: Runner
  priceBitsBefore: string[]
  priceBitsAfter: string[]
  fixedMove: PriceMove | null
}

// Shown beside CareerStats once a runner has actually raced - takes over
// that slot from ComparisonGrid, since "does today's shape suit it" (a
// pre-race question) stops being the interesting one once today already
// happened and "how far off was the projection, and what actually
// happened" is. Two side-by-side stat blocks rather than a dense table -
// reads as a real "predicted vs actual" comparison at a glance, and fills
// the width naturally instead of stretching a table with lots of columns.
// Also carries the Price line (moved here from the modal footer for a
// resulted runner) - "what the market actually paid" pairs naturally with
// "what actually happened", and fills out the card's height too.
export function ResultVsProjection({ runner, priceBitsBefore, priceBitsAfter, fixedMove }: ResultVsProjectionProps) {
  if (runner.actualWpr == null) return null

  const miss = runner.projectedWpr != null ? runner.actualWpr - runner.projectedWpr : null
  const missAbs = miss != null ? Math.abs(miss) : null
  const missClass =
    missAbs == null ? 'text-ink-mute' : missAbs >= 8 ? 'text-rose' : missAbs >= 4 ? 'text-amber' : 'text-emerald-deep'

  let rankText: string | null = null
  if (runner.wprRank != null && runner.actualWprRank != null) {
    const rd = runner.actualWprRank - runner.wprRank
    rankText = rd === 0 ? 'exact' : rd > 0 ? `${rd} lower` : `${-rd} higher`
  }

  return (
    <div className="rounded-lg border border-line bg-panel p-2.5">
      <div className="mb-1.5 text-xs font-semibold text-ink">Result vs projection</div>
      <div className="grid grid-cols-2 gap-3">
        <div>
          <div className="text-[11px] text-ink-faint">Predicted</div>
          <div className="font-mono text-lg font-semibold text-ink">{fmt(runner.projectedWpr)}</div>
          <div className="text-xs text-ink-mute">rank {runner.wprRank ?? '—'}</div>
        </div>
        <div>
          <div className="text-[11px] text-ink-faint">Actual</div>
          <div className="font-mono text-lg font-semibold text-ink">{fmt(runner.actualWpr)}</div>
          <div className="text-xs text-ink-mute">
            rank {runner.actualWprRank ?? '—'}
            {runner.finishPosition != null && (
              <>
                {' '}
                &middot; {runner.won ? 'won' : ordinal(runner.finishPosition)}
                {runner.marginFinish != null && !runner.won && ` (${runner.marginFinish.toFixed(1)}L)`}
              </>
            )}
          </div>
        </div>
      </div>
      {(miss != null || rankText) && (
        <div className="mt-2 border-t border-line-soft pt-1.5 text-xs text-ink-mute">
          {miss != null && (
            <>
              Missed by{' '}
              <span className={`font-mono font-medium ${missClass}`}>
                {miss > 0 ? '+' : ''}
                {miss.toFixed(1)}
              </span>
            </>
          )}
          {rankText && <>{miss != null ? ' · ' : ''}rank {rankText}</>}
        </div>
      )}
      <div className="mt-2 border-t border-line-soft pt-1.5 text-xs text-ink-mute">
        <span className="mr-1 font-medium text-ink">Price</span>
        {priceBitsBefore.length > 0 && `${priceBitsBefore.join(' · ')} · `}
        {runner.fixedWinPrice != null && (
          <>
            Fixed {fmtPrice(runner.fixedWinPrice)}
            {fixedMove && (
              <span className={fixedMove.direction === 'firmed' ? 'text-emerald-deep' : 'text-rose'}>
                {' '}
                ({fixedMove.direction} {fixedMove.pctChange.toFixed(0)}% from {fmtPrice(runner.openFixedPrice)} at open)
              </span>
            )}
            {' · '}
          </>
        )}
        {priceBitsAfter.join(' · ')}
      </div>
    </div>
  )
}
