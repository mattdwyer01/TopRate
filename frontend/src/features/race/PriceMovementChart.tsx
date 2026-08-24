import type { Runner } from '../../types/domain'
import { fmtPrice } from '../../lib/format'
import { computePriceMove, type PriceMove } from '../../lib/priceMove'

interface PriceMovementChartProps {
  runner: Runner
  priceBitsBefore: string[]
  priceBitsAfter: string[]
  fixedMove: PriceMove | null
}

function fmtMinutes(m: number): string {
  if (m <= 0) return 'Open'
  if (m < 60) return `+${Math.round(m)}m`
  const h = Math.floor(m / 60)
  const rem = Math.round(m % 60)
  return rem === 0 ? `+${h}h` : `+${h}h ${rem}m`
}

const CHART_W = 260
const CHART_H = 60
const PAD = 5

// The single "Price" card for a runner - the Fixed price's intraday
// snapshot history as a real line chart (dot per snapshot, y-axis
// auto-scaled to this runner's own price range) rather than a table of
// rows, so a glance shows the SHAPE of the move, not a column of numbers
// to read. Sits beside CareerStats (see RunnerDetailModal). Folds in the
// WPR $/TR $/SP bits that used to live in their own text line at the very
// bottom of the modal (and inside ResultVsProjection for a resulted
// runner) - this card is now the one place all of a runner's price
// information lives, not just the Fixed price trend. Falls back to plain
// "Fixed $X" text when there aren't 2+ snapshots yet to chart (a very
// recent capture, or a payload from before price history was committed).
export function PriceMovementChart({ runner, priceBitsBefore, priceBitsAfter, fixedMove }: PriceMovementChartProps) {
  const pts = runner.priceSeries
  const hasChart = pts.length >= 2
  const bits = [...priceBitsBefore, ...priceBitsAfter].join('  ·  ')

  return (
    <div className="rounded-lg border border-line bg-panel p-2.5">
      <div className="mb-1.5 text-xs font-semibold text-ink">Price</div>

      {hasChart ? (
        <PriceChart pts={pts} />
      ) : (
        runner.fixedWinPrice != null && (
          <div className="text-xs text-ink-mute">
            Fixed {fmtPrice(runner.fixedWinPrice)}
            {fixedMove && (
              <span className={fixedMove.direction === 'firmed' ? 'text-emerald-deep' : 'text-rose'}>
                {' '}
                ({fixedMove.direction} {fixedMove.pctChange.toFixed(0)}% from {fmtPrice(runner.openFixedPrice)} at
                open)
              </span>
            )}
          </div>
        )
      )}

      {bits && (
        <div className={`text-xs text-ink-faint ${hasChart ? 'mt-2 border-t border-line-soft pt-1.5' : 'mt-1'}`}>
          {bits}
        </div>
      )}
    </div>
  )
}

function PriceChart({ pts }: { pts: Runner['priceSeries'] }) {
  const prices = pts.map((p) => p.price)
  const min = Math.min(...prices)
  const max = Math.max(...prices)
  const range = max - min || 1

  const points = pts.map((p, i) => {
    const x = (i / (pts.length - 1)) * (CHART_W - PAD * 2) + PAD
    const y = CHART_H - PAD - ((p.price - min) / range) * (CHART_H - PAD * 2)
    return { x, y }
  })
  const linePoints = points.map((p) => `${p.x.toFixed(1)},${p.y.toFixed(1)}`).join(' ')

  const open = pts[0].price
  const current = pts[pts.length - 1].price
  const move = computePriceMove(open, current)
  const good = current < open
  const colorClass = move == null ? 'text-ink-faint' : good ? 'text-emerald-deep' : 'text-rose'

  return (
    <div>
      <div className="flex items-baseline justify-between text-xs">
        <span className="text-ink-mute">
          Open <span className="font-mono font-semibold text-ink">{fmtPrice(open)}</span>
        </span>
        {move && (
          <span className={`font-mono font-semibold ${colorClass}`}>
            {good ? '-' : '+'}
            {move.pctChange.toFixed(0)}%
          </span>
        )}
      </div>
      <div className="text-xs text-ink-mute">
        Now{' '}
        <span className={`font-mono font-semibold ${move == null ? 'text-ink' : colorClass}`}>
          {fmtPrice(current)}
        </span>
        {move && <span className={colorClass}> ({move.direction})</span>}
      </div>
      <svg
        width="100%"
        height={CHART_H}
        viewBox={`0 0 ${CHART_W} ${CHART_H}`}
        preserveAspectRatio="none"
        className={`mt-1 ${colorClass}`}
      >
        <polyline
          points={linePoints}
          fill="none"
          stroke="currentColor"
          strokeWidth="1.75"
          strokeLinecap="round"
          strokeLinejoin="round"
        />
        {points.map((p, i) => (
          <circle key={i} cx={p.x} cy={p.y} r={i === points.length - 1 ? 2.5 : 1.5} fill="currentColor" />
        ))}
      </svg>
      <div className="mt-0.5 flex justify-between text-[11px] text-ink-faint">
        <span>Open</span>
        <span>{fmtMinutes(pts[pts.length - 1].minutesSinceOpen)}</span>
      </div>
    </div>
  )
}
