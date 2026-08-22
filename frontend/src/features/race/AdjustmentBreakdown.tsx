import { ADJUSTMENT_LABELS, BASELINE_KEY } from '../../lib/adjustmentLabels'

interface AdjustmentBreakdownProps {
  breakdown: Record<string, number>
  adjustment: number
}

const MIN_SHOWN = 0.05

function fmtSigned(v: number): string {
  return `${v > 0 ? '+' : ''}${v.toFixed(2)}`
}

// What's actually driving this runner's adjustment, feature by feature -
// not just the two biggest reasons describe() narrates (it only speaks up
// when the total is >=3 WPR), the full picture, including small nudges.
// Values sum to `adjustment` exactly. Wrapping pills rather than one row
// per feature - a compact strip instead of a tall list, since there can be
// up to 15 of these.
export function AdjustmentBreakdown({ breakdown, adjustment }: AdjustmentBreakdownProps) {
  const baseline = breakdown[BASELINE_KEY] ?? 0
  const rows = Object.entries(breakdown)
    .filter(([key, v]) => key !== BASELINE_KEY && Math.abs(v) >= MIN_SHOWN)
    .sort((a, b) => Math.abs(b[1]) - Math.abs(a[1]))

  if (rows.length === 0) {
    return (
      <div className="text-sm text-ink-mute">
        Nothing in this horse's situation moved the rating - the adjustment is essentially the model's baseline
        calibration ({fmtSigned(baseline)}).
      </div>
    )
  }

  return (
    <div>
      <div className="mb-1 flex items-baseline justify-between">
        <span className="text-sm font-semibold text-ink">What's driving the adjustment</span>
        <span className="text-xs text-ink-faint">
          plus baseline &amp; calibration {fmtSigned(baseline)} = total{' '}
          <span className={adjustment > 0 ? 'text-emerald-deep' : adjustment < 0 ? 'text-rose' : 'text-ink-mute'}>
            {fmtSigned(adjustment)}
          </span>
        </span>
      </div>
      <div className="flex flex-wrap gap-1.5">
        {rows.map(([key, v]) => (
          <span
            key={key}
            className={`inline-flex items-center gap-1 rounded-full border px-2 py-0.5 text-xs ${
              v > 0 ? 'border-emerald-line bg-emerald-bg text-emerald-deep' : 'border-rose-line bg-rose-bg text-rose'
            }`}
          >
            {ADJUSTMENT_LABELS[key] ?? key}
            <span className="font-mono font-semibold">{fmtSigned(v)}</span>
          </span>
        ))}
      </div>
    </div>
  )
}
