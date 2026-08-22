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
// Values sum to `adjustment` exactly, shown at the bottom for transparency.
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
      <div className="mb-1 text-sm font-semibold text-ink">What's driving the adjustment</div>
      <div className="flex flex-col divide-y divide-line-soft rounded-lg border border-line">
        {rows.map(([key, v]) => (
          <div key={key} className="flex items-center justify-between gap-3 px-2.5 py-1.5 text-sm">
            <span className="text-ink-soft">{ADJUSTMENT_LABELS[key] ?? key}</span>
            <span className={`font-mono font-medium ${v > 0 ? 'text-emerald-deep' : 'text-rose'}`}>
              {fmtSigned(v)}
            </span>
          </div>
        ))}
        <div className="flex items-center justify-between gap-3 px-2.5 py-1.5 text-xs text-ink-faint">
          <span>Model baseline &amp; calibration (not specific to this horse)</span>
          <span className="font-mono">{fmtSigned(baseline)}</span>
        </div>
        <div className="flex items-center justify-between gap-3 px-2.5 py-1.5 text-sm font-semibold">
          <span className="text-ink">Total adjustment</span>
          <span className={`font-mono ${adjustment > 0 ? 'text-emerald-deep' : adjustment < 0 ? 'text-rose' : 'text-ink-mute'}`}>
            {fmtSigned(adjustment)}
          </span>
        </div>
      </div>
    </div>
  )
}
