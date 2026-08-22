import { ADJUSTMENT_LABELS } from '../../lib/adjustmentLabels'

interface AdjustmentBreakdownProps {
  breakdown: Record<string, number>
}

const MIN_SHOWN = 0.05

// field_size and baseline are the same for every horse in a given race (a
// race-wide constant, and a global model constant respectively) - they
// shift every runner's WPR by the same amount, which the price/rank
// softmax is invariant to (see wpr_projection.py project_race). They don't
// distinguish this horse from the others in its own race, so they're
// excluded here as noise rather than a real "driver".
const NON_DIFFERENTIATING = new Set(['field_size', 'baseline'])

function fmtSigned(v: number): string {
  return `${v > 0 ? '+' : ''}${v.toFixed(2)}`
}

// What's actually driving this runner's adjustment RELATIVE TO OTHER
// RUNNERS IN THE SAME RACE - not just the two biggest reasons describe()
// narrates (it only speaks up when the total is >=3 WPR), the full
// picture, including small nudges. Wrapping pills rather than one row per
// feature - a compact strip instead of a tall list, since there can be up
// to 15 of these.
export function AdjustmentBreakdown({ breakdown }: AdjustmentBreakdownProps) {
  const rows = Object.entries(breakdown)
    .filter(([key, v]) => !NON_DIFFERENTIATING.has(key) && Math.abs(v) >= MIN_SHOWN)
    .sort((a, b) => Math.abs(b[1]) - Math.abs(a[1]))

  if (rows.length === 0) {
    return (
      <div className="text-sm text-ink-mute">
        Nothing about this horse's own situation moved the rating relative to the rest of the field.
      </div>
    )
  }

  return (
    <div>
      <div className="mb-1 text-sm font-semibold text-ink">What's driving the adjustment</div>
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
