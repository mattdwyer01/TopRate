import { ADJUSTMENT_LABELS } from '../../lib/adjustmentLabels'

interface AdjustmentBreakdownProps {
  breakdown: Record<string, number>
}

const MIN_SHOWN = 0.05

// baseline is the global calibration offset (wpr_projection.py's
// calib_offset) - the same for every horse in every race, not a
// horse-specific driver. Every other ADJ_TERMS key is this horse's own
// history vs its own career average, so it's excluded here as noise
// rather than a real "driver".
const NON_DIFFERENTIATING = new Set(['baseline'])

function fmtSigned(v: number): string {
  return `${v > 0 ? '+' : ''}${v.toFixed(2)}`
}

// What's actually driving this runner's adjustment RELATIVE TO OTHER
// RUNNERS IN THE SAME RACE - not just the two biggest reasons describe()
// narrates (it only speaks up when the total is >=3 WPR), the full
// picture, including small nudges. A plain two-column table rather than a
// wrapping pill strip - easier to scan down than to parse pill-by-pill.
export function AdjustmentBreakdown({ breakdown }: AdjustmentBreakdownProps) {
  const rows = Object.entries(breakdown)
    .filter(([key, v]) => !NON_DIFFERENTIATING.has(key) && Math.abs(v) >= MIN_SHOWN)
    .sort((a, b) => Math.abs(b[1]) - Math.abs(a[1]))

  if (rows.length === 0) {
    return (
      <div className="rounded-lg border border-line bg-panel p-2 text-sm text-ink-mute">
        Nothing about this horse's own situation moved the rating relative to the rest of the field.
      </div>
    )
  }

  return (
    <div className="rounded-lg border border-line bg-panel p-2">
      <div className="mb-0.5 text-xs font-semibold text-ink">What's driving the adjustment</div>
      <table className="w-full text-xs">
        <tbody className="[&_td]:py-0 [&_td]:leading-5">
          {rows.map(([key, v]) => (
            <tr key={key}>
              <td className="text-ink-soft">{ADJUSTMENT_LABELS[key] ?? key}</td>
              <td className={`text-right font-mono font-semibold ${v > 0 ? 'text-emerald-deep' : 'text-rose'}`}>
                {fmtSigned(v)}
              </td>
            </tr>
          ))}
        </tbody>
      </table>
    </div>
  )
}
