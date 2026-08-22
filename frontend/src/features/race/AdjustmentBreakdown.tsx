import { ADJUSTMENT_LABELS } from '../../lib/adjustmentLabels'

interface AdjustmentBreakdownProps {
  breakdown: Record<string, number>
}

const MIN_SHOWN = 0.05

// field_size, baseline, today_wet and cur_surface are all the same for
// every horse in a given race - a race-wide constant, a global model
// constant, and two features derived purely from today's going/track
// grading (see _going_is_wet/_going_surface in wpr_projection.py), with no
// horse-specific input at all. They shift every runner's WPR by the same
// amount, which the price/rank softmax is invariant to (see
// wpr_projection.py project_race). They don't distinguish this horse from
// the others in its own race, so they're excluded here as noise rather
// than a real "driver".
const NON_DIFFERENTIATING = new Set(['field_size', 'baseline', 'today_wet', 'cur_surface'])

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
