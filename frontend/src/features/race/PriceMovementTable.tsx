import type { Runner } from '../../types/domain'
import { fmtPrice } from '../../lib/format'

interface PriceMovementTableProps {
  runner: Runner
}

function fmtMinutes(m: number): string {
  if (m <= 0) return 'Open'
  if (m < 60) return `+${Math.round(m)}m`
  const h = Math.floor(m / 60)
  const rem = Math.round(m % 60)
  return rem === 0 ? `+${h}h` : `+${h}h ${rem}m`
}

// Fixed-price snapshot history as a table - sits beside CareerStats (see
// RunnerDetailModal) so it fills the space that table otherwise leaves
// blank, and gives the exact captured prices the PriceTrend sparkline alone
// can't. Newest first so the current price is always the top row. Move %
// is coloured on the same "down = firming = good" convention as
// PriceTrend's invertColor (a shortening price is being backed).
export function PriceMovementTable({ runner }: PriceMovementTableProps) {
  if (runner.priceSeries.length < 2) return null
  const rows = [...runner.priceSeries].reverse()

  return (
    <div className="overflow-x-auto rounded-lg border border-line bg-panel p-2.5">
      <div className="mb-1.5 text-xs font-semibold text-ink">Price movement</div>
      <table className="w-full max-w-xs text-xs">
        <thead>
          <tr className="border-b border-line-soft text-ink-faint">
            <th className="pb-1 text-left font-normal">Time</th>
            <th className="pb-1 text-right font-normal">Fixed</th>
            <th className="pb-1 pl-2 text-right font-normal">Move</th>
          </tr>
        </thead>
        <tbody className="[&_td]:py-0.5 [&_td]:leading-5">
          {rows.map((p, i) => {
            const prev = rows[i + 1]
            const pctMove = prev ? ((p.price - prev.price) / prev.price) * 100 : null
            return (
              <tr key={p.minutesSinceOpen} className="border-b border-line-soft/60 last:border-0">
                <td className="whitespace-nowrap text-ink-mute">{fmtMinutes(p.minutesSinceOpen)}</td>
                <td className="text-right font-mono text-ink">{fmtPrice(p.price)}</td>
                <td className="pl-2 text-right font-mono">
                  {pctMove == null ? (
                    <span className="text-ink-faint">—</span>
                  ) : pctMove === 0 ? (
                    <span className="text-ink-faint">0%</span>
                  ) : (
                    <span className={pctMove < 0 ? 'text-emerald-deep' : 'text-rose'}>
                      {pctMove > 0 ? '+' : ''}
                      {pctMove.toFixed(0)}%
                    </span>
                  )}
                </td>
              </tr>
            )
          })}
        </tbody>
      </table>
    </div>
  )
}
