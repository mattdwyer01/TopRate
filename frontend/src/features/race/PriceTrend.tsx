import type { Runner } from '../../types/domain'
import { Sparkline } from '../../components/Sparkline'

interface PriceTrendProps {
  runner: Runner
}

// Intraday fixed-price sparkline - real snapshot history now that
// toprate_price_history.csv is committed (Aug 2026, previously local-only
// so it never actually accumulated across GitHub Actions runs). Sits next
// to the existing open-vs-current text rather than replacing it - the
// shape is a glance ("has it been drifting steadily, or just moved once"),
// the text still carries the exact numbers. invertColor: a price DROPPING
// is firming (backed, good = emerald), rising is drifting (bad = rose) -
// opposite of Sparkline's default "up is good" (WPR trend) convention.
export function PriceTrend({ runner }: PriceTrendProps) {
  if (runner.priceSeries.length < 2) return null
  return (
    <Sparkline
      values={runner.priceSeries.map((p) => p.price)}
      width={56}
      height={18}
      invertColor
    />
  )
}
