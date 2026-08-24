interface SparklineProps {
  values: number[]
  width?: number
  height?: number
  // Flips which direction counts as "good" (emerald) vs "bad" (rose) - the
  // default (false) treats a rising line as good (WPR trend, career form).
  // A price sparkline wants the opposite: price DROPPING is firming
  // (backed, good), price RISING is drifting (bad) - same convention as
  // lib/priceMove.ts's firmed/drifted colouring.
  invertColor?: boolean
}

// Minimal inline-SVG trend line - values assumed chronological (oldest
// first). Colour reflects direction (last point vs first), not magnitude -
// this is a "which way is it moving" glance, not a precise chart.
export function Sparkline({ values, width = 44, height = 16, invertColor = false }: SparklineProps) {
  if (values.length < 2) return <span className="text-ink-faint">—</span>

  const min = Math.min(...values)
  const max = Math.max(...values)
  const range = max - min || 1
  const pad = 2
  const points = values
    .map((v, i) => {
      const x = (i / (values.length - 1)) * (width - pad * 2) + pad
      const y = height - pad - ((v - min) / range) * (height - pad * 2)
      return `${x.toFixed(1)},${y.toFixed(1)}`
    })
    .join(' ')

  const trendingUp = values[values.length - 1] >= values[0]
  const isGood = invertColor ? !trendingUp : trendingUp
  const colorClass = isGood ? 'text-emerald-deep' : 'text-rose'

  return (
    // Tailwind's base reset makes svg display:block, so a `text-right` on a
    // containing <td> has no effect (text-align only steers inline content) -
    // this SVG just sat flush-left in its cell regardless, visibly adrift
    // from a right-aligned "Trend" header above it. block + ml-auto pushes
    // a block-level box with its own fixed width to the right explicitly.
    <svg
      width={width}
      height={height}
      viewBox={`0 0 ${width} ${height}`}
      className={`block ml-auto ${colorClass}`}
    >
      <polyline points={points} fill="none" stroke="currentColor" strokeWidth="1.5" strokeLinecap="round" strokeLinejoin="round" />
    </svg>
  )
}
