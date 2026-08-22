interface SparklineProps {
  values: number[]
  width?: number
  height?: number
}

// Minimal inline-SVG trend line - values assumed chronological (oldest
// first). Colour reflects direction (last point vs first), not magnitude -
// this is a "which way is it moving" glance, not a precise chart.
export function Sparkline({ values, width = 44, height = 16 }: SparklineProps) {
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
  const colorClass = trendingUp ? 'text-emerald-deep' : 'text-rose'

  return (
    <svg width={width} height={height} viewBox={`0 0 ${width} ${height}`} className={colorClass}>
      <polyline points={points} fill="none" stroke="currentColor" strokeWidth="1.5" strokeLinecap="round" strokeLinejoin="round" />
    </svg>
  )
}
