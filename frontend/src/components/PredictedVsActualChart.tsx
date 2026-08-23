import type { CalibrationBins } from '../lib/accuracyStats'

interface PredictedVsActualChartProps {
  bins: CalibrationBins
}

const WIDTH = 560
const HEIGHT = 360
const MARGIN = { top: 12, right: 16, bottom: 36, left: 44 }
const PLOT_W = WIDTH - MARGIN.left - MARGIN.right
const PLOT_H = HEIGHT - MARGIN.top - MARGIN.bottom

// Sequential single-hue density: opacity scales with sqrt(count/maxCount) so
// a handful of very dense cells don't wash out every lighter one - a
// standard density-plot technique. Emerald matches the app's existing
// "positive/primary" token rather than introducing a new hue for one chart.
const CELL_COLOR = '#059669' // --color-emerald
const MIN_OPACITY = 0.12

function opacityFor(count: number, maxCount: number): number {
  if (maxCount <= 0) return 0
  return MIN_OPACITY + (1 - MIN_OPACITY) * Math.sqrt(count / maxCount)
}

function niceStep(range: number): number {
  if (range <= 40) return 10
  if (range <= 80) return 20
  return 25
}

// Density-shaded predicted-vs-actual scatter (a "calibration plot"): if
// projections were perfect, every runner would sit on the diagonal. Binned
// rather than one dot per runner - with thousands of resulted runners a raw
// scatter is just an overplotted smear; a shaded grid reads the same shape
// (the cloud's width and any tilt/curve off the diagonal) without it.
export function PredictedVsActualChart({ bins }: PredictedVsActualChartProps) {
  const { min, max, cells, maxCount, binSize } = bins
  const range = max - min || 1
  const scale = (v: number) => ((v - min) / range) * PLOT_W

  const step = niceStep(range)
  const ticks: number[] = []
  for (let v = Math.ceil(min / step) * step; v <= max; v += step) ticks.push(v)

  if (cells.length === 0) {
    return (
      <div className="flex h-40 items-center justify-center rounded-lg border border-line bg-panel text-sm text-ink-mute">
        Not enough data to chart.
      </div>
    )
  }

  return (
    <div className="rounded-lg border border-line bg-panel p-3">
      <svg viewBox={`0 0 ${WIDTH} ${HEIGHT}`} className="w-full" role="img" aria-label="Predicted vs actual WPR density chart">
        <g transform={`translate(${MARGIN.left},${MARGIN.top})`}>
          {/* gridlines + ticks, recessive */}
          {ticks.map((t) => (
            <g key={`x${t}`}>
              <line x1={scale(t)} y1={0} x2={scale(t)} y2={PLOT_H} stroke="var(--color-line-soft)" strokeWidth={1} />
              <text x={scale(t)} y={PLOT_H + 16} textAnchor="middle" fontSize={10} fill="var(--color-ink-mute)">
                {t}
              </text>
            </g>
          ))}
          {ticks.map((t) => (
            <g key={`y${t}`}>
              <line x1={0} y1={PLOT_H - scale(t)} x2={PLOT_W} y2={PLOT_H - scale(t)} stroke="var(--color-line-soft)" strokeWidth={1} />
              <text x={-8} y={PLOT_H - scale(t) + 3} textAnchor="end" fontSize={10} fill="var(--color-ink-mute)">
                {t}
              </text>
            </g>
          ))}

          {/* density cells */}
          {cells.map((c) => {
            const x = scale(c.predLo)
            const w = scale(c.predLo + binSize) - x
            const h = scale(c.actualLo + binSize) - scale(c.actualLo)
            const y = PLOT_H - scale(c.actualLo) - h
            return (
              <rect
                key={`${c.predLo}-${c.actualLo}`}
                x={x}
                y={y}
                width={Math.max(w, 1)}
                height={Math.max(Math.abs(h), 1)}
                fill={CELL_COLOR}
                fillOpacity={opacityFor(c.count, maxCount)}
              >
                <title>
                  Predicted {c.predLo}-{c.predLo + binSize}, actual {c.actualLo}-{c.actualLo + binSize}: {c.count}{' '}
                  runner{c.count === 1 ? '' : 's'}
                </title>
              </rect>
            )
          })}

          {/* y=x reference line - a perfect projection would land every runner here */}
          <line
            x1={0}
            y1={PLOT_H}
            x2={PLOT_W}
            y2={0}
            stroke="var(--color-ink-faint)"
            strokeWidth={1.5}
            strokeDasharray="4 3"
          />

          <text x={PLOT_W - 4} y={10} textAnchor="end" fontSize={10} fill="var(--color-ink-faint)">
            perfect projection
          </text>

          {/* axis titles */}
          <text x={PLOT_W / 2} y={PLOT_H + 30} textAnchor="middle" fontSize={11} fill="var(--color-ink-soft)">
            Predicted WPR
          </text>
          <text
            x={-PLOT_H / 2}
            y={-32}
            textAnchor="middle"
            fontSize={11}
            fill="var(--color-ink-soft)"
            transform="rotate(-90)"
          >
            Actual WPR
          </text>
        </g>
      </svg>
      <div className="mt-1 flex items-center justify-end gap-1.5 text-xs text-ink-mute">
        <span>Fewer runners</span>
        <span className="flex h-3 w-16 overflow-hidden rounded-sm border border-line-soft">
          {[0.15, 0.35, 0.55, 0.75, 1].map((o) => (
            <span key={o} className="flex-1" style={{ backgroundColor: CELL_COLOR, opacity: o }} />
          ))}
        </span>
        <span>More runners</span>
      </div>
    </div>
  )
}
