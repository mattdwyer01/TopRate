import { useMemo, useState } from 'react'
import type { Runner } from '../../types/domain'

interface WprTrendChartProps {
  runners: Runner[]
}

const WIDTH = 720
const HEIGHT = 260
const MARGIN = { top: 16, right: 88, bottom: 16, left: 36 }
const PLOT_W = WIDTH - MARGIN.left - MARGIN.right
const PLOT_H = HEIGHT - MARGIN.top - MARGIN.bottom
const MAX_PAST_RUNS = 8

interface TrendPoint {
  x: number // 0 = today (predicted); negative = runs back from today
  wpr: number
  date: string | null
  track: string | null
  predicted: boolean
}

interface TrendLine {
  runId: string
  tabNumber: number
  horse: string
  points: TrendPoint[]
}

// Anchored on TODAY (x=0, the predicted rating), not on raw run count - a
// horse with 4 runs and one with 10 both have their most recent ACTUAL run
// at x=-1, so "how has this horse trended INTO today" compares like for
// like across the field, rather than jumbling horses with different amounts
// of history at different x positions.
function buildLine(runner: Runner): TrendLine | null {
  const real = runner.recentRuns
    .filter((r) => r.wpr != null)
    .slice(0, MAX_PAST_RUNS)
    .reverse() // oldest -> newest
  const points: TrendPoint[] = real.map((r, i) => ({
    x: -(real.length - i),
    wpr: r.wpr as number,
    date: r.date ?? null,
    track: r.track,
    predicted: false,
  }))
  if (runner.projectedWpr != null) {
    points.push({ x: 0, wpr: runner.projectedWpr, date: null, track: null, predicted: true })
  }
  if (points.length < 2) return null
  return { runId: runner.runId, tabNumber: runner.tabNumber, horse: runner.horse, points }
}

function pathFor(points: TrendPoint[], xScale: (x: number) => number, yScale: (v: number) => number): string {
  return points.map((p, i) => `${i === 0 ? 'M' : 'L'}${xScale(p.x).toFixed(1)},${yScale(p.wpr).toFixed(1)}`).join(' ')
}

// Rating trend into today: each runner's recent WPR history (capped at the
// last 8 real runs) plus today's projection, all anchored so "today" lines
// up at the same x for every horse - lets you compare who's improving,
// steady, or fading heading into this specific race, at a glance across the
// whole field. One line is highlighted at a time (hover/tap) rather than a
// full N-colour legend - with up to 16+ runners a fixed categorical palette
// can't give each one a distinguishable hue, and the actual question this
// answers ("how is THIS horse trending") is naturally one-at-a-time.
export function WprTrendChart({ runners }: WprTrendChartProps) {
  const [activeId, setActiveId] = useState<string | null>(null)

  const lines = useMemo(
    () => runners.map(buildLine).filter((l): l is TrendLine => l !== null),
    [runners],
  )

  if (lines.length === 0) {
    return (
      <div className="rounded-lg border border-line bg-panel p-3 text-sm text-ink-mute">
        Not enough rating history to chart.
      </div>
    )
  }

  const allX = lines.flatMap((l) => l.points.map((p) => p.x))
  const allWpr = lines.flatMap((l) => l.points.map((p) => p.wpr))
  const minX = Math.min(...allX)
  const minWpr = Math.min(...allWpr)
  const maxWpr = Math.max(...allWpr)
  const wprPad = Math.max(1, (maxWpr - minWpr) * 0.12)
  const yLo = minWpr - wprPad
  const yHi = maxWpr + wprPad

  const xScale = (x: number) => ((x - minX) / (0 - minX || 1)) * PLOT_W
  const yScale = (v: number) => PLOT_H - ((v - yLo) / (yHi - yLo || 1)) * PLOT_H

  const yTicks: number[] = []
  const step = (yHi - yLo) / 4
  for (let i = 0; i <= 4; i++) yTicks.push(yLo + step * i)

  const active = lines.find((l) => l.runId === activeId) ?? null
  const activePoint = active
    ? active.points.find((p) => p.predicted) ?? active.points[active.points.length - 1]
    : null

  return (
    <div className="rounded-lg border border-line bg-panel p-3 shadow-[var(--shadow-1)]">
      <div className="flex flex-wrap items-baseline justify-between gap-2">
        <span className="text-sm font-semibold text-ink">Rating trend into today</span>
        <span className="text-xs text-ink-faint">
          Last {MAX_PAST_RUNS} WPR ratings &middot; hollow point = today&apos;s projection &middot; hover to highlight
        </span>
      </div>
      <svg
        viewBox={`0 0 ${WIDTH} ${HEIGHT}`}
        className="mt-1 w-full"
        role="img"
        aria-label="WPR rating trend per runner, ending in today's projection"
        onMouseLeave={() => setActiveId(null)}
      >
        <g transform={`translate(${MARGIN.left},${MARGIN.top})`}>
          {yTicks.map((t) => (
            <g key={t}>
              <line x1={0} y1={yScale(t)} x2={PLOT_W} y2={yScale(t)} stroke="var(--color-line-soft)" strokeWidth={1} />
              <text x={-8} y={yScale(t)} dy="0.32em" textAnchor="end" className="fill-ink-faint text-[10px]">
                {t.toFixed(0)}
              </text>
            </g>
          ))}
          <line
            x1={xScale(0)}
            y1={0}
            x2={xScale(0)}
            y2={PLOT_H}
            stroke="var(--color-line)"
            strokeWidth={1}
            strokeDasharray="2,3"
          />
          <text x={xScale(0)} y={PLOT_H + 12} textAnchor="middle" className="fill-ink-faint text-[10px]">
            Today
          </text>

          {/* Recessive pass: every non-hovered line, drawn first so the
              hovered one always sits on top. */}
          {lines.map((line) => {
            if (line.runId === activeId) return null
            const real = line.points.filter((p) => !p.predicted)
            const pred = line.points.find((p) => p.predicted)
            return (
              <g key={line.runId} className="cursor-pointer" onMouseEnter={() => setActiveId(line.runId)}>
                <path d={pathFor(real, xScale, yScale)} fill="none" stroke="var(--color-ink-faint)" strokeWidth={1.5} opacity={0.45} />
                {pred && real.length > 0 && (
                  <line
                    x1={xScale(real[real.length - 1].x)}
                    y1={yScale(real[real.length - 1].wpr)}
                    x2={xScale(pred.x)}
                    y2={yScale(pred.wpr)}
                    stroke="var(--color-ink-faint)"
                    strokeWidth={1.5}
                    strokeDasharray="3,3"
                    opacity={0.45}
                  />
                )}
                {/* invisible fat hit-area so hovering near the line (not
                    just exactly on the 1.5px stroke) picks it up */}
                <path d={pathFor(line.points, xScale, yScale)} fill="none" stroke="transparent" strokeWidth={10} />
              </g>
            )
          })}

          {/* Highlighted line, on top. */}
          {active &&
            (() => {
              const real = active.points.filter((p) => !p.predicted)
              const pred = active.points.find((p) => p.predicted)
              return (
                <g>
                  <path d={pathFor(real, xScale, yScale)} fill="none" stroke="var(--color-emerald-deep)" strokeWidth={2.5} strokeLinecap="round" />
                  {pred && real.length > 0 && (
                    <line
                      x1={xScale(real[real.length - 1].x)}
                      y1={yScale(real[real.length - 1].wpr)}
                      x2={xScale(pred.x)}
                      y2={yScale(pred.wpr)}
                      stroke="var(--color-emerald-deep)"
                      strokeWidth={2.5}
                      strokeDasharray="4,3"
                    />
                  )}
                  {real.map((p, i) => (
                    <circle key={i} cx={xScale(p.x)} cy={yScale(p.wpr)} r={3.5} fill="var(--color-emerald-deep)" />
                  ))}
                  {pred && (
                    <circle
                      cx={xScale(pred.x)}
                      cy={yScale(pred.wpr)}
                      r={4.5}
                      fill="var(--color-panel)"
                      stroke="var(--color-emerald-deep)"
                      strokeWidth={2.5}
                    />
                  )}
                </g>
              )
            })()}
        </g>
      </svg>

      {/* Tooltip-equivalent: fixed status line under the chart rather than a
          cursor-following box, so it never overlaps the plot on a narrow
          screen - names the hovered horse and its projection plainly. */}
      <div className="mt-1 h-4 text-xs text-ink-mute">
        {active && activePoint ? (
          <span>
            <span className="font-semibold text-ink">
              {active.tabNumber}. {active.horse}
            </span>
            {activePoint.predicted ? (
              <> &middot; today&apos;s projection {activePoint.wpr.toFixed(1)}</>
            ) : (
              <>
                {' '}
                &middot; {activePoint.date ?? ''} {activePoint.track ?? ''} &middot; {activePoint.wpr.toFixed(1)}
              </>
            )}
          </span>
        ) : (
          <span className="text-ink-faint">Hover a line to identify it.</span>
        )}
      </div>
    </div>
  )
}
