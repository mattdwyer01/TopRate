import { useMemo, useState } from 'react'
import type { ReactNode } from 'react'
import type { Race, Runner } from '../../types/domain'
import { goingBand } from '../../lib/pace'

interface WprTrendChartProps {
  runners: Runner[]
  race: Race
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
  distance: number | null
  going: string | null
  finishPosition: number | null
  margin: number | null
  daysSinceLast: number | null // gap since the PREVIOUS run in this same sequence
  predicted: boolean
  matchesToday: boolean // distance/going match, per the active filters - see matchFlags()
}

interface TrendLine {
  runId: string
  tabNumber: number
  horse: string
  points: TrendPoint[]
}

interface HoverKey {
  runId: string
  index: number
}

function parseISO(s: string | null | undefined): Date | null {
  if (!s) return null
  const t = Date.parse(s)
  return Number.isNaN(t) ? null : new Date(t)
}

function daysBetween(a: Date | null, b: Date | null): number | null {
  if (!a || !b) return null
  return Math.round((a.getTime() - b.getTime()) / 86_400_000)
}

// Anchored on TODAY (x=0, the predicted rating), not on raw run count - a
// horse with 4 runs and one with 10 both have their most recent ACTUAL run
// at x=-1, so "how has this horse trended INTO today" compares like for
// like across the field, rather than jumbling horses with different amounts
// of history at different x positions.
function buildLine(
  runner: Runner,
  race: Race,
  filterDistance: boolean,
  filterGoing: boolean,
): TrendLine | null {
  const real = runner.recentRuns
    .filter((r) => r.wpr != null)
    .slice(0, MAX_PAST_RUNS)
    .reverse() // oldest -> newest

  const distLo = race.distance * 0.9
  const distHi = race.distance * 1.1
  const raceBand = goingBand(race.going)

  const points: TrendPoint[] = real.map((r, i) => {
    const prevDate = i > 0 ? parseISO(real[i - 1].date) : null
    const distOk = !filterDistance || (r.distance >= distLo && r.distance <= distHi)
    const goingOk = !filterGoing || goingBand(r.going) === raceBand
    return {
      x: -(real.length - i),
      wpr: r.wpr as number,
      date: r.date ?? null,
      track: r.track,
      distance: r.distance,
      going: r.going,
      finishPosition: r.finishPosition,
      margin: r.margin,
      daysSinceLast: daysBetween(parseISO(r.date), prevDate),
      predicted: false,
      matchesToday: (filterDistance || filterGoing) && distOk && goingOk,
    }
  })
  if (runner.projectedWpr != null) {
    const lastReal = real.length > 0 ? parseISO(real[real.length - 1].date) : null
    points.push({
      x: 0,
      wpr: runner.projectedWpr,
      date: race.date,
      track: race.venue,
      distance: race.distance,
      going: race.going,
      finishPosition: null,
      margin: null,
      daysSinceLast: daysBetween(parseISO(race.date), lastReal),
      predicted: true,
      matchesToday: false,
    })
  }
  if (points.length < 2) return null
  return { runId: runner.runId, tabNumber: runner.tabNumber, horse: runner.horse, points }
}

function pathFor(points: TrendPoint[], xScale: (x: number) => number, yScale: (v: number) => number): string {
  return points.map((p, i) => `${i === 0 ? 'M' : 'L'}${xScale(p.x).toFixed(1)},${yScale(p.wpr).toFixed(1)}`).join(' ')
}

function FilterButton({
  active,
  onClick,
  children,
}: {
  active: boolean
  onClick: () => void
  children: ReactNode
}) {
  return (
    <button
      type="button"
      onClick={onClick}
      className={`rounded-full border px-2 py-0.5 text-[11px] font-medium transition-colors ${
        active
          ? 'border-amber bg-amber-bg text-amber'
          : 'border-line text-ink-mute hover:border-line-soft hover:text-ink'
      }`}
    >
      {children}
    </button>
  )
}

function finLabel(p: TrendPoint): string | null {
  if (p.finishPosition == null) return null
  const ord = p.finishPosition === 1 ? 'st' : p.finishPosition === 2 ? 'nd' : p.finishPosition === 3 ? 'rd' : 'th'
  const margin = p.margin != null && p.margin > 0 ? ` (${p.margin.toFixed(1)}L)` : ''
  return `${p.finishPosition}${ord}${margin}`
}

// Rating trend into today: each runner's recent WPR history (capped at the
// last 8 real runs) plus today's projection, all anchored so "today" lines
// up at the same x for every horse - lets you compare who's improving,
// steady, or fading heading into this specific race, at a glance across the
// whole field. One line is highlighted at a time (hover/tap) rather than a
// full N-colour legend - with up to 16+ runners a fixed categorical palette
// can't give each one a distinguishable hue, and the actual question this
// answers ("how is THIS horse trending") is naturally one-at-a-time.
//
// Dist/Going filters (same matching convention as RecentRunsTable's own
// filters - +/-10% distance band, same going band) don't hide anything here
// (a trend chart needs its continuity) - instead they mark which past
// points were run under conditions like today's, across EVERY line at once,
// so "has this field seen today's trip/going before, and how did they rate"
// reads at a glance without needing to hover each horse individually.
export function WprTrendChart({ runners, race }: WprTrendChartProps) {
  const [hover, setHover] = useState<HoverKey | null>(null)
  const [filterDistance, setFilterDistance] = useState(false)
  const [filterGoing, setFilterGoing] = useState(false)

  const lines = useMemo(
    () =>
      runners
        .map((r) => buildLine(r, race, filterDistance, filterGoing))
        .filter((l): l is TrendLine => l !== null),
    [runners, race, filterDistance, filterGoing],
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

  const activeLine = hover ? lines.find((l) => l.runId === hover.runId) ?? null : null
  const activePoint = activeLine && hover ? activeLine.points[hover.index] ?? null : null

  return (
    <div className="rounded-lg border border-line bg-panel p-3 shadow-[var(--shadow-1)]">
      <div className="flex flex-wrap items-baseline justify-between gap-2">
        <span className="text-sm font-semibold text-ink">Rating trend into today</span>
        <span className="text-xs text-ink-faint">
          Last {MAX_PAST_RUNS} WPR ratings &middot; hollow point = today&apos;s projection &middot; hover a point for
          detail
        </span>
      </div>

      <div className="mt-1.5 flex flex-wrap items-center gap-1.5">
        <span className="text-[11px] text-ink-faint">Highlight runs at today&apos;s:</span>
        <FilterButton active={filterDistance} onClick={() => setFilterDistance((v) => !v)}>
          Distance &plusmn;10% ({race.distance}m)
        </FilterButton>
        <FilterButton active={filterGoing} onClick={() => setFilterGoing((v) => !v)}>
          Going ({race.going || '—'})
        </FilterButton>
      </div>

      <svg
        viewBox={`0 0 ${WIDTH} ${HEIGHT}`}
        className="mt-1 w-full"
        role="img"
        aria-label="WPR rating trend per runner, ending in today's projection"
        onMouseLeave={() => setHover(null)}
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
            const isActive = line.runId === hover?.runId
            if (isActive) return null
            const real = line.points.filter((p) => !p.predicted)
            const pred = line.points.find((p) => p.predicted)
            return (
              <g key={line.runId}>
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
                {/* condition-match markers - visible on every line, not just
                    the hovered one, so a filter surfaces the whole field at
                    once (see the component docstring above) */}
                {real
                  .filter((p) => p.matchesToday)
                  .map((p, i) => (
                    <circle key={`m${i}`} cx={xScale(p.x)} cy={yScale(p.wpr)} r={3.5} fill="none" stroke="var(--color-amber)" strokeWidth={2} />
                  ))}
                {/* per-point hover targets (bigger invisible circle, small
                    visible dot) so a specific run can be identified, not
                    just "this line somewhere" */}
                {line.points.map((p, i) => (
                  <g key={i} className="cursor-pointer" onMouseEnter={() => setHover({ runId: line.runId, index: i })}>
                    <circle cx={xScale(p.x)} cy={yScale(p.wpr)} r={2} fill="var(--color-ink-faint)" opacity={0.45} />
                    <circle cx={xScale(p.x)} cy={yScale(p.wpr)} r={8} fill="transparent" />
                  </g>
                ))}
              </g>
            )
          })}

          {/* Highlighted line, on top. */}
          {activeLine &&
            (() => {
              const real = activeLine.points.filter((p) => !p.predicted)
              const pred = activeLine.points.find((p) => p.predicted)
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
                  {real
                    .filter((p) => p.matchesToday)
                    .map((p, i) => (
                      <circle key={`m${i}`} cx={xScale(p.x)} cy={yScale(p.wpr)} r={5} fill="none" stroke="var(--color-amber)" strokeWidth={2} />
                    ))}
                  {activeLine.points.map((p, i) => {
                    const isHovered = hover?.index === i
                    return p.predicted ? (
                      <circle
                        key={i}
                        cx={xScale(p.x)}
                        cy={yScale(p.wpr)}
                        r={isHovered ? 5.5 : 4.5}
                        fill="var(--color-panel)"
                        stroke="var(--color-emerald-deep)"
                        strokeWidth={2.5}
                        className="cursor-pointer"
                        onMouseEnter={() => setHover({ runId: activeLine.runId, index: i })}
                      />
                    ) : (
                      <circle
                        key={i}
                        cx={xScale(p.x)}
                        cy={yScale(p.wpr)}
                        r={isHovered ? 4.5 : 3.5}
                        fill="var(--color-emerald-deep)"
                        className="cursor-pointer"
                        onMouseEnter={() => setHover({ runId: activeLine.runId, index: i })}
                      />
                    )
                  })}
                </g>
              )
            })()}
        </g>
      </svg>

      {/* Tooltip-equivalent: fixed status line under the chart rather than a
          cursor-following box, so it never overlaps the plot on a narrow
          screen - names the hovered horse and the specific run's detail. */}
      <div className="mt-1 min-h-8 text-xs text-ink-mute">
        {activeLine && activePoint ? (
          <div>
            <span className="font-semibold text-ink">
              {activeLine.tabNumber}. {activeLine.horse}
            </span>
            {activePoint.predicted ? (
              <>
                {' '}
                &middot; <span className="font-medium text-ink">today&apos;s projection {activePoint.wpr.toFixed(1)}</span>
                {' '}&middot; {race.venue} &middot; {race.distance}m &middot; {race.going || '—'}
                {activePoint.daysSinceLast != null && <> &middot; {activePoint.daysSinceLast}d since last run</>}
              </>
            ) : (
              <>
                {' '}
                &middot; {activePoint.date ?? ''} {activePoint.track ?? ''} &middot; {activePoint.distance ?? '—'}m &middot;{' '}
                {activePoint.going || '—'}
                {activePoint.daysSinceLast != null && <> &middot; {activePoint.daysSinceLast}d since prior run</>}
                {finLabel(activePoint) && <> &middot; fin {finLabel(activePoint)}</>}
                {' '}&middot; <span className="font-medium text-ink">WPR {activePoint.wpr.toFixed(1)}</span>
                {activePoint.matchesToday && <span className="ml-1 text-amber">&middot; matches today</span>}
              </>
            )}
          </div>
        ) : (
          <span className="text-ink-faint">Hover a point to see its date, distance, going and result.</span>
        )}
      </div>
    </div>
  )
}
