import { useEffect, useMemo, useRef, useState } from 'react'
import type { Race, Runner } from '../../types/domain'
import { computeCareerStats } from '../../lib/careerStats'
import { fmtAdj } from './rowParts'
import { fmtInt, fmtPrice, fmtWpr } from '../../lib/format'
import type { PriceMove } from '../../lib/priceMove'
import { isVoid } from '../../lib/wprVoid'

// Building blocks for the runner's detail page. Each takes plain values so RunnerDetailModal stays a layout file.

function ordinal(n: number): string {
  const v = n % 100
  if (v >= 11 && v <= 13) return `${n}th`
  return `${n}${({ 1: 'st', 2: 'nd', 3: 'rd' } as Record<number, string>)[n % 10] ?? 'th'}`
}

export function Tile({ label, children, sub, className = '' }: { label: string; children: React.ReactNode; sub?: React.ReactNode; className?: string }) {
  return (
    <div className={`min-w-0 rounded-lg bg-bg p-3 ${className}`}>
      <div className="text-[11px] font-semibold uppercase tracking-wide text-ink-faint">{label}</div>
      <div className="mt-1">{children}</div>
      {sub && <div className="mt-1 text-xs text-ink-mute">{sub}</div>}
    </div>
  )
}

/* ------------------------------------------------------------------ hero */

interface HeroProps {
  compact?: boolean
  runner: Runner
  race: Race
  proj: number | null
  scratched: boolean
  rank: number | null
  fieldSize: number
  fieldTop: number | null
  fair: number | null
  market: number | null
  fixedMove: PriceMove | null
  hasOverride: boolean
}

// The runner's rating (the race's ranking figure at today's weight), where it ranks, the market against the bet-signal model's price, and the basics.
export function HorseHero({ runner, race, proj, scratched, rank, fieldSize, fieldTop, fair, market, fixedMove, hasOverride, compact }: HeroProps) {
  const gap = proj != null && fieldTop != null ? fieldTop - proj : null
  const verdict =
    rank != null && !scratched
      ? `${ordinal(rank)} of ${fieldSize}${gap != null && gap > 0.05 ? `, ${gap.toFixed(1)} off the top` : ', top rated'}.`
      : scratched
        ? 'Scratched.'
        : ''
  return (
    <section className={compact ? 'rounded-md border border-line-soft bg-bg px-2.5 py-1.5' : 'rounded-lg border border-line bg-panel px-3 py-2.5 sm:px-4'}>
      <div className="grid grid-cols-[minmax(0,1fr)_auto] items-center gap-x-4 gap-y-1">
        <div className="min-w-0">
          <div className="flex flex-wrap items-center gap-2">
            <span className="text-[11px] font-semibold uppercase tracking-wide text-ink-faint">Rating</span>
            {hasOverride && <span className="rounded-full bg-amber-bg px-2 py-0.5 text-[11px] font-semibold text-amber">manually adjusted</span>}
          </div>
          {scratched ? (
            <div className="font-mono text-3xl font-bold leading-none text-rose">SCR</div>
          ) : (
            <div className={`font-mono font-bold leading-none text-emerald-deep ${compact ? 'text-2xl' : 'text-3xl'}`}>{fmtWpr(proj)}</div>
          )}
          {verdict && <p className="mt-1 text-xs text-ink-soft">{verdict}</p>}
        </div>
        <div className="flex-none text-right">
          <div className="text-[11px] font-semibold uppercase tracking-wide text-ink-faint">Market / model</div>
          <div className={`font-mono font-semibold leading-tight text-ink ${compact ? 'text-lg' : 'text-xl'}`}>
            {fmtPrice(market)} <span className="text-base font-normal text-ink-faint">/ {fair != null && !scratched ? fmtPrice(fair) : '-'}</span>
          </div>
          <div className="text-xs text-ink-mute">
            {fixedMove ? (
              <span className={fixedMove.direction === 'firmed' ? 'text-emerald-deep' : 'text-rose'}>
                {fixedMove.direction} {fixedMove.pctChange.toFixed(0)}% from {fmtPrice(runner.openFixedPrice)}
              </span>
            ) : (
              'no move since open'
            )}
          </div>
        </div>
      </div>
      <div className="mt-1.5 flex flex-wrap items-baseline gap-x-4 gap-y-0.5 border-t border-line-soft pt-1.5 text-xs">
        <span>
          <span className="text-[10px] uppercase tracking-wide text-ink-faint">TopRate </span>
          <span className="font-mono font-semibold text-ink-soft">{fmtInt(runner.toprateRating)}</span>
        </span>
        <span>
          <span className="text-[10px] uppercase tracking-wide text-ink-faint">Form </span>
          <span className="font-mono font-semibold text-ink-soft">{fmtInt(runner.formFactor)}</span>
        </span>
        <span>
          <span className="text-[10px] uppercase tracking-wide text-ink-faint">Nett </span>
          <span className="font-mono font-semibold text-ink-soft">{fmtInt(runner.wprNett)}</span>
        </span>
        <span className="font-semibold text-ink">
          Barrier {runner.barrier ?? '-'}
          {runner.weightCarried != null && <> &middot; {runner.weightCarried}kg</>}
          {race.distance ? <span className="font-normal text-ink-mute"> &middot; {race.distance}m</span> : null}
        </span>
      </div>
    </section>
  )
}

/* ----------------------------------------------------------- timeline */

// Every recent run as a dot: height is WPR, spacing is real time (so spells show as gaps), dot size and colour show how it finished. Drawn at the
// container's own width so the text stays crisp and the chart fills the card.
export function RunTimeline({ runner, raceDate }: { runner: Runner; raceDate: string }) {
  const wrapRef = useRef<HTMLDivElement>(null)
  const [width, setWidth] = useState(640)
  useEffect(() => {
    const el = wrapRef.current
    if (!el) return
    const ro = new ResizeObserver(() => setWidth(Math.max(300, Math.round(el.clientWidth))))
    ro.observe(el)
    setWidth(Math.max(300, Math.round(el.clientWidth)))
    return () => ro.disconnect()
  }, [])
  const dots = useMemo(() => {
    const byDate = new Map<string, Runner['recentRuns'][number]>()
    for (const r of runner.recentRuns) if (r.date) byDate.set(r.date.slice(0, 10), r)
    return runner.formHistory
      .filter((e) => e.wpr != null && e.date)
      .map((e) => ({ e, run: byDate.get(e.date.slice(0, 10)) ?? null }))
      .sort((a, b) => a.e.date.localeCompare(b.e.date))
      .slice(-14)
  }, [runner.formHistory, runner.recentRuns])
  // The measuring wrapper is always rendered, so the observer attaches even when the first horse shown has no timeline.
  if (dots.length < 2)
    return (
      <div ref={wrapRef} className="w-full">
        <p className="text-sm text-ink-mute">Fewer than two rated runs, so there is no timeline yet.</p>
      </div>
    )
  const narrow = width < 480
  const W = width
  const H = narrow ? 160 : 190
  const padL = 34
  const padR = narrow ? 56 : 76
  const padT = 14
  const padB = 24
  const t = (d: string) => new Date(d).getTime()
  const t0 = t(dots[0].e.date)
  const t1 = Math.max(t(raceDate), t(dots[dots.length - 1].e.date))
  const vals = dots.map((d) => d.e.wpr as number)
  const lo = Math.floor((Math.min(...vals) - 2) / 5) * 5
  const hi = Math.ceil((Math.max(...vals) + 2) / 5) * 5
  const X = (ms: number) => padL + 8 + ((ms - t0) / Math.max(1, t1 - t0)) * (W - padL - padR - 8)
  const Y = (v: number) => padT + (1 - (v - lo) / (hi - lo)) * (H - padT - padB)
  const ticks: number[] = []
  for (let v = lo; v <= hi; v += 5) ticks.push(v)
  const path = dots.map((d, i) => `${i ? 'L' : 'M'}${X(t(d.e.date)).toFixed(1)},${Y(d.e.wpr as number).toFixed(1)}`).join(' ')
  const months: { ms: number; label: string }[] = []
  const cur = new Date(t0)
  cur.setDate(1)
  cur.setMonth(cur.getMonth() + 1)
  while (cur.getTime() < t1) {
    months.push({ ms: cur.getTime(), label: cur.toLocaleString('en-AU', { month: 'short' }) + (cur.getMonth() === 0 ? ` ${cur.getFullYear()}` : '') })
    cur.setMonth(cur.getMonth() + 1)
  }
  const step = Math.ceil(months.length / (narrow ? 5 : 10))
  return (
    <div ref={wrapRef} className="w-full">
      <svg width={W} height={H} viewBox={`0 0 ${W} ${H}`} role="img" aria-label="Recent runs over time, with today's projection and the rating expected to win">
        {ticks.map((v) => (
          <g key={v}>
            <line x1={padL} x2={W - padR + 14} y1={Y(v)} y2={Y(v)} stroke="var(--color-line-soft)" />
            <text x={padL - 6} y={Y(v) + 3} textAnchor="end" fontSize={10} fill="var(--color-ink-faint)">
              {v}
            </text>
          </g>
        ))}
        {months.map((m, i) =>
          i % step ? null : (
            <text key={m.ms} x={X(m.ms)} y={H - 7} textAnchor="middle" fontSize={10} fill="var(--color-ink-faint)">
              {m.label}
            </text>
          ),
        )}
        <path d={path} fill="none" stroke="var(--color-slate)" strokeWidth={1.5} strokeOpacity={0.45} strokeLinejoin="round" />
        {dots.map((d) => {
          const fin = d.run?.finishPosition ?? null
          const r = fin === 1 ? 6.5 : fin != null && fin <= 3 ? 5.5 : 4.5
          const fill = d.e.isVoid ? 'var(--color-line)' : fin === 1 ? 'var(--color-amber)' : fin != null && fin <= 3 ? 'var(--color-emerald)' : 'var(--color-slate)'
          return (
            <g key={d.e.date}>
              <title>{`${d.e.date}${d.run ? ` ${d.run.track} ${d.run.distance}m` : ` ${d.e.distance}m`} ${d.e.going}: WPR ${fmtWpr(d.e.wpr)}${fin != null ? `, finished ${fin}` : ''}${d.e.isVoid ? ' (compromised run)' : ''}`}</title>
              <circle cx={X(t(d.e.date))} cy={Y(d.e.wpr as number)} r={r} fill={fill} stroke="#fff" strokeWidth={1.2} />
            </g>
          )
        })}
      </svg>
    </div>
  )
}

export function TimelineLegend({ atwOffset, weightKg }: { atwOffset: number | null; weightKg: number | null }) {
  const shifted = atwOffset != null && Math.abs(atwOffset) >= 0.05
  return (
    <div className="mt-1 flex flex-wrap gap-x-3 gap-y-1 text-[11px] text-ink-mute">
      <span>
        <span className="mr-1 inline-block h-2.5 w-2.5 rounded-full bg-amber align-middle" />
        won
      </span>
      <span>
        <span className="mr-1 inline-block h-2.5 w-2.5 rounded-full bg-emerald align-middle" />
        placed
      </span>
      <span>
        <span className="mr-1 inline-block h-2.5 w-2.5 rounded-full bg-slate align-middle" />
        unplaced
      </span>
      <span>
        <span className="mr-1 inline-block h-2.5 w-2.5 rounded-full bg-line align-middle" />
        compromised run
      </span>
      <span className="hidden sm:inline">Height is WPR; gaps between dots are real time (spells).</span>
      {shifted && (
        <span className="basis-full">
          Ratings are at today&apos;s weight{weightKg != null ? ` (${weightKg}kg)`: ''}, the same as the Recent runs table.
        </span>
      )}
    </div>
  )
}

/* ---------------------------------------------------------- scorecard */

// Today's conditions against this horse's own record: distance, going, spell position, with each average against its career average.
export function ConditionsScorecard({ runner, race }: { runner: Runner; race: Race }) {
  const rows = useMemo(() => computeCareerStats(runner, race), [runner, race])
  const career = rows.find((r) => r.label === 'Career')
  const allPicked = rows.filter((r) => r.label !== 'Career' && r.label !== 'Last 6mo')
  const picked = allPicked.filter((r) => r.runs > 0)
  const empty = allPicked.filter((r) => r.runs === 0)
  const heading = (label: string) => (label === rows[1]?.label ? `Today's distance (${label})` : label === rows[2]?.label ? `Going (${label})` : label)
  return (
    <div>
      {career && (
        <div className="mb-2 text-sm text-ink-soft">
          Career: <span className="font-mono font-semibold">{career.runs}</span> rated runs, average <span className="font-mono font-semibold">{fmtWpr(career.avg)}</span>, peak{' '}
          <span className="font-mono font-semibold">{fmtWpr(career.peak)}</span>
        </div>
      )}
      <div className="grid grid-cols-1 gap-1 sm:grid-cols-2 md:grid-cols-3 sm:gap-2">
        {picked.map((r) => {
          const d = r.vsCareerAvg
          return (
            <div key={r.label} className="flex items-baseline justify-between gap-2 rounded-lg bg-bg px-2.5 py-1.5 text-sm sm:block sm:p-2.5">
              <div className="truncate text-[11px] font-semibold uppercase tracking-wide text-ink-faint" title={heading(r.label)}>
                {heading(r.label)}
              </div>
              {r.runs === 0 ? (
                <div className="text-ink-mute sm:mt-1">no runs</div>
              ) : (
                <div className="text-right sm:mt-1 sm:text-left">
                  <span className="font-mono font-semibold text-ink">
                    {r.runs} run{r.runs === 1 ? '' : 's'} <span className="text-ink-faint">&middot;</span> avg {fmtWpr(r.avg)}
                  </span>
                  <span className={`ml-2 font-mono text-xs sm:ml-0 sm:block ${d == null ? 'text-ink-mute' : d > 0.5 ? 'text-emerald-deep' : d < -0.5 ? 'text-rose' : 'text-ink-mute'}`}>
                    {d == null ? 'no comparison' : `${fmtAdj(d)} vs career`}
                  </span>
                </div>
              )}
            </div>
          )
        })}
      </div>
      {empty.length > 0 && <div className="mt-1.5 text-xs text-ink-mute">No runs at: {empty.map((r) => heading(r.label).toLowerCase()).join(', ')}.</div>}
    </div>
  )
}

/* ------------------------------------------------------- price vs fair */

function fmtMin(m: number): string {
  if (m <= 0) return 'open'
  if (m < 60) return `+${Math.round(m)}m`
  return `+${(m / 60).toFixed(m % 60 === 0 ? 0 : 1)}h`
}

// The price over time with the bet-signal model's price as a dashed line. That model starts from the market price, so its price sits close to it; only the
// gap matters (edge), and it is experimental (lib/betSignals.ts).
export function PriceVsFair({ runner, fair }: { runner: Runner; fair: number | null }) {
  const pts = runner.priceSeries
  const market = runner.fixedWinPrice
  const vals = [...pts.map((p) => p.price), ...(fair != null ? [fair] : []), ...(market != null ? [market] : [])]
  if (pts.length < 2 || vals.length === 0) {
    return (
      <div className="text-sm text-ink-soft">
        {market != null ? (
          <>
            Fixed <span className="font-mono font-semibold">{fmtPrice(market)}</span>
            {fair != null && (
              <>
                , model <span className="font-mono">{fmtPrice(fair)}</span>
              </>
            )}
            . Not enough price snapshots to draw a line yet.
          </>
        ) : (
          'No price information yet.'
        )}
        {runner.startingPrice != null && <div className="mt-1 text-xs text-ink-mute">SP {fmtPrice(runner.startingPrice)}</div>}
      </div>
    )
  }
  const W = 420
  const H = 96
  const padL = 40
  const padR = 10
  const lo = Math.min(...vals)
  const hi = Math.max(...vals)
  const span = Math.max(0.5, hi - lo)
  const yl = lo - span * 0.15
  const yh = hi + span * 0.15
  const t1 = Math.max(...pts.map((p) => p.minutesSinceOpen), 1)
  const X = (m: number) => padL + (m / t1) * (W - padL - padR)
  const Y = (v: number) => 10 + (1 - (v - yl) / (yh - yl)) * (H - 34)
  const path = pts.map((p, i) => `${i ? 'L' : 'M'}${X(p.minutesSinceOpen).toFixed(1)},${Y(p.price).toFixed(1)}`).join(' ')
  const last = pts[pts.length - 1]
  return (
    <div>
      <svg viewBox={`0 0 ${W} ${H}`} className="h-auto w-full max-w-xl" role="img" aria-label="Price over time against the bet-signal model's price">
        {fair != null && (
          <>
            <line x1={padL} x2={W - padR} y1={Y(fair)} y2={Y(fair)} stroke="var(--color-emerald)" strokeDasharray="5 3" strokeWidth={1.5} />
            <text x={padL - 4} y={Y(fair) + 3} textAnchor="end" fontSize={10} fontWeight={600} fill="var(--color-emerald-deep)">
              {fmtPrice(fair)}
            </text>
          </>
        )}
        <path d={path} fill="none" stroke="var(--color-indigo)" strokeWidth={2} />
        {pts.map((p) => (
          <circle key={p.minutesSinceOpen} cx={X(p.minutesSinceOpen)} cy={Y(p.price)} r={2.5} fill="var(--color-indigo)" />
        ))}
        <circle cx={X(last.minutesSinceOpen)} cy={Y(last.price)} r={5} fill="var(--color-indigo)" stroke="#fff" strokeWidth={1.5} />
        <text x={padL - 4} y={Y(pts[0].price) + 3} textAnchor="end" fontSize={10} fill="var(--color-ink-mute)">
          {fair == null || Math.abs(Y(pts[0].price) - Y(fair)) > 12 ? fmtPrice(pts[0].price) : ''}
        </text>
        <text x={W - padR} y={Y(last.price) - 8} textAnchor="end" fontSize={11} fontWeight={600} fill="var(--color-indigo)">
          {fmtPrice(last.price)}
        </text>
        <text x={padL} y={H - 6} fontSize={10} fill="var(--color-ink-faint)">
          open
        </text>
        <text x={W - padR} y={H - 6} textAnchor="end" fontSize={10} fill="var(--color-ink-faint)">
          {fmtMin(t1)}
        </text>
      </svg>
      <div className="text-xs text-ink-mute">
        {fair != null ? (
          <>
            Dashed line is the bet-signal model's price. It starts from the market and corrects it, so it stays close; the Select and Volume tiers mark where it disagrees enough to bet. Experimental.
          </>
        ) : (
          'No model price for this runner (needs a drawn, fully priced field).'
        )}
        {runner.startingPrice != null && <> SP {fmtPrice(runner.startingPrice)}.</>}
      </div>
    </div>
  )
}

/* -------------------------------------------------------- result card */

// What the race itself says about the result: the market against the finish, the model's rank against the finish, a compromised-run flag from the
// stewards' and video comments (lib/wprVoid, the same test Review uses to leave a run out of the accuracy numbers) and the comments themselves.
function ResultContext({ runner }: { runner: Runner }) {
  const sp = runner.startingPrice
  const open = runner.openFixedPrice
  const lines: string[] = []
  if (sp != null) {
    const move = open != null && open > 1 ? (sp - open) / open : null
    const trend = move == null || Math.abs(move) < 0.1 ? '' : move < 0 ? `, firmed from ${fmtPrice(open)}` : `, eased from ${fmtPrice(open)}`
    lines.push(`Starting price ${fmtPrice(sp)}${trend}.`)
  }
  const v = isVoid(null, runner.commentsVideo, runner.commentsSteward)
  const hasText = (runner.commentsSteward ?? '').trim() !== '' || (runner.commentsVideo ?? '').trim() !== ''
  if (lines.length === 0 && !hasText) return null
  return (
    <div className="mt-2 space-y-1 border-t border-line-soft pt-2 text-sm text-ink-soft">
      {lines.map((l) => (
        <p key={l}>{l}</p>
      ))}
      {v.isVoid && <p className="text-amber">The run looks compromised ({v.reason}). Review leaves it out of the accuracy numbers.</p>}
      {hasText && (
        <details className="text-xs text-ink-mute">
          <summary className="cursor-pointer hover:text-ink">Race comments</summary>
          {runner.commentsSteward && <p className="mt-1"><span className="font-semibold">Stewards:</span> {runner.commentsSteward}</p>}
          {runner.commentsVideo && <p className="mt-1"><span className="font-semibold">Video:</span> {runner.commentsVideo}</p>}
        </details>
      )}
    </div>
  )
}


// After the race: how it finished, the actual rating it ran (ATW) and what the race itself said.
export function ResultCard({ runner }: { runner: Runner }) {
  const actual = runner.actualWpr
  const fin = runner.finishPosition
  if (fin == null && actual == null && !runner.resultKnown) {
    return <p className="text-sm text-ink-mute">The result and the actual rating show here after the race.</p>
  }
  return (
    <div>
      <div className="grid grid-cols-2 gap-2">
        <Tile label="Finish">
          <span className="font-mono text-xl font-semibold text-ink">{fin != null ? ordinal(fin) : runner.won ? '1st' : runner.resultKnown ? 'Unplaced' : '-'}</span>
        </Tile>
        <Tile label="Actual rating (ATW)">
          <span className="font-mono text-xl font-semibold text-emerald-deep">{actual != null ? fmtWpr(actual) : '-'}</span>
        </Tile>
      </div>
      <ResultContext runner={runner} />
      <p className="mt-2 text-sm text-ink-soft">
        {fin != null && runner.marginFinish != null && fin > 1 ? `Beaten ${runner.marginFinish.toFixed(1)}L. ` : ''}
        {actual == null ? 'The actual rating settles a few days after the race.' : ''}
      </p>
    </div>
  )
}
