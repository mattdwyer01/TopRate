import { useMemo, useState } from 'react'
import type { Race, Runner } from '../../types/domain'
import type { TripRace } from '../../lib/tripMap'
import { computeCareerStats } from '../../lib/careerStats'
import { fmtInt, fmtPrice, fmtWpr } from '../../lib/format'
import type { PriceMove } from '../../lib/priceMove'
import { adjClass, fmtAdj, spellWord } from './rowParts'
import { typicalSd } from './raceFacts'

// Building blocks for the runner's detail page. Each takes plain values so RunnerDetailModal stays a layout file.

const HALF = 0.67 // likely range = about +-0.67 typical error (the middle half of outcomes)

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
  runner: Runner
  race: Race
  proj: number | null
  scratched: boolean
  rank: number | null
  fieldSize: number
  fieldTop: number | null
  fieldLow: number | null
  fair: number | null
  market: number | null
  fixedMove: PriceMove | null
  hasOverride: boolean
  spellLabel: string
  daysSince: number | null
}

// A likely range drawn against the whole field: the pale track is the field from lowest to highest projection, the bar is this horse's
// likely range, the dot its projection, the line the field's top.
function RangeGauge({ proj, sd, top, low }: { proj: number; sd: number | null; top: number | null; low: number | null }) {
  const half = sd != null ? HALF * sd : 0
  const lo = Math.min(proj - half, low ?? proj) - 3
  const hi = Math.max(proj + half, top ?? proj) + 3
  const W = 420
  const X = (v: number) => 6 + ((v - lo) / (hi - lo)) * (W - 12)
  return (
    <svg viewBox={`0 0 ${W} 58`} className="h-auto w-full max-h-12 sm:max-h-none" role="img" aria-label="Likely range of this projection against the field">
      {low != null && top != null && <rect x={X(low)} y={25} width={Math.max(2, X(top) - X(low))} height={6} rx={3} fill="var(--color-line-soft)" />}
      {half > 0 && <rect x={X(proj - half)} y={19} width={Math.max(4, X(proj + half) - X(proj - half))} height={18} rx={9} fill="var(--color-emerald-tint)" stroke="var(--color-emerald-line)" />}
      {top != null && (
        <>
          <line x1={X(top)} x2={X(top)} y1={9} y2={45} stroke="var(--color-indigo)" strokeWidth={2} />
          <text x={Math.min(X(top) + 5, W - 74)} y={13} fontSize={10} fill="var(--color-indigo)">
            field top {fmtWpr(top)}
          </text>
        </>
      )}
      <circle cx={X(proj)} cy={28} r={6} fill="var(--color-emerald-deep)" stroke="#fff" strokeWidth={1.5} />
      {half > 0 && (
        <>
          <text x={X(proj - half)} y={54} textAnchor="middle" fontSize={10} fill="var(--color-ink-mute)">
            {Math.round(proj - half)}
          </text>
          <text x={X(proj + half)} y={54} textAnchor="middle" fontSize={10} fill="var(--color-ink-mute)">
            {Math.round(proj + half)}
          </text>
        </>
      )}
    </svg>
  )
}

export function HorseHero({ runner, race, proj, scratched, rank, fieldSize, fieldTop, fieldLow, fair, market, fixedMove, hasOverride, spellLabel, daysSince }: HeroProps) {
  const sd = typicalSd(runner, proj)
  const priorRuns = runner.formHistory.length
  const gap = proj != null && fieldTop != null ? fieldTop - proj : null
  const reasons: string[] = []
  if (runner.projectionModel === 'light') reasons.push(`only ${priorRuns} prior run${priorRuns === 1 ? '' : 's'}, so the error is wider`)
  if (spellLabel === 'FS') reasons.push('first start')
  else if (spellLabel === 'FU') reasons.push(`first-up${daysSince != null ? ` after ${daysSince} days` : ''}`)
  else if (spellLabel !== '—' && /^\dU$/.test(spellLabel)) reasons.push(spellWord(spellLabel))
  if (sd != null && sd >= 10.5 && runner.projectionModel !== 'light') reasons.push('recent form is patchy')
  const verdict =
    rank != null && !scratched
      ? `${ordinal(rank)} of ${fieldSize}${gap != null && gap > 0.05 ? `, ${gap.toFixed(1)} off the top` : ', top rated'}.`
      : scratched
        ? 'Scratched.'
        : ''
  return (
    <section className="rounded-lg border border-line bg-panel p-3 sm:p-4">
      <div className="flex items-start gap-x-4 sm:gap-x-6">
        <div className="min-w-0 flex-1 sm:min-w-[210px]">
          <div className="flex flex-wrap items-center gap-2">
            <span className="text-[11px] font-semibold uppercase tracking-wide text-ink-faint">Projected WPR</span>
            {hasOverride && <span className="rounded-full bg-amber-bg px-2 py-0.5 text-[11px] font-semibold text-amber">manually adjusted</span>}
          </div>
          {scratched ? (
            <div className="font-mono text-4xl font-bold leading-tight text-rose">SCR</div>
          ) : (
            <div className="font-mono text-3xl font-bold leading-tight text-emerald-deep sm:text-4xl">{fmtWpr(proj)}</div>
          )}
          <p className="mt-1 max-w-[46ch] text-sm text-ink-soft">
            {verdict}
            {sd != null && !scratched && <> Typical error &plusmn;{sd.toFixed(0)}.</>}
            {reasons.length > 0 && !scratched && <> {reasons[0][0].toUpperCase() + reasons[0].slice(1)}{reasons.length > 1 ? `, ${reasons.slice(1).join(', ')}` : ''}.</>}
          </p>
        </div>
        <div className="flex-none text-right">
          <div className="text-[11px] font-semibold uppercase tracking-wide text-ink-faint">Market / fair</div>
          <div className="font-mono text-xl font-semibold text-ink sm:text-2xl">
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
      {proj != null && !scratched && (
        <div className="mt-2 max-w-xl">
          <RangeGauge proj={proj} sd={sd} top={fieldTop} low={fieldLow} />
          <div className="hidden text-[11px] text-ink-faint sm:block">Shaded bar is the likely range (the middle half of outcomes). Pale track is the whole field.</div>
        </div>
      )}
      <div className="mt-2 flex flex-wrap items-baseline gap-x-4 gap-y-0.5 border-t border-line-soft pt-2 text-sm">
        <span>
          <span className="text-[11px] uppercase tracking-wide text-ink-faint">TopRate </span>
          <span className="font-mono font-semibold text-ink-soft">{fmtInt(runner.toprateRating)}</span>
        </span>
        <span>
          <span className="text-[11px] uppercase tracking-wide text-ink-faint">Form </span>
          <span className="font-mono font-semibold text-ink-soft">{fmtInt(runner.formFactor)}</span>
        </span>
        <span>
          <span className="text-[11px] uppercase tracking-wide text-ink-faint">Nett </span>
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

/* ------------------------------------------------------------- waterfall */

function mean(xs: number[]): number | null {
  return xs.length ? xs.reduce((a, b) => a + b, 0) / xs.length : null
}

// Every step from the evidence to the projection as its own row: levels as bars on one WPR scale, adjustments as signed bars about a
// centre line.
export function ProjectionWaterfall({ runner, proj, deltaValue }: { runner: Runner; proj: number | null; deltaValue: number | null }) {
  const b = runner.adjustmentBreakdown
  const recent = mean(runner.formHistory.filter((e) => e.wpr != null && !e.isVoid).slice(-5).map((e) => e.wpr as number))
  const levels: { label: string; v: number | null; strong?: boolean }[] = [
    { label: 'Last 5 runs average', v: recent },
    { label: 'TopRate rating', v: runner.toprateRating },
    { label: 'Model base', v: runner.baseWpr, strong: true },
  ]
  const steps: { label: string; v: number | null }[] = []
  if (b && (b.suitability != null || b.weight != null)) {
    if (b.suitability != null) steps.push({ label: 'Suitability', v: b.suitability })
    if (b.weight != null) steps.push({ label: 'Weight carried', v: b.weight })
  } else if (runner.wprAdjustment != null) {
    steps.push({ label: 'Adjustments', v: runner.wprAdjustment })
  }
  if (deltaValue != null && deltaValue !== 0) steps.push({ label: 'Your adjustment', v: deltaValue })
  const all = [...levels.map((l) => l.v), proj].filter((v): v is number => v != null)
  const lo = all.length ? Math.min(...all) - 8 : 0
  const hi = all.length ? Math.max(...all) + 2 : 100
  const pct = (v: number) => Math.max(2, Math.min(100, ((v - lo) / (hi - lo)) * 100))
  return (
    <div className="flex flex-col gap-1.5 text-sm">
      {levels.map((l) =>
        l.v == null ? null : (
          <div key={l.label} className="grid grid-cols-[minmax(0,1.2fr)_minmax(0,1.6fr)_44px] items-center gap-2">
            <span className={l.strong ? 'font-semibold text-ink' : 'text-ink-mute'}>{l.label}</span>
            <span className="h-2 overflow-hidden rounded-full bg-line-soft">
              <span className={`block h-full rounded-full ${l.strong ? 'bg-slate' : 'bg-line'}`} style={{ width: `${pct(l.v)}%` }} />
            </span>
            <span className={`text-right font-mono ${l.strong ? 'font-semibold text-ink' : 'text-ink-mute'}`}>{fmtWpr(l.v)}</span>
          </div>
        ),
      )}
      {steps.map((s) => (
        <div key={s.label} className="grid grid-cols-[minmax(0,1.2fr)_minmax(0,1.6fr)_44px] items-center gap-2">
          <span className="text-ink-mute">{s.label}</span>
          <span className="relative h-2 rounded-full bg-line-soft">
            <span className="absolute left-1/2 top-[-2px] h-3 w-px bg-line" />
            {s.v != null && (
              <span
                className={`absolute top-0 h-full rounded-full ${s.v >= 0 ? 'bg-emerald' : 'bg-rose'}`}
                style={s.v >= 0 ? { left: '50%', width: `${Math.min(50, Math.abs(s.v) * 8)}%` } : { right: '50%', width: `${Math.min(50, Math.abs(s.v) * 8)}%` }}
              />
            )}
          </span>
          <span className={`text-right font-mono ${adjClass(s.v)}`}>{fmtAdj(s.v)}</span>
        </div>
      ))}
      <div className="grid grid-cols-[minmax(0,1.2fr)_minmax(0,1.6fr)_44px] items-center gap-2 border-t border-line-soft pt-1.5">
        <span className="font-semibold text-ink">Projected WPR</span>
        <span className="h-2 overflow-hidden rounded-full bg-line-soft">{proj != null && <span className="block h-full rounded-full bg-emerald" style={{ width: `${pct(proj)}%` }} />}</span>
        <span className="text-right font-mono font-semibold text-emerald-deep">{fmtWpr(proj)}</span>
      </div>
    </div>
  )
}

/* ------------------------------------------------------- mini trip map */

// This horse among its rivals at about 800m from home: lengths behind the leader across, metres off the rail down.
export function HorseTripMini({ trip, runnerId, excluded }: { trip: TripRace; runnerId: string; excluded: Set<string> }) {
  const rows = trip.runners.filter((r) => r.gap != null && (!excluded.has(r.rid) || r.rid === runnerId))
  const me = rows.find((r) => r.rid === runnerId)
  if (!me || rows.length < 2) return null
  const minG = Math.min(...rows.map((r) => r.gap as number))
  const gx = (r: (typeof rows)[number]) => (r.gap as number) - minG
  const maxG = Math.max(6, ...rows.map(gx)) + 1
  const maxL = Math.max(10, ...rows.map((r) => r.lane)) + 1.5
  const W = 420
  const H = 124
  const l = 8
  const rr = 8
  const X = (g: number) => W - rr - (g / maxG) * (W - l - rr)
  const Y = (m: number) => 14 + (m / maxL) * (H - 34)
  const mx = X(gx(me))
  const my = Y(me.lane)
  return (
    <svg viewBox={`0 0 ${W} ${H}`} className="h-auto w-full rounded-md bg-bg" role="img" aria-label="This horse's projected position among the field">
      <line x1={0} x2={W} y1={10} y2={10} stroke="var(--color-ink-faint)" strokeWidth={3} />
      <text x={W - 4} y={H - 4} textAnchor="end" fontSize={10} fill="var(--color-ink-mute)">
        front of the field
      </text>
      <text x={4} y={H - 4} fontSize={10} fill="var(--color-ink-mute)">
        further back
      </text>
      {rows
        .filter((r) => r.rid !== runnerId)
        .map((r) => (
          <g key={r.rid}>
            <ellipse cx={X(gx(r))} cy={Y(r.lane)} rx={9} ry={4} fill="var(--color-line)" />
            <text x={X(gx(r))} y={Y(r.lane) - 6} textAnchor="middle" fontSize={9} fill="var(--color-ink-faint)">
              {r.barrier}
            </text>
          </g>
        ))}
      <line x1={X(0)} x2={mx} y1={H - 16} y2={H - 16} stroke="var(--color-ink)" strokeWidth={1} />
      <line x1={X(0)} x2={X(0)} y1={H - 20} y2={H - 12} stroke="var(--color-ink)" strokeWidth={1} />
      <line x1={mx} x2={mx} y1={H - 20} y2={H - 12} stroke="var(--color-ink)" strokeWidth={1} />
      <text x={Math.min(Math.max((X(0) + mx) / 2, 62), W - 62)} y={H - 20} textAnchor="middle" fontSize={10} fill="var(--color-ink)">
        {gx(me).toFixed(1)}L behind leader
      </text>
      <ellipse cx={mx} cy={my} rx={11} ry={5} fill="var(--color-emerald-deep)" />
      <text x={Math.min(mx, W - 50)} y={my - 8} textAnchor="middle" fontSize={11} fontWeight={600} fill="var(--color-ink)">
        {me.barrier}. {me.name.length > 16 ? `${me.name.slice(0, 15)}…` : me.name}
      </text>
    </svg>
  )
}

/* ----------------------------------------------------------- timeline */

// Every recent run as a dot: height is WPR, spacing is real time (so spells show as gaps), dot size and colour show how it finished.
// The projection for today sits at the right with its likely range.
export function RunTimeline({ runner, proj, raceDate }: { runner: Runner; proj: number | null; raceDate: string }) {
  const sd = typicalSd(runner, proj)
  const dots = useMemo(() => {
    const byDate = new Map<string, Runner['recentRuns'][number]>()
    for (const r of runner.recentRuns) if (r.date) byDate.set(r.date.slice(0, 10), r)
    return runner.formHistory
      .filter((e) => e.wpr != null && e.date)
      .map((e) => ({ e, run: byDate.get(e.date.slice(0, 10)) ?? null }))
      .sort((a, b) => a.e.date.localeCompare(b.e.date))
      .slice(-14)
  }, [runner.formHistory, runner.recentRuns])
  if (dots.length < 2) return <p className="text-sm text-ink-mute">Fewer than two rated runs, so there is no timeline yet.</p>
  const W = 480
  const H = 128
  const padL = 30
  const padR = 52
  const t = (d: string) => new Date(d).getTime()
  const t0 = t(dots[0].e.date)
  const t1 = Math.max(t(raceDate), t(dots[dots.length - 1].e.date))
  const vals = [...dots.map((d) => d.e.wpr as number), ...(proj != null ? [proj - (sd ?? 0) * HALF, proj + (sd ?? 0) * HALF] : [])]
  const lo = Math.floor((Math.min(...vals) - 3) / 5) * 5
  const hi = Math.ceil((Math.max(...vals) + 3) / 5) * 5
  const X = (ms: number) => padL + ((ms - t0) / Math.max(1, t1 - t0)) * (W - padL - padR)
  const Y = (v: number) => 12 + (1 - (v - lo) / (hi - lo)) * (H - 40)
  const ticks: number[] = []
  for (let v = lo; v <= hi; v += 5) ticks.push(v)
  const path = dots.map((d, i) => `${i ? 'L' : 'M'}${X(t(d.e.date)).toFixed(1)},${Y(d.e.wpr as number).toFixed(1)}`).join(' ')
  const px = X(t(raceDate))
  const months: { ms: number; label: string }[] = []
  const cur = new Date(t0)
  cur.setDate(1)
  cur.setMonth(cur.getMonth() + 1)
  while (cur.getTime() < t1) {
    months.push({ ms: cur.getTime(), label: cur.toLocaleString('en-AU', { month: 'short' }) })
    cur.setMonth(cur.getMonth() + 1)
  }
  const step = Math.ceil(months.length / 8)
  return (
    <svg viewBox={`0 0 ${W} ${H}`} className="h-auto w-full max-w-2xl" role="img" aria-label="Recent runs over time, with today's projection">
      {ticks.map((v) => (
        <g key={v}>
          <line x1={padL} x2={W - padR + 10} y1={Y(v)} y2={Y(v)} stroke="var(--color-line-soft)" />
          <text x={padL - 4} y={Y(v) + 3} textAnchor="end" fontSize={10} fill="var(--color-ink-faint)">
            {v}
          </text>
        </g>
      ))}
      {months.map((m, i) =>
        i % step ? null : (
          <text key={m.ms} x={X(m.ms)} y={H - 6} textAnchor="middle" fontSize={10} fill="var(--color-ink-faint)">
            {m.label}
          </text>
        ),
      )}
      <path d={path} fill="none" stroke="var(--color-slate)" strokeWidth={1.5} strokeOpacity={0.45} />
      {proj != null && (
        <>
          {sd != null && <rect x={px - 7} y={Y(proj + sd * HALF)} width={14} height={Math.max(3, Y(proj - sd * HALF) - Y(proj + sd * HALF))} rx={4} fill="var(--color-emerald-tint)" stroke="var(--color-emerald-line)" />}
          <line x1={X(t(dots[dots.length - 1].e.date))} y1={Y(dots[dots.length - 1].e.wpr as number)} x2={px} y2={Y(proj)} stroke="var(--color-emerald-deep)" strokeDasharray="4 3" strokeWidth={1.5} />
          <circle cx={px} cy={Y(proj)} r={6} fill="var(--color-emerald-deep)" />
          <text x={px + 10} y={Y(proj) + 4} fontSize={11} fontWeight={600} fill="var(--color-emerald-deep)">
            {fmtWpr(proj)}
          </text>
        </>
      )}
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
  )
}

export function TimelineLegend() {
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

// The price over time with the model's fair price as a dashed line. The fair price is the model's own view; in testing it has not beaten the market.
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
                , fair <span className="font-mono">{fmtPrice(fair)}</span>
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
      <svg viewBox={`0 0 ${W} ${H}`} className="h-auto w-full max-w-xl" role="img" aria-label="Price over time against the model's fair price">
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
            Dashed line is the model's fair price (its view only). Backing runners the model rates above the market has not made money in testing.
          </>
        ) : (
          'No fair price for this runner.'
        )}
        {runner.startingPrice != null && <> SP {fmtPrice(runner.startingPrice)}.</>}
      </div>
    </div>
  )
}

/* -------------------------------------------------------- result card */

// After the race: projected against actual (ATW) with the miss sized against the horse's own typical error.
export function ResultCard({ runner }: { runner: Runner }) {
  const proj = runner.projectedWpr
  const actual = runner.actualWpr
  const fin = runner.finishPosition
  const sd = runner.projectionSd
  const miss = actual != null && proj != null ? actual - proj : null
  const big = miss != null && sd != null && Math.abs(miss) > sd
  if (fin == null && actual == null && !runner.resultKnown) {
    return <p className="text-sm text-ink-mute">The result and the actual rating show here after the race. Projection to beat: <span className="font-mono font-semibold text-ink">{fmtWpr(proj)}</span>.</p>
  }
  return (
    <div>
      <div className="grid grid-cols-3 gap-2">
        <Tile label="Projected">
          <span className="font-mono text-xl font-semibold text-ink">{fmtWpr(proj)}</span>
        </Tile>
        <Tile label="Actual (ATW)">
          <span className="font-mono text-xl font-semibold text-emerald-deep">{actual != null ? fmtWpr(actual) : '-'}</span>
        </Tile>
        <Tile label="Miss">
          <span className={`font-mono text-xl font-semibold ${miss == null ? 'text-ink-mute' : big ? 'text-amber' : miss >= 0 ? 'text-emerald-deep' : 'text-ink-soft'}`}>{miss != null ? fmtAdj(miss) : '-'}</span>
        </Tile>
      </div>
      <p className="mt-2 text-sm text-ink-soft">
        {fin != null ? <>Finished {ordinal(fin)}{runner.marginFinish != null && fin > 1 ? `, ${runner.marginFinish.toFixed(1)}L` : ''}. </> : runner.won ? 'Won. ' : runner.resultKnown ? 'Unplaced. ' : ''}
        {actual == null ? 'The actual rating settles a few days after the race.' : miss != null && big ? `Ran ${Math.abs(miss).toFixed(1)} ${miss >= 0 ? 'better' : 'worse'} than projected, more than the typical error of ${sd!.toFixed(0)}.` : miss != null ? 'Within the typical error of the projection.' : ''}
        {runner.missReason ? ` ${runner.missReason}` : ''}
      </p>
    </div>
  )
}

/* ------------------------------------------------------------ collapsible */

// A section that starts open on tablets and desktops and closed on phones, where vertical room is the scarce thing.
export function Collapsible({ title, note, defaultOpenWide = true, children }: { title: string; note?: React.ReactNode; defaultOpenWide?: boolean; children: React.ReactNode }) {
  const [open, setOpen] = useState(() => (typeof window === 'undefined' ? true : defaultOpenWide && window.matchMedia('(min-width: 768px)').matches))
  return (
    <div>
      <button type="button" onClick={() => setOpen((o) => !o)} aria-expanded={open} className="flex w-full items-baseline justify-between gap-2 text-left">
        <span className="text-xs font-semibold uppercase tracking-wide text-ink-faint">
          {open ? '▾' : '▸'} {title}
        </span>
        {note && <span className="text-[11px] text-ink-faint">{note}</span>}
      </button>
      {open && <div className="mt-1.5">{children}</div>}
    </div>
  )
}
