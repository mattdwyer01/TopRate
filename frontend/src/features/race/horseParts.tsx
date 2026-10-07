import { useMemo, useState } from 'react'
import type { Race, Runner } from '../../types/domain'
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
    <svg viewBox={`0 0 ${W} 58`} className="h-auto w-full max-h-12" role="img" aria-label="Likely range of this projection against the field">
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
    <section className="rounded-lg border border-line bg-panel px-3 py-2.5 sm:px-4">
      <div className="grid grid-cols-[minmax(0,1fr)_auto] items-center gap-x-4 gap-y-1 lg:grid-cols-[minmax(150px,auto)_minmax(0,1fr)_auto] lg:gap-x-6">
        <div className="min-w-0">
          <div className="flex flex-wrap items-center gap-2">
            <span className="text-[11px] font-semibold uppercase tracking-wide text-ink-faint">Projected WPR</span>
            {hasOverride && <span className="rounded-full bg-amber-bg px-2 py-0.5 text-[11px] font-semibold text-amber">manually adjusted</span>}
          </div>
          {scratched ? (
            <div className="font-mono text-3xl font-bold leading-none text-rose">SCR</div>
          ) : (
            <div className="font-mono text-3xl font-bold leading-none text-emerald-deep">{fmtWpr(proj)}</div>
          )}
          <p className="mt-1 text-xs text-ink-soft">
            {verdict}
            {sd != null && !scratched && <> Error &plusmn;{sd.toFixed(0)}.</>}
            {reasons.length > 0 && !scratched && <> {reasons[0][0].toUpperCase() + reasons[0].slice(1)}{reasons.length > 1 ? `, ${reasons.slice(1).join(', ')}` : ''}.</>}
          </p>
        </div>
        {proj != null && !scratched && (
          <div className="order-last col-span-2 min-w-0 lg:order-none lg:col-span-1" title="Shaded bar is the likely range (the middle half of outcomes). Pale track is the whole field.">
            <RangeGauge proj={proj} sd={sd} top={fieldTop} low={fieldLow} />
          </div>
        )}
        <div className="flex-none text-right">
          <div className="text-[11px] font-semibold uppercase tracking-wide text-ink-faint">Market / fair</div>
          <div className="font-mono text-xl font-semibold leading-tight text-ink">
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

/* ------------------------------------------------------------- waterfall */

// What each correction group is made of, and how far it typically moves a rating (5th to 95th percentile, and the extremes, over the
// last 60 days of runs, 23,820 runs in 2,947 races, scored as of each race). The groups are TreeSHAP sums of the main model's correction on top of the recent-form anchor.
const GROUPS: { key: string; label: string; what: string; p5: number; p95: number; min: number; max: number }[] = [
  { key: 'form', label: 'Form pattern', what: 'Shape of the recent WPRs: consistency, best and worst of the last 5, change from the run before', p5: -1.25, p95: 1.75, min: -4.74, max: 14.54 },
  { key: 'rest', label: 'Spell and trials', what: 'Days since the last run, run number in the prep, trials, first-up and second-up record', p5: -0.7, p95: 1.35, min: -4.55, max: 5.69 },
  { key: 'class', label: 'Class and grade', what: 'Class and grade today against the last run, and the level of the track', p5: -1.41, p95: 0.87, min: -5.32, max: 1.8 },
  { key: 'going', label: 'Going', what: 'Today\'s going, the change from the last run, and the horse\'s record on it', p5: -1.27, p95: 0.7, min: -3.62, max: 1.44 },
  { key: 'dist_track', label: 'Distance and track', what: 'Today\'s distance and its change, and the horse\'s record at the distance and the track', p5: -1.06, p95: 1.34, min: -12.81, max: 3.42 },
  { key: 'connections', label: 'Jockey and trainer', what: 'Jockey and trainer effect, their form, the combination, and a jockey change', p5: -2.07, p95: 1.55, min: -9.55, max: 3.26 },
  { key: 'weight_age', label: 'Weight, age, sex', what: 'Weight carried and allowance in the model\'s own features, age and sex (the separate weight step comes after the base)', p5: -1.31, p95: 0.83, min: -3.46, max: 2.62 },
  { key: 'field', label: 'Field and barrier', what: 'Barrier, field size, and how today\'s rivals rate against this horse', p5: -1.98, p95: 2.51, min: -4.11, max: 11.01 },
  { key: 'comments', label: 'Run comments', what: 'What the race comments said about the last runs (checked, wide, held up and so on)', p5: -0.93, p95: 0.87, min: -3.48, max: 2.89 },
]
const SCALE = 3 // WPR points either side of zero drawn on the adjustment rows

function Level({ label, v, lo, hi, strong, title }: { label: string; v: number; lo: number; hi: number; strong?: boolean; title?: string }) {
  const pct = Math.max(2, Math.min(100, ((v - lo) / (hi - lo)) * 100))
  return (
    <div title={title} className="grid grid-cols-[minmax(0,1.3fr)_minmax(0,1.6fr)_44px] items-center gap-2">
      <span className={strong ? 'font-semibold text-ink' : 'text-ink-mute'}>{label}</span>
      <span className="h-2 overflow-hidden rounded-full bg-line-soft">
        <span className={`block h-full rounded-full ${strong ? 'bg-slate' : 'bg-line'}`} style={{ width: `${pct}%` }} />
      </span>
      <span className={`text-right font-mono ${strong ? 'font-semibold text-ink' : 'text-ink-mute'}`}>{fmtWpr(v)}</span>
    </div>
  )
}

// A signed step about a centre line. When a typical range is given it is drawn as a pale band behind the bar, so a +1.2 reads as small
// for a group that often moves 2 and large for one that rarely moves 0.5.
function Step({ label, v, range, title }: { label: string; v: number; range?: { p5: number; p95: number }; title?: string }) {
  const w = (x: number) => Math.min(50, (Math.abs(x) / SCALE) * 50)
  return (
    <div title={title} className="grid grid-cols-[minmax(0,1.3fr)_minmax(0,1.6fr)_44px] items-center gap-2">
      <span className="text-ink-mute">{label}</span>
      <span className="relative h-2 rounded-full bg-line-soft">
        <span className="absolute left-1/2 top-[-2px] h-3 w-px bg-line" />
        {range && <span className="absolute top-[-1px] h-[10px] rounded-full bg-line/60" style={{ left: `${50 + (Math.max(-SCALE, range.p5) / SCALE) * 50}%`, width: `${((Math.min(SCALE, range.p95) - Math.max(-SCALE, range.p5)) / SCALE) * 50}%` }} />}
        <span className={`absolute top-0 h-full rounded-full ${v >= 0 ? 'bg-emerald' : 'bg-rose'}`} style={v >= 0 ? { left: '50%', width: `${w(v)}%` } : { right: '50%', width: `${w(v)}%` }} />
      </span>
      <span className={`text-right font-mono ${adjClass(v)}`}>{fmtAdj(v)}</span>
    </div>
  )
}

// From the recent-form anchor to the projection. The main model starts from a weighted average of recent form and corrects it for the
// factors in GROUPS; the shaded band behind each bar is how far that factor typically moves a rating. Runners from before the breakdown was
// logged, and light-history runners, get base, suitability and weight only.
export function ProjectionWaterfall({ runner, proj, deltaValue }: { runner: Runner; proj: number | null; deltaValue: number | null }) {
  const [all, setAll] = useState(false)
  const b = runner.adjustmentBreakdown
  const anchor = b?.g_anchor
  const groups = anchor != null ? GROUPS.map((g) => ({ ...g, v: b?.['g_' + g.key] ?? 0 })).sort((x, y) => Math.abs(y.v) - Math.abs(x.v)) : []
  const shown = groups.filter((g) => Math.abs(g.v) >= 0.15)
  const small = groups.filter((g) => Math.abs(g.v) < 0.15)
  const lead = all ? shown : shown.slice(0, 4)
  const hiddenCount = shown.length - lead.length + (small.length ? 1 : 0)
  const steps: { label: string; v: number; title?: string }[] = []
  if (b && (b.suitability != null || b.weight != null)) {
    if (b.suitability != null) steps.push({ label: 'Suitability', v: b.suitability, title: 'Comment history, day-of bias, finishing profile and jockey/trainer tendencies' })
    if (b.weight != null) steps.push({ label: 'Weight carried', v: b.weight, title: 'About 0.4 WPR per kg above the field average' })
  } else if (runner.wprAdjustment != null) {
    steps.push({ label: 'Adjustments', v: runner.wprAdjustment })
  }
  if (deltaValue != null && deltaValue !== 0) steps.push({ label: 'Your adjustment', v: deltaValue })
  const levels = [anchor, runner.baseWpr, proj].filter((v): v is number => v != null)
  const lo = levels.length ? Math.min(...levels) - 8 : 0
  const hi = levels.length ? Math.max(...levels) + 2 : 100
  return (
    <div className="flex flex-col gap-1.5 text-sm">
      {anchor != null && <Level label="Recent form" v={anchor} lo={lo} hi={hi} title="Weighted average of the last runs, career average, form factor, margins and days since the last run: the model's starting point" />}
      {lead.map((g) => (
        <Step key={g.key} label={g.label} v={g.v} range={g} title={`${g.what}. Typical range ${g.p5.toFixed(1)} to +${g.p95.toFixed(1)}; most extreme ${g.min.toFixed(1)} to +${g.max.toFixed(1)}.`} />
      ))}
      {anchor != null && all && small.length > 0 && <Step label="Other factors" v={small.reduce((a, g) => a + g.v, 0)} title={`Smaller than 0.15 each: ${small.map((g) => g.label).join(', ')}`} />}
      {anchor != null && hiddenCount > 0 && !all && (
        <button type="button" onClick={() => setAll(true)} className="text-left text-xs text-ink-mute underline hover:text-ink">
          Show {hiddenCount} more factor{hiddenCount === 1 ? '' : 's'}
        </button>
      )}
      {runner.baseWpr != null && <Level label="Model base" v={runner.baseWpr} lo={lo} hi={hi} strong />}
      {steps.map((s) => (
        <Step key={s.label} label={s.label} v={s.v} title={s.title} />
      ))}
      <div className="grid grid-cols-[minmax(0,1.3fr)_minmax(0,1.6fr)_44px] items-center gap-2 border-t border-line-soft pt-1.5">
        <span className="font-semibold text-ink">Projected WPR</span>
        <span className="h-2 overflow-hidden rounded-full bg-line-soft">{proj != null && <span className="block h-full rounded-full bg-emerald" style={{ width: `${Math.max(2, Math.min(100, ((proj - lo) / (hi - lo)) * 100))}%` }} />}</span>
        <span className="text-right font-mono font-semibold text-emerald-deep">{fmtWpr(proj)}</span>
      </div>
      {anchor == null && runner.projectionModel === 'light' && <p className="text-xs text-ink-faint">Few prior runs, so the light-history model gives the base directly with no split by factor.</p>}
      {anchor != null && <p className="text-xs text-ink-faint">Shaded band behind each bar: how far that factor typically moves a rating. Hover a row for what it covers.</p>}
    </div>
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
