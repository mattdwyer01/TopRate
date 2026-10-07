import { useEffect, useMemo, useRef, useState } from 'react'
import type { Race, Runner } from '../../types/domain'
import { projectedAtActualScale } from '../../lib/atw'
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
  projAtw: number | null
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

export function HorseHero({ runner, race, proj, scratched, rank, fieldSize, fieldTop, fieldLow, fair, market, fixedMove, hasOverride, spellLabel, daysSince, projAtw }: HeroProps) {
  const sd = typicalSd(runner, proj)
  // The whole hero is at today's weight (ATW), the scale of the form table. The gauge shifts the field by this horse's own offset, so gaps are unchanged.
  const shift = projAtw != null && proj != null ? projAtw - proj : 0
  const last3 = runner.formHistory.filter((e) => e.wpr != null && e.date && !e.isVoid).sort((a, c) => c.date.localeCompare(a.date)).slice(0, 3)
  const recentAvg = projAtw != null && last3.length >= 2 ? last3.reduce((a, e) => a + (e.wpr as number), 0) / last3.length : null
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
            <div className="font-mono text-3xl font-bold leading-none text-emerald-deep">{fmtWpr(projAtw ?? proj)}</div>
          )}
          {!scratched && (projAtw ?? proj) != null && (
            <p className="mt-0.5 text-[11px] text-ink-mute" title="Every rating on this page is at the weight carried today (ATW), the scale of the Recent runs table, the chart and the waterfall. Ranking, the gap to the top and the field range use the same rating shifted together, so they are unchanged.">
              {projAtw != null ? <>at {runner.weightCarried != null ? `${runner.weightCarried}kg` : "today's weight"}</> : null}
              {recentAvg != null && <>{projAtw != null ? ' \u00b7 ' : ''}last {last3.length} runs avg {fmtWpr(recentAvg)} ({fmtAdj((projAtw ?? proj!) - recentAvg)})</>}
            </p>
          )}
          <p className="mt-1 text-xs text-ink-soft">
            {verdict}
            {sd != null && !scratched && <> Error &plusmn;{sd.toFixed(0)}.</>}
            {reasons.length > 0 && !scratched && <> {reasons[0][0].toUpperCase() + reasons[0].slice(1)}{reasons.length > 1 ? `, ${reasons.slice(1).join(', ')}` : ''}.</>}
          </p>
        </div>
        {proj != null && !scratched && (
          <div className="order-last col-span-2 min-w-0 lg:order-none lg:col-span-1" title="Shaded bar is the likely range (the middle half of outcomes). Pale track is the whole field.">
            <RangeGauge proj={proj + shift} sd={sd} top={fieldTop != null ? fieldTop + shift : null} low={fieldLow != null ? fieldLow + shift : null} />
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
// A real waterfall on one WPR axis: the first bar is the recent-form anchor, every factor then floats from where the one before it ended
// (green up, red down, a thin line carries the running total across), the model base and the projection are full bars. The axis does not
// start at zero (a bar from 0 to 87 would hide a +0.8), so it is cut near the lowest total and the cut is stated underneath.
type WfRow = { key: string; label: string; kind: 'total' | 'step'; from: number; to: number; title?: string; strong?: boolean }

function WaterfallRow({ row, lo, hi, last }: { row: WfRow; lo: number; hi: number; last: boolean }) {
  const pos = (v: number) => Math.max(0, Math.min(100, ((v - lo) / (hi - lo)) * 100))
  const total = row.kind === 'total'
  const a = total ? 0 : Math.min(pos(row.from), pos(row.to))
  const b = total ? pos(row.to) : Math.max(pos(row.from), pos(row.to))
  const delta = row.to - row.from
  const tone = total ? (row.strong ? 'bg-slate' : 'bg-line') : delta >= 0 ? 'bg-emerald' : 'bg-rose'
  return (
    <div title={row.title} className="grid h-[22px] grid-cols-[minmax(0,9.5rem)_minmax(0,1fr)_3rem] items-center gap-2 sm:grid-cols-[minmax(0,11rem)_minmax(0,1fr)_3.25rem]">
      <span className={`truncate ${total && row.strong ? 'font-semibold text-ink' : 'text-ink-mute'}`}>{row.label}</span>
      <span className="relative block h-full">
        <span className={`absolute top-[4px] h-[14px] rounded-[3px] ${tone}`} style={{ left: `${a}%`, width: `${Math.max(0.8, b - a)}%` }} />
        {!last && <span className="absolute top-[18px] h-[10px] w-px bg-ink-faint/60" style={{ left: `${pos(row.to)}%` }} />}
      </span>
      <span className={`text-right font-mono ${total ? (row.strong ? 'font-semibold text-ink' : 'text-ink-mute') : adjClass(delta)}`}>{total ? fmtWpr(row.to) : fmtAdj(delta)}</span>
    </div>
  )
}

// From the recent-form anchor to the projection. The main model starts from a weighted average of recent form and corrects it for the
// factors in GROUPS. The biggest few are listed, the rest are folded into one step so the bars always add up. Runners from before the
// breakdown was logged, and light-history runners, get base, suitability and weight only.
export function ProjectionWaterfall({ runner, proj, deltaValue, atwOffset, weightKg }: { runner: Runner; proj: number | null; deltaValue: number | null; atwOffset: number | null; weightKg: number | null }) {
  const [all, setAll] = useState(false)
  const b = runner.adjustmentBreakdown
  const anchor = b?.g_anchor
  // One list of steps from the recent-form anchor to the projection: the model's factor groups plus the suitability and weight steps that
  // come after its base. Biggest first; the smallest fold into one "other" step so the bars always add up.
  const steps: { key: string; label: string; v: number; title: string }[] =
    anchor != null
      ? [
          ...GROUPS.map((g) => ({ key: g.key, label: g.label, v: b?.['g_' + g.key] ?? 0, title: `${g.what}. Typical range ${g.p5.toFixed(1)} to +${g.p95.toFixed(1)}; most extreme ${g.min.toFixed(1)} to +${g.max.toFixed(1)}.` })),
          ...(b?.suitability != null ? [{ key: 'suit', label: 'Suitability', v: b.suitability, title: 'Comment history, day-of bias, finishing profile and jockey/trainer tendencies' }] : []),
          ...(b?.weight != null ? [{ key: 'wt', label: 'Weight carried', v: b.weight, title: 'About 0.4 WPR per kg above the field average' }] : []),
        ].sort((x, y) => Math.abs(y.v) - Math.abs(x.v))
      : []
  const lead = all ? steps.filter((g) => Math.abs(g.v) >= 0.15) : steps.slice(0, 4)
  const rest = steps.filter((g) => !lead.includes(g))
  const restSum = rest.reduce((a, g) => a + g.v, 0)

  // Everything is drawn at today's weight (ATW), the scale of the Recent runs table: the starting bar carries the horse's own offset, the steps are
  // differences and need no conversion, and the total is the projection on the same scale.
  const off = atwOffset ?? 0
  const rows: WfRow[] = []
  let run = 0
  if (anchor != null) {
    rows.push({ key: 'anchor', label: off !== 0 ? `Recent form at ${weightKg != null ? weightKg + 'kg' : 'today\'s weight'}` : 'Recent form', kind: 'total', from: 0, to: anchor + off, title: "Weighted average of the last runs, career average, form factor, margins and days since the last run: the model's starting point" + (off !== 0 ? ", on the same scale as the Recent runs table (every run rated at today's weight)" : '') })
    run = anchor + off
    for (const g of lead) {
      rows.push({ key: g.key, label: g.label, kind: 'step', from: run, to: run + g.v, title: g.title })
      run += g.v
    }
    if (rest.length > 0) {
      rows.push({ key: 'rest', label: `${rest.length} other factor${rest.length === 1 ? '' : 's'}`, kind: 'step', from: run, to: run + restSum, title: rest.map((g) => `${g.label} ${fmtAdj(g.v)}`).join(', ') })
      run += restSum
    }
  } else {
    // Older logged runs and light-history runners have no split by factor, so they start from the model's own base and take the same
    // suitability and weight steps.
    // A light-history runner's last one or two ratings are shown as plain reference bars (the light model does not build its base from them).
    if (runner.projectionModel === 'light') {
      const last = runner.formHistory.filter((e) => e.wpr != null && e.date && !e.isVoid).sort((a, c) => c.date.localeCompare(a.date)).slice(0, 2)
      last.forEach((e, i) => rows.push({ key: 'ref' + i, label: i === 0 ? 'Last run' : 'Run before', kind: 'total', from: 0, to: e.wpr as number, title: `${e.date.slice(0, 10)}: for reference only. The light-history model reads the runner's price and a few other signals rather than starting from recent form.` }))
    }
    if (runner.baseWpr != null) {
      rows.push({ key: 'base', label: 'Model base', kind: 'total', from: 0, to: runner.baseWpr + off, title: 'The model\'s projection before the suitability and weight steps (no split by factor for this runner)' })
      run = runner.baseWpr + off
    }
    const tail = b && (b.suitability != null || b.weight != null)
      ? [
          ...(b.suitability != null ? [{ key: 'suit', label: 'Suitability', v: b.suitability, title: 'Comment history, day-of bias, finishing profile and jockey/trainer tendencies' }] : []),
          ...(b.weight != null ? [{ key: 'wt', label: 'Weight carried', v: b.weight, title: 'About 0.4 WPR per kg above the field average' }] : []),
        ]
      : runner.wprAdjustment != null
        ? [{ key: 'adj', label: 'Adjustments', v: runner.wprAdjustment, title: undefined as string | undefined }]
        : []
    for (const e of tail) {
      rows.push({ key: e.key, label: e.label, kind: 'step', from: run, to: run + e.v, title: e.title })
      run += e.v
    }
  }
  if (deltaValue != null && deltaValue !== 0) {
    rows.push({ key: 'you', label: 'Your adjustment', kind: 'step', from: run, to: run + deltaValue })
    run += deltaValue
  }
  if (proj != null) rows.push({ key: 'proj', label: 'Projected WPR', kind: 'total', from: 0, to: proj + (atwOffset ?? 0), strong: true })

  const levels = rows.filter((r) => r.kind === 'step').flatMap((r) => [r.from, r.to]).concat(rows.filter((r) => r.kind === 'total').map((r) => r.to))
  const min = levels.length ? Math.min(...levels) : 0
  const max = levels.length ? Math.max(...levels) : 100
  const span = Math.max(3, max - min)
  const lo = Math.floor(min - span * 0.6)
  const hi = Math.ceil(max + span * 0.12)
  return (
    <div className="flex flex-col text-sm">
      {rows.map((r, i) => (
        <WaterfallRow key={r.key} row={r} lo={lo} hi={hi} last={i === rows.length - 1} />
      ))}
      {anchor != null && !all && rest.some((g) => Math.abs(g.v) >= 0.15) && (
        <button type="button" onClick={() => setAll(true)} className="mt-1 w-fit text-left text-xs text-ink-mute underline hover:text-ink">
          Show each of the {rest.length} other factors
        </button>
      )}
      {anchor != null && all && (
        <button type="button" onClick={() => setAll(false)} className="mt-1 w-fit text-left text-xs text-ink-mute underline hover:text-ink">
          Show fewer
        </button>
      )}
      {anchor == null && runner.projectionModel === 'light' && <p className="mt-1 text-xs text-ink-faint">Few prior runs, so the light-history model gives the base directly with no split by factor. Last-run bars are for reference, not a step.</p>}
      <p className="mt-1.5 text-xs text-ink-faint">
        Each bar starts where the one above ended. {off !== 0 ? `Rated at ${weightKg != null ? weightKg + 'kg' : "today's weight"}, the same scale as the Recent runs table. ` : ''}Scale starts at {lo}. Hover a row for what it covers.
      </p>
    </div>
  )
}

/* ----------------------------------------------------------- timeline */

// Every recent run as a dot: height is WPR, spacing is real time (so spells show as gaps), dot size and colour show how it finished.
// The projection for today sits at the right with its likely range, and the dotted line is the minimum winning standard for
// this race: the expected winning rating (raceFacts.expectedWinningWpr) less MIN_WINNING_STANDARD_OFFSET, so a horse's runs read against what it takes to win. Drawn at the container's own width so
// the text stays crisp and the chart fills the card.
export function RunTimeline({ runner, proj: projRaw, raceDate, expectedWin: winRaw, atwOffset }: { runner: Runner; proj: number | null; raceDate: string; expectedWin: number | null; atwOffset: number | null }) {
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
  const sd = typicalSd(runner, projRaw)
  // The runs are ATW (each rating adjusted to the weight carried today), the projection and winning line are plain WPR, so both are shifted by
  // the horse's own ATW offset to sit on the same scale as the runs. No offset known (older payload, too little history): drawn as before.
  const off = atwOffset ?? 0
  const proj = projRaw != null ? projRaw + off : null
  const expectedWin = winRaw != null ? winRaw + off : null
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
  const vals = [...dots.map((d) => d.e.wpr as number), ...(proj != null ? [proj - (sd ?? 0) * HALF, proj + (sd ?? 0) * HALF] : []), ...(expectedWin != null ? [expectedWin] : [])]
  const lo = Math.floor((Math.min(...vals) - 2) / 5) * 5
  const hi = Math.ceil((Math.max(...vals) + 2) / 5) * 5
  const X = (ms: number) => padL + 8 + ((ms - t0) / Math.max(1, t1 - t0)) * (W - padL - padR - 8)
  const Y = (v: number) => padT + (1 - (v - lo) / (hi - lo)) * (H - padT - padB)
  const ticks: number[] = []
  for (let v = lo; v <= hi; v += 5) ticks.push(v)
  const path = dots.map((d, i) => `${i ? 'L' : 'M'}${X(t(d.e.date)).toFixed(1)},${Y(d.e.wpr as number).toFixed(1)}`).join(' ')
  const px = X(t(raceDate))
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
        {expectedWin != null && (
          <g>
            <title>{`Minimum winning standard ${fmtWpr(expectedWin)}: about 19 in 20 winners have run this rating or better. It sits well below the typical winning rating (what winners have actually run in past races, given this field's top, runner-up and average projection and its size), so almost every winner clears it.`}</title>
            <line x1={padL} x2={W - padR + 14} y1={Y(expectedWin)} y2={Y(expectedWin)} stroke="var(--color-amber)" strokeWidth={1.5} strokeDasharray="2 4" strokeLinecap="round" />
            <rect x={padL + 2} y={Y(expectedWin) - 19} width={150} height={16} rx={8} fill="var(--color-amber-bg)" stroke="var(--color-amber-line)" />
            <text x={padL + 77} y={Y(expectedWin) - 7.5} textAnchor="middle" fontSize={10.5} fontWeight={700} fill="var(--color-amber)">
              {`min winning rating ~${Math.round(expectedWin)}`}
            </text>
          </g>
        )}
        <path d={path} fill="none" stroke="var(--color-slate)" strokeWidth={1.5} strokeOpacity={0.45} strokeLinejoin="round" />
        {proj != null && (
          <>
            {sd != null && <rect x={px - 7} y={Y(proj + sd * HALF)} width={14} height={Math.max(3, Y(proj - sd * HALF) - Y(proj + sd * HALF))} rx={4} fill="var(--color-emerald-tint)" stroke="var(--color-emerald-line)" />}
            <line x1={X(t(dots[dots.length - 1].e.date))} y1={Y(dots[dots.length - 1].e.wpr as number)} x2={px} y2={Y(proj)} stroke="var(--color-emerald-deep)" strokeDasharray="4 3" strokeWidth={1.5} />
            <circle cx={px} cy={Y(proj)} r={6} fill="var(--color-emerald-deep)" />
            <text x={px + 11} y={Y(proj) + 4} fontSize={12} fontWeight={700} fill="var(--color-emerald-deep)">
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
      <span>
        <span className="mr-1 inline-block w-4 border-t-2 border-dotted border-amber align-middle" />
        minimum winning standard (about 19 in 20 winners reach it)
      </span>
      <span className="hidden sm:inline">Height is WPR; gaps between dots are real time (spells).</span>
      {shifted && (
        <span className="basis-full">
          Ratings are at today&apos;s weight{weightKg != null ? ` (${weightKg}kg)`: ''}, the same as the Recent runs table. The projection dot and winning line are on that scale too.
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
  const proj = projectedAtActualScale(runner)
  const actual = runner.actualWpr
  const fin = runner.finishPosition
  const sd = runner.projectionSd
  const miss = actual != null && proj != null ? actual - proj : null
  const big = miss != null && sd != null && Math.abs(miss) > sd
  if (fin == null && actual == null && !runner.resultKnown) {
    return <p className="text-sm text-ink-mute">The result and the actual rating show here after the race. Projected rating to beat: <span className="font-mono font-semibold text-ink">{fmtWpr(proj)}</span>.</p>
  }
  return (
    <div>
      <div className="grid grid-cols-3 gap-2">
        <Tile label="Projected (ATW)">
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
