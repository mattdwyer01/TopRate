import type { Race, Runner } from '../../types/domain'
import { computeCareerStats } from '../../lib/careerStats'
import { ADJUSTMENT_LABELS, SAMPLE_SIZE_TERMS, LOW_SAMPLE_THRESHOLD } from '../../lib/adjustmentLabels'
import { Sparkline } from '../../components/Sparkline'

interface CareerStatsProps {
  runner: Runner
  race: Race
}

const MIN_ADJ_SHOWN = 0.05

function fmt(v: number | null): string {
  return v == null ? '—' : v.toFixed(1)
}

function fmtSigned(v: number | null): string {
  if (v == null) return '—'
  const f = v.toFixed(1)
  return v > 0 ? `+${f}` : f
}

// Same threshold and reasoning as ComparisonGrid's MIN_RUNS_TO_COMPARE -
// below this many runs, "vs Career" is 1-2 data points dressed up as a
// confident read. Below the threshold the figure still shows, just without
// the colour that implies a reliable signal.
const MIN_RUNS_TO_COLOR = 3

function vsCareerAvgClass(v: number | null, runs: number): string {
  if (v == null || runs < MIN_RUNS_TO_COLOR) return 'text-ink-mute'
  if (v >= 1) return 'text-emerald-deep font-medium'
  if (v <= -1) return 'text-rose font-medium'
  return 'text-ink-mute'
}

// Career/condition WPR summary shown up top in the runner detail - peak,
// average and average-vs-career-average across career plus a handful of
// conditions relevant to today's race (including first/second-up history
// when today is itself a first/second-up run). Reference only - "how has
// this horse actually run in X" - deliberately carries no adjustment
// values (see AdjustmentBreakdown below for those). Splitting these two
// questions into two panels (Sep 2026) replaced an earlier design that
// folded the model's applied adjustment into whichever row happened to
// share a condition with an ADJ_TERM (distance/going/first-up/second-up) -
// found to actively mislead: this table's own "First-up" average is
// computed from the raw recorded WPR of every matching run, while the
// model's own first-up ADJ_TERM discounts a run flagged void (vet/
// checked/eased/etc, see wpr_void.py) from that same average - a horse
// whose one bad first-up run was a checked run showed a strongly negative
// "vs Career" here right next to a positive adjustment, looking like a
// bug rather than two different (both correct) questions. Sits beside
// ComparisonGrid (see RunnerDetailModal), which asks a narrower question
// (does today's specific pace/settle suit it).
function CareerConditionTable({ runner, race }: CareerStatsProps) {
  // Rows with zero matching runs (e.g. "This prep" for a first-up horse)
  // show nothing but dashes - the em-dash IS the information, so drop the
  // row rather than spend a full line saying "no data" (a first-up horse's
  // empty prep is already obvious from the recent-runs table's spell marker).
  const rows = computeCareerStats(runner, race).filter((row) => row.runs > 0)

  return (
    <div>
      <div className="mb-1.5 text-xs font-semibold text-ink">
        Career &amp; condition <span className="font-normal text-ink-faint">&middot; reference</span>
      </div>
      <table className="w-full min-w-[220px] text-xs">
        <thead>
          <tr className="border-b border-line-soft text-ink-faint">
            <th className="pb-1 text-left font-normal" />
            <th className="pb-1 pl-2 text-right font-normal">Peak</th>
            <th className="pb-1 pl-2 text-right font-normal">Avg</th>
            <th className="pb-1 pl-2 text-right font-normal">vs Career</th>
            <th className="pb-1 pl-2 text-right font-normal">Trend</th>
          </tr>
        </thead>
        <tbody className="[&_td]:py-0.5 [&_td]:leading-5">
          {rows.map((row) => {
            const isCareer = row.label === 'Career'
            return (
              <tr
                key={row.label}
                className={`border-b border-line-soft/60 last:border-0 ${
                  isCareer ? 'font-medium text-ink' : 'text-ink'
                }`}
              >
                <td className="whitespace-nowrap">
                  {row.label} <span className="font-normal text-ink-faint">&middot; {row.runs}</span>
                </td>
                <td className="pl-2 text-right font-mono">{fmt(row.peak)}</td>
                <td className="pl-2 text-right font-mono">{fmt(row.avg)}</td>
                <td className={`pl-2 text-right font-mono ${vsCareerAvgClass(row.vsCareerAvg, row.runs)}`}>
                  {fmtSigned(row.vsCareerAvg)}
                </td>
                <td className="py-0.5 pl-2 text-right">
                  <Sparkline values={row.trend} />
                </td>
              </tr>
            )
          })}
        </tbody>
      </table>
    </div>
  )
}

// What's actually adjusting the rating - every ADJ_TERM the model applied
// (base + sum(these) == effective WPR, via runner.wprAdjustment as the
// authoritative total - not a re-sum of the rows below, which are each
// independently rounded to 1dp for display and would drift from the true
// total by a few hundredths). A bar makes each term's size and direction
// scannable at a glance, scaled to the LARGEST adjustment this runner
// actually has (never a fixed scale) so a runner whose biggest driver is
// +0.3 doesn't look as flat as one whose biggest is +6.
//
// trainer_merit/jockey_merit get a confidence dot when the strike rate
// behind them is built on a thin recent sample (see adjustmentLabels.ts's
// SAMPLE_SIZE_TERMS/LOW_SAMPLE_THRESHOLD) - found via a live example
// (Sep 2026): a 50% jockey strike rate off a handful of recent rides
// produced as large an adjustment as a genuinely proven one, because the
// model only ever sees the percentage, never the count it's based on.
function AdjustmentBreakdown({ runner }: { runner: Runner }) {
  const breakdown = runner.adjustmentBreakdown
  if (!breakdown || runner.wprAdjustment == null) return null

  const rows = Object.entries(breakdown).filter(
    ([key, v]) => key !== 'baseline' && Math.abs(v) >= MIN_ADJ_SHOWN,
  )
  if (!rows.length) return null

  const maxAbs = Math.max(1, ...rows.map(([, v]) => Math.abs(v)))

  return (
    <div>
      <div className="mb-1.5 text-xs font-semibold text-ink">What&apos;s adjusting the rating</div>
      <div className="space-y-0.5">
        {rows.map(([key, v]) => {
          const label = ADJUSTMENT_LABELS[key] ?? key
          const isLowSample =
            SAMPLE_SIZE_TERMS.has(key) &&
            (key === 'jockey_merit' ? runner.jockeyStarts90d : runner.trainerStarts365d) != null &&
            (key === 'jockey_merit' ? runner.jockeyStarts90d! : runner.trainerStarts365d!) < LOW_SAMPLE_THRESHOLD
          const n = key === 'jockey_merit' ? runner.jockeyStarts90d : runner.trainerStarts365d
          // Track is centred at 50%; fill extends toward the value's sign,
          // capped at 48% of the track so it can never visually collide
          // with the number sitting to its right.
          const barPct = Math.min(48, (Math.abs(v) / maxAbs) * 48)
          return (
            <div key={key} className="flex items-center gap-2 border-b border-line-soft/60 py-1 last:border-0">
              <div className="min-w-0 flex-1 text-xs text-ink">
                <span className="inline-flex items-center gap-1.5">
                  {isLowSample && (
                    <span
                      className="inline-block h-1.5 w-1.5 flex-none rounded-full bg-amber"
                      title={`Thin sample${n != null ? ` - ${n} recent rides/runs` : ''}`}
                    />
                  )}
                  {label}
                </span>
                {isLowSample && (
                  <div className="text-[11px] text-amber">
                    {n != null ? `${n} recent rides/runs - thin sample` : 'thin sample'}
                  </div>
                )}
              </div>
              <div className="relative h-1.5 w-16 flex-none rounded-full bg-line-soft">
                <div
                  className={`absolute top-0 bottom-0 rounded-full ${
                    v > 0 ? 'left-1/2' : 'right-1/2'
                  } ${isLowSample ? 'bg-amber' : v > 0 ? 'bg-emerald-deep' : 'bg-rose'}`}
                  style={{ width: `${barPct}%` }}
                />
              </div>
              <div
                className={`w-11 flex-none text-right font-mono text-xs font-semibold ${
                  isLowSample ? 'text-amber' : v > 0 ? 'text-emerald-deep' : 'text-rose'
                }`}
              >
                {fmtSigned(v)}
              </div>
            </div>
          )
        })}
        <div className="flex items-center gap-2 border-t border-line-soft pt-1.5 font-semibold text-ink">
          <div className="flex-1 text-xs">Total adjustment</div>
          <div className="w-16 flex-none" />
          <div className="w-11 flex-none text-right font-mono text-xs">{fmtSigned(runner.wprAdjustment)}</div>
        </div>
      </div>
    </div>
  )
}

export function CareerStats({ runner, race }: CareerStatsProps) {
  if (!runner.formHistory.length) return null
  return (
    <div className="overflow-x-auto rounded-lg border border-line bg-panel p-2.5">
      <div className="flex flex-col gap-4">
        <CareerConditionTable runner={runner} race={race} />
        <AdjustmentBreakdown runner={runner} />
      </div>
    </div>
  )
}
