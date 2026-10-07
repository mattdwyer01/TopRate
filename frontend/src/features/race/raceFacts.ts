import type { Race, Runner } from '../../types/domain'
import type { EffectiveRunner } from '../../lib/raceModel'

// Small pure helpers shared by the race page's header, glance panel, table and cards.

export type GoingTone = 'dry' | 'soft' | 'heavy' | 'other'

export function goingTone(going: string | null | undefined): GoingTone {
  const m = /(\d+)/.exec(going ?? '')
  if (!m) return 'other'
  const n = Number(m[1])
  return n <= 4 ? 'dry' : n <= 7 ? 'soft' : 'heavy'
}

// The going this race had changed from, taken from the nearest earlier race at the same meeting that was on different going.
export function goingChange(race: Race, meeting: Race[]): { from: string; race: number } | null {
  const earlier = meeting.filter((r) => r.raceNumber < race.raceNumber).sort((a, b) => b.raceNumber - a.raceNumber)
  const prev = earlier.find((r) => r.going && race.going && r.going !== race.going)
  return prev ? { from: prev.going, race: prev.raceNumber } : null
}

export function fmtPrize(v: number | null): string | null {
  if (v == null || v <= 0) return null
  if (v >= 1_000_000) return `$${(v / 1_000_000).toFixed(v % 1_000_000 === 0 ? 0 : 1)}M`
  if (v >= 1000) return `$${Math.round(v / 1000)}k`
  return `$${v}`
}

export interface Ranked {
  runner: Runner
  proj: number
  gap: number
  eff: EffectiveRunner | undefined
  inner: boolean
  outer: boolean // inside the outer line but outside the inner one
}

// Runners still in the race with a projection, best first, with their gap to the top and which line they fall inside.
export function rankField(
  runners: Runner[],
  effective: Record<string, EffectiveRunner>,
  scratched: Set<string>,
  innerGap: number,
  outerGap: number,
): Ranked[] {
  type Row = { runner: Runner; proj: number; eff: EffectiveRunner | undefined }
  const rows: Row[] = []
  for (const r of runners) {
    if (scratched.has(r.runId)) continue
    const eff: EffectiveRunner | undefined = effective[r.runId]
    const proj = eff?.effectiveProjectedWpr ?? r.projectedWpr
    if (proj != null) rows.push({ runner: r, proj, eff })
  }
  rows.sort((a, b) => b.proj - a.proj)
  const top = rows.length ? rows[0].proj : 0
  return rows.map((x) => {
    const gap = top - x.proj
    return { ...x, gap, inner: gap <= innerGap, outer: gap > innerGap && gap <= outerGap }
  })
}

// Share of each runner's typical error that counts as independent between runners. The projection error is mostly shared across a race
// (going, pace, a weak or strong field), so simulating the full error overshoots. 0.6 gives zero bias against 2,821 resulted races
// (1 Jul to 6 Oct 2026, pre-race projections): the expected figure was within 3.9 WPR (one standard deviation) of the winner's actual rating.
const WIN_RATING_ERROR_SHARE = 0.6

// The rating a winner is expected to run in this race: the expected best performance across the field, with each runner's rating drawn
// around its projection by its typical error. Always above the top projection, and more so in a big or uncertain field.
export function expectedWinningWpr(field: { proj: number; sd: number }[]): number | null {
  if (field.length < 2) return null
  const sds = field.map((f) => Math.max(0.5, f.sd * WIN_RATING_ERROR_SHARE))
  const lo = Math.min(...field.map((f, i) => f.proj - 5 * sds[i]))
  const hi = Math.max(...field.map((f, i) => f.proj + 5 * sds[i]))
  const n = 240
  const dx = (hi - lo) / n
  const phi = (z: number) => {
    // Abramowitz and Stegun 7.1.26 normal CDF
    const x = Math.abs(z) / Math.SQRT2
    const t = 1 / (1 + 0.3275911 * x)
    const y = 1 - (((((1.061405429 * t - 1.453152027) * t) + 1.421413741) * t - 0.284496736) * t + 0.254829592) * t * Math.exp(-x * x)
    return z >= 0 ? 0.5 * (1 + y) : 0.5 * (1 - y)
  }
  // E[max] = lo + integral of (1 - P(max <= x)) from lo to hi
  let area = 0
  for (let i = 0; i < n; i++) {
    const x = lo + (i + 0.5) * dx
    let cdf = 1
    for (let j = 0; j < field.length; j++) cdf *= phi((x - field[j].proj) / sds[j])
    area += (1 - cdf) * dx
  }
  return lo + area
}

// Typical error of a projection (WPR points). Uses the payload's own value; when it is missing, the model's documented out-of-sample error
// for its kind of runner (main model by projection level, light model by number of prior runs).
export function typicalSd(runner: Runner, proj: number | null): number | null {
  if (runner.projectionSd != null) return runner.projectionSd
  if (proj == null) return null
  if (runner.projectionModel === 'light') return ({ 0: 11.8, 1: 10.5, 2: 10.0 } as Record<number, number>)[Math.min(2, runner.formHistory.length)] ?? 11
  return proj >= 70 ? 7.96 : proj >= 60 ? 9.43 : 11.9
}
