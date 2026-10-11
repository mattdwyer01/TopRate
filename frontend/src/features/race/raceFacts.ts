import { CORE_GAP_FROM_TOP } from '../../lib/raceModel'
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
  core: boolean // inside the core line (a subset of inner)
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
  coreGap = CORE_GAP_FROM_TOP,
  // 'projection' ranks on the WPR projection even where the race's rating is the bet-signal rating: for the things that explain the projection (the track-bias
  // note, the typical winning rating), which were fitted on it.
  scale: 'rating' | 'projection' = 'rating',
): Ranked[] {
  type Row = { runner: Runner; proj: number; eff: EffectiveRunner | undefined }
  const rows: Row[] = []
  for (const r of runners) {
    if (scratched.has(r.runId)) continue
    const eff: EffectiveRunner | undefined = effective[r.runId]
    const proj = scale === 'projection' ? (eff?.projectionWpr ?? r.projectedWpr) : (eff?.effectiveProjectedWpr ?? r.projectedWpr)
    if (proj != null) rows.push({ runner: r, proj, eff })
  }
  rows.sort((a, b) => b.proj - a.proj)
  const top = rows.length ? rows[0].proj : 0
  return rows.map((x) => {
    const gap = top - x.proj
    return { ...x, gap, core: gap <= coreGap, inner: gap <= innerGap, outer: gap > innerGap && gap <= outerGap }
  })
}

// The rating a winner typically runs in this race, fitted on what winners actually ran: 2,823 resulted races (8 Aug to 6 Oct 2026) with their
// pre-race projections (weight term in), regressing the winner's actual WPR on the field's top projection, runner-up projection, average
// projection and field size. A winner usually runs above the top projection (about +4 on average) because the winner is whoever has the
// best day, and a stronger field raises the bar. Typical error of the fit is about 3.8 WPR; fitted on either half of the window and scored
// on the other, the bias was within 1 WPR.
const WIN_FIT = { intercept: 16.5838, top: 0.2874, second: 0.3066, mean: 0.2514, size: 0.186 }

// The line shown on the horse timeline is a minimum winning standard, not the typical figure: expectedWinningWpr less this offset. On 2,821
// resulted races (8 Aug to 6 Oct 2026, pre-race projections) a 6 WPR offset puts the line at a rating 95% of winners reached or beat; the
// winner's own projection was at or above it 38% of the time, with about 1.5 runners a race projected above it. Raise it to lower the line.
export const MIN_WINNING_STANDARD_OFFSET = 6

export function expectedWinningWpr(projs: number[]): number | null {
  if (projs.length < 2) return null
  const sorted = [...projs].sort((a, b) => b - a)
  const mean = projs.reduce((a, v) => a + v, 0) / projs.length
  return WIN_FIT.intercept + WIN_FIT.top * sorted[0] + WIN_FIT.second * sorted[1] + WIN_FIT.mean * mean + WIN_FIT.size * projs.length
}

// Typical error of a projection (WPR points). Uses the payload's own value; when it is missing, the model's documented out-of-sample error
// for its kind of runner (main model by projection level, light model by number of prior runs).
export function typicalSd(runner: Runner, proj: number | null): number | null {
  if (runner.projectionSd != null) return runner.projectionSd
  if (proj == null) return null
  if (runner.projectionModel === 'light') return ({ 0: 11.8, 1: 10.5, 2: 10.0 } as Record<number, number>)[Math.min(2, runner.formHistory.length)] ?? 11
  return proj >= 70 ? 7.96 : proj >= 60 ? 9.43 : 11.9
}
