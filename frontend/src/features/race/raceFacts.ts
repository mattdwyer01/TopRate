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

export const GOING_TONE_CLASS: Record<GoingTone, string> = {
  dry: 'border-emerald-line bg-emerald-bg text-emerald-deep',
  soft: 'border-amber-line bg-amber-bg text-amber',
  heavy: 'border-rose-line bg-rose-bg text-rose',
  other: 'border-line bg-bg text-ink-mute',
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
