import type { Runner } from '../types/domain'
import type { EffectiveRunner } from './raceModel'
import { lastRunsRating } from './formRatings'

// Combined rank across three signals: Proj (the table's rating), Nett (TopRate's own forward rating) and L3 (average of the last
// 3 rated runs). Each signal ranks the non-scratched field (1 = best, ties share the best place), the runner's score is the mean of
// the ranks it has, and the final rank orders those means (ties share the best place). A runner needs at least two of the three.
// Basis (15 Oct 2026, 1,139 races 20 Sep to 15 Oct): the combined #1 wins 29.6% against 30.6% for Proj alone, so it is a reading aid
// that shows where the signals agree, not a better winner picker, and the market already prices that agreement.
export interface CombinedRank {
  rank: number
  mean: number
  ranks: [number | null, number | null, number | null] // Proj, Nett, L3
}

const MIN_SIGNALS = 2

function rankDesc(values: Map<string, number>): Map<string, number> {
  const all = [...values.values()]
  const out = new Map<string, number>()
  for (const [id, v] of values) out.set(id, 1 + all.filter((x) => x > v + 1e-9).length)
  return out
}

export function computeCombinedRank(
  runners: Runner[],
  effectiveByRunId: Record<string, EffectiveRunner>,
  scratched: Set<string>,
  raceDate: string | null,
): Map<string, CombinedRank> {
  const proj = new Map<string, number>()
  const nett = new Map<string, number>()
  const l3 = new Map<string, number>()
  for (const r of runners) {
    if (scratched.has(r.runId)) continue
    const p = effectiveByRunId[r.runId]?.effectiveProjectedWpr ?? r.projectedWpr
    if (p != null) proj.set(r.runId, p)
    if (r.nett != null) nett.set(r.runId, r.nett)
    const f = lastRunsRating(r.formHistory, raceDate, 3)
    if (f) l3.set(r.runId, f.avg)
  }
  const rp = rankDesc(proj)
  const rn = rankDesc(nett)
  const rl = rankDesc(l3)
  const means = new Map<string, { mean: number; ranks: CombinedRank['ranks'] }>()
  for (const r of runners) {
    if (scratched.has(r.runId)) continue
    const ranks: CombinedRank['ranks'] = [rp.get(r.runId) ?? null, rn.get(r.runId) ?? null, rl.get(r.runId) ?? null]
    const have = ranks.filter((x): x is number => x != null)
    if (have.length < MIN_SIGNALS) continue
    means.set(r.runId, { mean: have.reduce((s, x) => s + x, 0) / have.length, ranks })
  }
  const all = [...means.values()].map((m) => m.mean)
  const out = new Map<string, CombinedRank>()
  for (const [id, m] of means) out.set(id, { rank: 1 + all.filter((x) => x < m.mean - 1e-9).length, mean: m.mean, ranks: m.ranks })
  return out
}
