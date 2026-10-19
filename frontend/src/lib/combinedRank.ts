import type { Runner } from '../types/domain'
import type { EffectiveRunner } from './raceModel'
import { lastRunsRating } from './formRatings'

// Combined rank across four signals, in column order: Spd (pre-race speed rating), Nett (TopRate's own forward rating), L3 (average of the last
// 3 rated runs) and Proj (the table's rating). Each signal ranks the non-scratched field (1 = best, ties share the best place), the runner's score
// is the mean of the ranks it has, and the final rank orders those means (ties share the best place). A runner needs at least two of the four.
// Basis: 15 Oct 2026, 1,139 races: the combined rank of Proj, Nett and L3 picked the winner about as often as Proj alone and the market already
// prices the agreement, so it is a reading aid. 16 Oct 2026 (688 races): when speed also agrees, all four rating the same runner #1 happened in
// 8% of races and that runner won 43.9% (market 41.6%), about break-even at the starting price; speed on its own is the weakest of the four.
export interface CombinedRank {
  rank: number
  tied: boolean // another runner shares this rank
  mean: number
  ranks: [number | null, number | null, number | null, number | null] // Spd, Nett, L3, Proj
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
  const speed = new Map<string, number>()
  const nett = new Map<string, number>()
  const l3 = new Map<string, number>()
  const proj = new Map<string, number>()
  for (const r of runners) {
    if (scratched.has(r.runId)) continue
    if (r.speedRating != null) speed.set(r.runId, r.speedRating)
    if (r.nett != null) nett.set(r.runId, r.nett)
    const f = lastRunsRating(r.formHistory, raceDate, 3)
    if (f) l3.set(r.runId, f.avg)
    const p = effectiveByRunId[r.runId]?.effectiveProjectedWpr ?? r.projectedWpr
    if (p != null) proj.set(r.runId, p)
  }
  const rs = rankDesc(speed)
  const rn = rankDesc(nett)
  const rl = rankDesc(l3)
  const rp = rankDesc(proj)
  const means = new Map<string, { mean: number; ranks: CombinedRank['ranks'] }>()
  for (const r of runners) {
    if (scratched.has(r.runId)) continue
    const ranks: CombinedRank['ranks'] = [rs.get(r.runId) ?? null, rn.get(r.runId) ?? null, rl.get(r.runId) ?? null, rp.get(r.runId) ?? null]
    const have = ranks.filter((x): x is number => x != null)
    if (have.length < MIN_SIGNALS) continue
    means.set(r.runId, { mean: have.reduce((s, x) => s + x, 0) / have.length, ranks })
  }
  const all = [...means.values()].map((m) => m.mean)
  const out = new Map<string, CombinedRank>()
  for (const [id, m] of means) {
    out.set(id, { rank: 1 + all.filter((x) => x < m.mean - 1e-9).length, tied: all.filter((x) => Math.abs(x - m.mean) < 1e-9).length > 1, mean: m.mean, ranks: m.ranks })
  }
  return out
}
