import type { Runner } from '../types/domain'
import type { EffectiveRunner } from './raceModel'

// Combined rank. Score = weighted mean of within-race z-scores of Proj (0.50), Nett (0.30) and Spd (0.20; 22 Oct 2026, owner's call after research/rank_refit_ctx.py, was 0.65 / 0.25 / 0.10), over the signals the runner has; the
// rank orders the scores (ties share the best place). A runner needs at least two of the three. L3 was removed from the dashboard (20 Oct 2026): Proj is built from the same runs and a fitted blend gave L3 a weight of -0.01 (19 Oct 2026, `research/rank_weights.py`, 4,107 races,
// cross-fitted by date: fitted blend top pick wins 28.1% / log-lik -1.9030 vs 27.0% / -1.9184 for Proj alone and 25.8% for the old equal-weight
// rank mean). Older note on the equal-weight version:
// Basis: 15 Oct 2026, 1,139 races: the combined rank of Proj, Nett and L3 picked the winner about as often as Proj alone and the market already
// prices the agreement, so it is a reading aid. 16 Oct 2026 (688 races): when speed also agrees, all four rating the same runner #1 happened in
// 8% of races and that runner won 43.9% (market 41.6%), about break-even at the starting price; speed on its own is the weakest of the four.
export interface CombinedRank {
  rank: number
  tied: boolean // another runner shares this rank
  mean: number // lower is better: the negative of the weighted z-score
  rating: number | null // the weighted z-score put on the Proj scale: field mean of Proj + score x field spread of Proj (higher is better)
  ranks: [number | null, number | null, number | null] // Spd, Nett, Proj
  estimated: boolean // a first starter: the rating is its Proj estimate (race level and price), placed against the rated runners
}

const MIN_SIGNALS = 2
const W_SPD = 0.2
const W_NETT = 0.3
const W_PROJ = 0.5

function zscores(values: Map<string, number>): Map<string, number> {
  const v = [...values.values()]
  const out = new Map<string, number>()
  if (v.length < 2) return out
  const m = v.reduce((s, x) => s + x, 0) / v.length
  const sd = Math.sqrt(v.reduce((s, x) => s + (x - m) ** 2, 0) / (v.length - 1))
  if (sd < 1e-9) return out
  for (const [id, x] of values) out.set(id, (x - m) / sd)
  return out
}

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
): Map<string, CombinedRank> {
  const speed = new Map<string, number>()
  const nett = new Map<string, number>()
  const proj = new Map<string, number>()
  for (const r of runners) {
    if (scratched.has(r.runId)) continue
    if (r.speedRating != null) speed.set(r.runId, r.speedRating)
    if (r.nett != null) nett.set(r.runId, r.nett)
    // a first starter's Proj is an estimate from the race level and its price, not a form rating: it takes no part in the Rating
    if (r.projectionModel === 'debut') continue
    const p = effectiveByRunId[r.runId]?.effectiveProjectedWpr ?? r.projectedWpr
    if (p != null) proj.set(r.runId, p)
  }
  const rs = rankDesc(speed)
  const rn = rankDesc(nett)
  const rp = rankDesc(proj)
  const zs = zscores(speed)
  const zn = zscores(nett)
  const zp = zscores(proj)
  const means = new Map<string, { mean: number; ranks: CombinedRank['ranks'] }>()
  for (const r of runners) {
    if (scratched.has(r.runId)) continue
    const ranks: CombinedRank['ranks'] = [rs.get(r.runId) ?? null, rn.get(r.runId) ?? null, rp.get(r.runId) ?? null]
    let num = 0
    let den = 0
    let n = 0
    for (const [z, w] of [[zs, W_SPD], [zn, W_NETT], [zp, W_PROJ]] as const) {
      const v = z.get(r.runId)
      if (v == null) continue
      num += w * v
      den += w
      n++
    }
    if (n < MIN_SIGNALS) continue
    means.set(r.runId, { mean: -(num / den), ranks })
  }
  const pv = [...proj.values()]
  const pMean = pv.length > 1 ? pv.reduce((a, x) => a + x, 0) / pv.length : null
  const pSd = pMean != null ? Math.sqrt(pv.reduce((a, x) => a + (x - pMean) ** 2, 0) / (pv.length - 1)) : 0
  const all = [...means.values()].map((m) => m.mean)
  const out = new Map<string, CombinedRank>()
  for (const [id, m] of means) {
    out.set(id, { rank: 1 + all.filter((x) => x < m.mean - 1e-9).length, tied: all.filter((x) => Math.abs(x - m.mean) < 1e-9).length > 1, mean: m.mean, rating: pMean != null && pSd > 1e-9 ? pMean - m.mean * pSd : null, ranks: m.ranks, estimated: false })
  }
  // first starters: rating is the Proj estimate itself (already on the Proj scale); placed against the rated runners without shifting their ranks
  if (pMean != null && pSd > 1e-9) {
    for (const r of runners) {
      if (scratched.has(r.runId) || r.projectionModel !== 'debut' || out.has(r.runId)) continue
      const p = effectiveByRunId[r.runId]?.effectiveProjectedWpr ?? r.projectedWpr
      if (p == null) continue
      const mean = -(p - pMean) / pSd
      out.set(r.runId, { rank: 1 + all.filter((x) => x < mean - 1e-9).length, tied: all.some((x) => Math.abs(x - mean) < 1e-9), mean, rating: p, ranks: [null, null, null], estimated: true })
    }
  }
  return out
}
