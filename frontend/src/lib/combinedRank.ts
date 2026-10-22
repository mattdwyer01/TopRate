import type { Runner } from '../types/domain'
import type { EffectiveRunner } from './raceModel'
import { speedRatingOnScale } from './speed'

// Combined rank. Score = weighted mean of the raw Proj (0.50), Nett (0.30) and Spd (0.20) figures on the Proj scale (22 Oct 2026, owner's call: raw 50 / 30 / 20 after the z-score comparison below), over the signals
// the runner has; the rank orders the scores (ties share the best place). A runner needs at least two of the three. Spd is its rating put on the Nett / Proj scale (`speedRatingOnScale`). The Rating is exactly the weighted average of the
// figures shown (22 Oct 2026, owner's call): an earlier version shifted Nett and Spd to the field mean of Proj first, which cannot change the order when all three are present (a constant per race)
// and only made the number harder to check by eye (Happy Smile 83.1 vs 83.9 from its tiles). A runner missing a signal renormalises the weights over the ones it has, so it can sit a point or so off level in a field where the signals' means differ.
// Basis (`research/z_vs_raw.py`, 4,530 races 4 Jul to 17 Oct 2026, Proj / Nett / Spd all present, clean books, softmax sharpness cross-fitted by date halves): winner log-lik z-score blend 50/30/20 -1.9108 vs raw
// 50/30/20 -1.8905 (paired +0.0204, se 0.0036; raw keeps how spread out the race is, a z-score throws it away); the old Rating (z blend x field Proj spread) -1.8963. A free raw fit gives Proj 0.68 / Nett 0.20 / Spd 0.12
// (90% interval 0.63-0.73 / 0.16-0.24 / 0.09-0.15, log-lik -1.8855); 50/30/20 was kept by the owner. Within 2 / 4 points of the top the raw 50/30/20 holds 2.36 / 4.14 runners and 52% / 72% of winners (Proj alone 2.12 / 3.59
// and 49% / 67%); at a fixed shortlist size it is no better than Proj alone, so the points lines add readability, not accuracy.
// L3 was removed from the dashboard (20 Oct 2026): Proj is built from the same runs and a fitted blend gave L3 a weight of -0.01 (`research/rank_weights.py`). Still a reading aid: nothing here beats the closing price.
export interface CombinedRank {
  rank: number
  tied: boolean // another runner shares this rank
  mean: number // lower is better: the negative of the rating
  rating: number | null // the weighted blend of Proj, Nett and Spd on the Proj scale (higher is better)
  ranks: [number | null, number | null, number | null] // TR (nett), SR (speed), WR (proj)
  estimated: boolean // a first starter: the rating is its Proj estimate (race level and price), placed against the rated runners
}

const MIN_SIGNALS = 2
const W_SPD = 0.2
const W_NETT = 0.3
const W_PROJ = 0.5

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
  const speed = new Map<string, number>() // Spd rating on the Nett / Proj scale
  const nett = new Map<string, number>()
  const proj = new Map<string, number>()
  for (const r of runners) {
    if (scratched.has(r.runId)) continue
    if (r.speedRating != null) speed.set(r.runId, speedRatingOnScale(r.speedRating))
    if (r.nett != null) nett.set(r.runId, r.nett)
    // a first starter's Proj is an estimate from the race level and its price, not a form rating: it takes no part in the Rating
    if (r.projectionModel === 'debut') continue
    const p = effectiveByRunId[r.runId]?.effectiveProjectedWpr ?? r.projectedWpr
    if (p != null) proj.set(r.runId, p)
  }
  const rs = rankDesc(speed)
  const rn = rankDesc(nett)
  const rp = rankDesc(proj)
  const scores = new Map<string, { rating: number; ranks: CombinedRank['ranks'] }>()
  for (const r of runners) {
    if (scratched.has(r.runId)) continue
    const ranks: CombinedRank['ranks'] = [rn.get(r.runId) ?? null, rs.get(r.runId) ?? null, rp.get(r.runId) ?? null]
    let num = 0
    let den = 0
    let n = 0
    const sp = speed.get(r.runId)
    const ne = nett.get(r.runId)
    const pr = proj.get(r.runId)
    if (sp != null) { num += W_SPD * sp; den += W_SPD; n++ }
    if (ne != null) { num += W_NETT * ne; den += W_NETT; n++ }
    if (pr != null) { num += W_PROJ * pr; den += W_PROJ; n++ }
    if (n < MIN_SIGNALS) continue
    scores.set(r.runId, { rating: num / den, ranks })
  }
  const all = [...scores.values()].map((m) => -m.rating)
  const out = new Map<string, CombinedRank>()
  for (const [id, m] of scores) {
    const mean = -m.rating
    out.set(id, { rank: 1 + all.filter((x) => x < mean - 1e-9).length, tied: all.filter((x) => Math.abs(x - mean) < 1e-9).length > 1, mean, rating: m.rating, ranks: m.ranks, estimated: false })
  }
  // first starters: rating is the Proj estimate itself (already on the Proj scale); placed against the rated runners without shifting their ranks
  for (const r of runners) {
    if (scratched.has(r.runId) || r.projectionModel !== 'debut' || out.has(r.runId)) continue
    const p = effectiveByRunId[r.runId]?.effectiveProjectedWpr ?? r.projectedWpr
    if (p == null) continue
    const mean = -p
    out.set(r.runId, { rank: 1 + all.filter((x) => x < mean - 1e-9).length, tied: all.some((x) => Math.abs(x - mean) < 1e-9), mean, rating: p, ranks: [null, null, null], estimated: true })
  }
  return out
}
