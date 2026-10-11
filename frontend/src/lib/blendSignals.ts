import type { Race } from '../types/domain'
import { computeEffectiveRace, type EffectiveRunner } from './raceModel'
import { signalFor, signalsForRace, type BetSignals, type Signal, type Tier } from './betSignals'

// One consistent blend (11 Oct 2026, EXPERIMENTAL). Rating, win chance, Model $, Edge and the Select/Volume tiers all come from the same 40% bet-signal /
// 60% WPR-projection rating. Win chance = softmax(BLEND_BETA x rating) over the runners still in the race; Model $ = 1 / chance; edge = chance x price.
// BLEND_BETA 0.248 is the value that calibrated the blended rating to winners on 1,693 July to October 2026 races.
// NOT VALIDATED AS A BETTING RULE: on those races the blended win chance had a worse log-loss than the pure model (1.826 vs 1.776; market 1.770), it
// over-predicts the high-edge runners (EV > 1.2 won 5.0% against 9.2% predicted), and every threshold tried lost money (about -28% to -37% flat at SP).
// No price floor (dropped 11 Oct 2026 at the user's request; the pure model's $3 floor came from favourites returning about 0%). The thresholds below are therefore a volume choice, not a backtested edge: they are set high so only about the top 1% to 5% of $3+ runners (blend EV
// above 2.17 / 1.60 are the 99th / 95th percentiles of $3+ runners) are flagged. The pure-model tiers (backtest +53% Select at SP) are still logged by betsignal/score.py
// and judged by betsignal/forward_check.py.
export const BLEND_BETA = 0.248
export const BLEND_SELECT_EV = 2.0
export const BLEND_VOLUME_EV = 1.6

function blendTier(ev: number): Tier {
  if (ev > BLEND_SELECT_EV) return 'S'
  if (ev > BLEND_VOLUME_EV) return 'V'
  return ''
}

/** Replaces each runner's signal with one whose win chance, edge and tier come from the blended rating. Races whose rating is the projection alone keep
 *  the raw signal untouched (their Model $ is then the pure model's, as before). */
export function blendSignals(
  race: Race,
  raw: Record<string, Signal | null>,
  effective: Record<string, EffectiveRunner>,
): Record<string, Signal | null> {
  const active = race.runners.filter((r) => {
    const e = effective[r.runId]
    return e && !e.scratched && e.effectiveProjectedWpr != null && raw[r.runId] != null
  })
  const usesBlend = active.length >= 5 && active.every((r) => effective[r.runId].ratingSource === 'bet')
  if (!usesBlend) return raw
  const top = Math.max(...active.map((r) => effective[r.runId].effectiveProjectedWpr as number))
  const exps = active.map((r) => Math.exp(BLEND_BETA * ((effective[r.runId].effectiveProjectedWpr as number) - top)))
  const sum = exps.reduce((a, b) => a + b, 0)
  const out: Record<string, Signal | null> = { ...raw }
  active.forEach((r, i) => {
    const s = raw[r.runId] as Signal
    const m = exps[i] / sum
    const e = m * s.p
    out[r.runId] = { ...s, m: Math.round(m * 10000) / 10000, e: Math.round(e * 1000) / 1000, t: blendTier(e) }
  })
  return out
}

/** Whole-window version for the Bets tab: blended signals for every race, packed back into a BetSignals so bets are listed from the same figures the
 *  Race page shows. Manual rating overrides are ignored here. */
export function blendedBetSignals(races: Race[], signals: BetSignals | null): BetSignals | null {
  if (!signals) return null
  const runs: BetSignals['runs'] = { ...signals.runs }
  for (const race of races) {
    const jumped = race.runners.some((r) => r.finishPosition !== null || r.resultKnown) || (race.startTime ? new Date(race.startTime).getTime() < Date.now() : false)
    const raw = signalsForRace(race, signals)
    const eff = computeEffectiveRace(race.runners, {}, {}, null, new Set(race.runners.filter((r) => r.dataScratched).map((r) => r.runId)), raw)
    const blended = blendSignals(race, raw, eff)
    for (const r of race.runners) {
      const b = blended[r.runId]
      if (!b || b === raw[r.runId]) continue
      const old = signals.runs[r.runId]
      if (!old || !signalFor(old, jumped)) continue
      runs[r.runId] = { ...old, now: b, fz: b }
    }
  }
  return { ...signals, runs }
}
