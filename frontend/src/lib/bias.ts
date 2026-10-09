import type { Race, Runner } from '../types/domain'
import type { Ranked } from '../features/race/raceFacts'

// Day-of track bias, as the projection sees it. Once races have run at a meeting the suitability adjustment reads how they ran (draw bias from the finishing
// order intraday; front-runner bias also once 800m positions arrive overnight). projection/run.py logs how much of each main-model runner's adjustment that is
// (`badj`, passed as wprp_contrib.bias): the adjustment minus the adjustment with the bias inputs blanked. It is already inside Proj and SM; this file only
// shows what it changed, so a runner or a race that moved because of the bias can be flagged.

// A runner is flagged when the bias moved its projection by at least this many WPR (about half the typical suitability spread).
export const BIAS_FLAG_MIN = 0.3

export const runnerBias = (r: Runner): number => r.adjustmentBreakdown?.bias ?? 0

export const hasRunnerBias = (r: Runner): boolean => Math.abs(runnerBias(r)) >= BIAS_FLAG_MIN

export const fmtBias = (v: number): string => `${v >= 0 ? '+' : ''}${v.toFixed(1)}`

/** Races at this meeting, earlier than this one, that have a result (so their running has been read into the bias). */
export function racesRunBefore(race: Race, all: Race[]): number {
  const t = new Date(race.startTime).getTime()
  return all.filter((r) => r.venue === race.venue && r.date === race.date && r.raceId !== race.raceId && new Date(r.startTime).getTime() < t && r.runners.some((x) => x.resultKnown || x.finishPosition != null)).length
}

export interface NoBias {
  // Projection (same scale as Ranked.proj) without the bias, and the speed-map figure (suitability minus the bias, demeaned against the race) without it.
  proj: number
  sm: number | null
}

/** Each ranked runner's projection and SM with the bias taken out, so the race can be re-ranked as it stood before the earlier races ran. */
export function withoutBias(ranked: Ranked[]): Map<string, NoBias> {
  const suit = ranked.map((x) => (x.runner.adjustmentBreakdown?.suitability != null ? x.runner.adjustmentBreakdown.suitability - runnerBias(x.runner) : null))
  const vals = suit.filter((v): v is number => v != null)
  const mean = vals.length ? vals.reduce((a, b) => a + b, 0) / vals.length : 0
  const out = new Map<string, NoBias>()
  ranked.forEach((x, i) => out.set(x.runner.runId, { proj: x.proj - runnerBias(x.runner), sm: suit[i] != null ? (suit[i] as number) - mean : null }))
  return out
}

export interface BiasMover {
  runner: Runner
  bias: number
  rankNow: number
  rankBefore: number
}

export interface RaceBias {
  racesRun: number
  movers: BiasMover[]
  // Positive when runners drawn wide are helped by the bias on average, negative when inside runners are; null when no clear lean.
  drawLean: number | null
  rankChanges: number
}

export function computeRaceBias(ranked: Ranked[], race: Race, all: Race[]): RaceBias {
  const racesRun = racesRunBefore(race, all)
  const nb = withoutBias(ranked)
  const before = [...ranked].sort((a, b) => (nb.get(b.runner.runId)?.proj ?? b.proj) - (nb.get(a.runner.runId)?.proj ?? a.proj))
  const rankBefore = new Map(before.map((x, i) => [x.runner.runId, i + 1]))
  const movers = ranked
    .map((x, i) => ({ runner: x.runner, bias: runnerBias(x.runner), rankNow: i + 1, rankBefore: rankBefore.get(x.runner.runId) ?? i + 1 }))
    .filter((m) => Math.abs(m.bias) >= BIAS_FLAG_MIN)
    .sort((a, b) => Math.abs(b.bias) - Math.abs(a.bias))
  // Draw lean: bias of the widest third of the draw minus the inner third.
  const size = ranked.length
  const wide: number[] = []
  const inner: number[] = []
  for (const x of ranked) {
    const b = x.runner.barrier
    if (b == null || size < 6 || x.runner.adjustmentBreakdown?.suitability == null) continue
    const f = (b - 1) / Math.max(size - 1, 1)
    if (f >= 0.67) wide.push(runnerBias(x.runner))
    else if (f <= 0.33) inner.push(runnerBias(x.runner))
  }
  const avg = (v: number[]) => (v.length ? v.reduce((a, c) => a + c, 0) / v.length : null)
  const aw = avg(wide)
  const ai = avg(inner)
  const lean = aw != null && ai != null && Math.abs(aw - ai) >= 0.2 ? aw - ai : null
  return { racesRun, movers, drawLean: lean, rankChanges: movers.filter((m) => m.rankNow !== m.rankBefore).length }
}
