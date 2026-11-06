import type { Race, Runner } from '../types/domain'
import type { Ranked } from '../features/race/raceFacts'

// Day-of draw lean, DISPLAY ONLY (owner's call, 23 Oct 2026: nothing about track bias is inside the Proj calculation). Once 3 or more races at a meeting have a clear top 4,
// projection/run.py reads which way the draw has run (mean barrier of the placegetters against the middle of the field) and logs lean x 15 x (barrier position - 0.5) for
// fields of 8+ as `badj` (wprp_contrib.bias): what the lean WOULD add. It is NOT added to Proj. This file shows it, so a runner whose rating the lean would move, or a race
// where it would change the order, can be flagged. Checked on the out-of-sample Proj: the flag points the right way (helped runners ran 0.4 above the Proj without it, hurt
// runners 1.0 below). The SM column's own suitability figure is separate.

// A runner is flagged when the draw lean would move its projection by at least this many WPR.
export const BIAS_FLAG_MIN = 0.3

// The lean needs this many earlier races at the meeting with a result (the projection also needs a clear top 4 and an 8+ field in each).
export const MIN_BIAS_RACES = 3

export const runnerBias = (r: Runner): number => r.adjustmentBreakdown?.bias ?? 0

export const hasRunnerBias = (r: Runner): boolean => Math.abs(runnerBias(r)) >= BIAS_FLAG_MIN

export const fmtBias = (v: number): string => `${v >= 0 ? '+' : ''}${v.toFixed(1)}`

/** Races at this meeting, earlier than this one, that have a result (so their running has been read into the bias). */
export function racesRunBefore(race: Race, all: Race[]): number {
  const t = new Date(race.startTime).getTime()
  return all.filter((r) => r.venue === race.venue && r.date === race.date && r.raceId !== race.raceId && new Date(r.startTime).getTime() < t && r.runners.some((x) => x.resultKnown || x.finishPosition != null)).length
}

export interface NoBias {
  // Projection (same scale as Ranked.proj) WITH the draw lean applied. The Proj itself does not contain it. The speed-map figure is unchanged.
  proj: number
  sm: number | null
}

/** Each ranked runner's projection with the draw lean applied on top, so the race can be re-ranked as it would stand if the lean were used. */
export function withoutBias(ranked: Ranked[]): Map<string, NoBias> {
  const suit = ranked.map((x) => (x.runner.adjustmentBreakdown?.suitability != null ? x.runner.adjustmentBreakdown.suitability : null))
  const vals = suit.filter((v): v is number => v != null)
  const mean = vals.length ? vals.reduce((a, b) => a + b, 0) / vals.length : 0
  const out = new Map<string, NoBias>()
  ranked.forEach((x, i) => out.set(x.runner.runId, { proj: x.proj + runnerBias(x.runner), sm: suit[i] != null ? (suit[i] as number) - mean : null }))
  return out
}

export interface BiasMover {
  runner: Runner
  bias: number
  rankNow: number
  // Rank if the lean were applied (the Proj itself does not apply it).
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
    if (b == null || size < 6) continue
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
