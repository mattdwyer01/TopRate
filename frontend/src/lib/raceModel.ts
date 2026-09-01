import type { Runner } from '../types/domain'

export interface EffectiveRunner {
  effectiveProjectedWpr: number | null
  effectivePrice: number | null
  effectiveRank: number | null
  hasOverride: boolean
  scratched: boolean
}

export interface EdgeScoreConfig {
  features: string[]
  means: Record<string, number>
  stds: Record<string, number>
  beta: number
}

// The wpr_price cap in wpr_projection.py's project_race() - a no-hope
// runner's raw softmax price can blow out to 5-6 figures; capped at 999
// since beyond that the exact number is meaningless. compute_edge_scores'
// blend_price uses the same cap.
const PRICE_CAP = 999

// Backend's own fallback when config.json doesn't carry a beta (see
// wpr_projection.py's get_price_beta) - practically never hit once
// PRICE_BETA is always populated, kept only for defensiveness.
const DEFAULT_BETA = 0.4

// Replicates wpr_projection.py's compute_edge_scores() blend score EXACTLY
// (same z-score-average formula, same "missing wprp_proj forces score to
// 0.0" rule - see that function's own _score docstring) over an EFFECTIVE
// wprp_proj: the model's own projectedWpr, or a manually entered base for a
// runner the model couldn't project, plus any manual delta on top.
// trainer/jockey/pfm are NOT overridable - a rating override only changes
// the horse's own WPR, so those three stay at the runner's real observed
// values throughout.
function blendScore(
  effectiveWpr: number | null,
  runner: Runner,
  cfg: EdgeScoreConfig,
): number {
  if (effectiveWpr == null) return 0.0
  const raw: Record<string, number | null> = {
    wprp_proj: effectiveWpr,
    trainer_win_pct_365d: runner.trainerWinPct365d,
    jockey_win_pct_90d: runner.jockeyWinPct90d,
    pfm_score: runner.pfmScore,
  }
  const zs: number[] = []
  for (const f of cfg.features) {
    const v = raw[f]
    const std = cfg.stds[f]
    if (v == null || !std) continue
    zs.push((v - (cfg.means[f] ?? 0)) / std)
  }
  return zs.length ? zs.reduce((a, b) => a + b, 0) / zs.length : 0.0
}

// Replicates wpr_projection.py's project_race()/compute_edge_scores()
// price/rank softmax EXACTLY, but over EFFECTIVE ratings: the model's own
// projectedWpr, or a manually entered base for a runner the model
// couldn't project, each with any manual delta added on top. This is what
// lets a manual override on one runner correctly shift every OTHER
// runner's price too - it's a field-relative softmax, not a per-runner
// calculation.
//
// "WPR $"/rank (wprPrice/wprRank) are the edge_score BLEND price/rank as
// of Sep 2026 (see compute_edge_scores) - a held-out backtest found the
// blend beats plain-projection ranking on both AUC and top-1 strike rate.
// When edgeScoreConfig is available this recomputes the full blend
// (holding each runner's own trainer/jockey/pfm fixed, only the WPR term
// moves with the override); if it's null (calibration not yet fitted
// server-side), falls back to the older plain-projection softmax so the
// override still does SOMETHING sensible rather than nothing.
export function computeEffectiveRace(
  runners: Runner[],
  deltas: Record<string, number>,
  bases: Record<string, number>,
  priceBeta: number | null,
  edgeScoreConfig: EdgeScoreConfig | null,
  // A per-device "sharpness" multiplier (Settings > WPR $ price sharpness,
  // see App.tsx's own computation) applied to whichever beta is actually
  // in effect, since the override is edited on the OLD plain-projection
  // beta's scale (~0.15-0.4) while the blend's calibrated beta (1.0) lives
  // on a different numeric scale (z-score gaps, not WPR-point gaps).
  // 1 = no override (use the calibrated beta as-is).
  sharpnessScale: number = 1,
  scratched: Set<string> = new Set(),
): Record<string, EffectiveRunner> {
  const withEffectiveWpr = runners.map((r) => {
    const modelBase = r.projectedWpr ?? (r.runId in bases ? bases[r.runId] : null)
    const delta = deltas[r.runId] ?? 0
    const hasOverride = deltas[r.runId] != null || (r.projectedWpr == null && r.runId in bases)
    const isScratched = scratched.has(r.runId)
    return {
      runId: r.runId,
      runner: r,
      // A scratched runner has no wpr for softmax purposes - excluded from
      // the field entirely (not just zeroed out), so the rest of the field
      // renormalizes as if it were never entered. A non-scratched runner
      // with no model projection and no manual base stays null too (no
      // rating source at all) - what THAT means for the softmax population
      // differs between the two formulas below.
      wpr: !isScratched && modelBase != null ? modelBase + delta : null,
      hasOverride,
      scratched: isScratched,
    }
  })

  // Softmax population: the blend (compute_edge_scores) includes EVERY
  // non-scratched runner, even one with no wprp_proj at all - blendScore
  // forces that runner's score to 0.0 rather than excluding it (see its
  // own docstring; verified against the server's own shipped wpjpr - a
  // fallback runner like a first-starter genuinely gets a real, non-null
  // WPR $ price server-side). The legacy plain-projection softmax
  // (project_race) does the opposite - it excludes a fallback runner
  // entirely (`valid = not fallback`), so mirror that instead when
  // edgeScoreConfig is unavailable.
  const population = edgeScoreConfig
    ? withEffectiveWpr.filter((r) => !r.scratched)
    : withEffectiveWpr.filter((r) => r.wpr != null)

  const priceByRunId = new Map<string, number>()
  const rankByRunId = new Map<string, number>()
  if (population.length >= 2) {
    const scored = edgeScoreConfig
      ? population.map((r) => ({ runId: r.runId, score: blendScore(r.wpr, r.runner, edgeScoreConfig) }))
      : (population as { runId: string; wpr: number }[]).map((r) => ({ runId: r.runId, score: r.wpr }))
    const beta = (edgeScoreConfig ? edgeScoreConfig.beta : (priceBeta ?? DEFAULT_BETA)) * sharpnessScale
    const maxScore = Math.max(...scored.map((r) => r.score))
    const exps = scored.map((r) => ({ runId: r.runId, e: Math.exp(beta * (r.score - maxScore)) }))
    const sumE = exps.reduce((s, x) => s + x.e, 0)
    for (const x of exps) {
      priceByRunId.set(x.runId, Math.min(1 / (x.e / sumE), PRICE_CAP))
    }
    ;[...scored]
      .sort((a, b) => b.score - a.score)
      .forEach((r, i) => rankByRunId.set(r.runId, i + 1))
  }

  const result: Record<string, EffectiveRunner> = {}
  for (const r of withEffectiveWpr) {
    result[r.runId] = {
      // Still null for a fallback (no-projection) runner even when it DID
      // get a blend price below - "Proj" has nothing to show, "WPR $" does
      // (matches the server's own wprp_blend_price behaviour - see
      // population's own comment above).
      effectiveProjectedWpr: r.wpr,
      effectivePrice: priceByRunId.get(r.runId) ?? null,
      effectiveRank: rankByRunId.get(r.runId) ?? null,
      hasOverride: r.hasOverride,
      scratched: r.scratched,
    }
  }
  return result
}
