import type { Runner } from '../types/domain'

// Replaces jtComboStrategy.ts (Aug 2026) - that file's qualifiers were
// gated on jtComboWinPct, confirmed to leak the runner's own race result
// (see toprate_daily.py's SIGNALS comment). This is the validated
// replacement: runner.edgeScore (model win probability minus the market's
// own implied probability, from wpr_projection.compute_edge_scores) is a
// held-out-backtested bet-selection signal, not a rediscovered "strongest
// predictor" claim - see calibrate_edge_score.py's docstring for the
// numbers and caveats.
//
// Three thresholds, not three different strategies - they're the same
// signal at different sensitivity, offered so a lower-volume/higher-bar cut
// is available without hardcoding a claim that a tighter threshold is
// "stronger" (the held-out backtest actually found the top band noisier,
// not cleanly better - see calibrate_edge_score.py's docstring). The
// EdgeScoreboard tracks REAL forward performance per tier instead of
// quoting a fixed backtest number, so this stays honest as more results
// come in rather than going stale.
export type EdgeTier = 'edge-8' | 'edge-10' | 'edge-13'

export const EDGE_TIER_THRESHOLD: Record<EdgeTier, number> = {
  'edge-8': 0.08,
  'edge-10': 0.1,
  'edge-13': 0.13,
}

export function qualifiesForEdgeTier(runner: Runner, tier: EdgeTier): boolean {
  return !runner.dataScratched && runner.edgeScore != null && runner.edgeScore >= EDGE_TIER_THRESHOLD[tier]
}
