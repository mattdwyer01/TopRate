import type { Runner } from '../types/domain'

// Replaces jtComboStrategy.ts (Aug 2026) - that file's qualifiers were
// gated on jtComboWinPct, confirmed to leak the runner's own race result
// (see toprate_daily.py's SIGNALS comment). This is the validated
// replacement: runner.edgeScore (model win probability minus the market's
// own implied probability, from wpr_projection.compute_edge_scores) is a
// walk-forward-backtested bet-selection signal, not a rediscovered
// "strongest predictor" claim - see calibrate_edge_score.py's docstring
// for the numbers and caveats.
//
// Thresholds 8% and 10% were REMOVED (not just de-emphasized) after a
// walk-forward audit (Aug 2026, after the blend switched to forcing
// score=0 for a missing wprp_proj) found them SIGNIFICANTLY NEGATIVE
// (t=-2.05 and t=-2.65, not just unproven - see
// wpr_models/config.json's edge_score.overlay_validation for the current
// numbers, calibrate_edge_score.py re-derives them). 13/15/20% are not
// proven positive either (none reached |t|>=1.96) but at least aren't
// disproven - don't read the highest as "best", the audit found the top
// band noisier, not cleanly better. The EdgeScoreboard tracks REAL
// forward performance per tier instead of quoting a fixed backtest
// number, so this stays honest as more results come in rather than
// going stale. Re-run calibrate_edge_score.py periodically and update
// these thresholds/blurbs in EdgeOverlays.tsx if the numbers move.
export type EdgeTier = 'edge-13' | 'edge-15' | 'edge-20'

export const EDGE_TIER_THRESHOLD: Record<EdgeTier, number> = {
  'edge-13': 0.13,
  'edge-15': 0.15,
  'edge-20': 0.2,
}

// The floor for showing an EDGE badge/callout anywhere in the Race tab
// (RunnerRow, RunnerDetailModal) - must match the lowest tier above
// (edge-13), NOT the old 0.08 which is now a CONFIRMED loss (see this
// file's header comment). Showing a "value" badge at a proven-losing
// threshold would be actively misleading, not just unproven.
export const EDGE_BADGE_THRESHOLD = EDGE_TIER_THRESHOLD['edge-13']

export function qualifiesForEdgeTier(runner: Runner, tier: EdgeTier): boolean {
  return !runner.dataScratched && runner.edgeScore != null && runner.edgeScore >= EDGE_TIER_THRESHOLD[tier]
}
