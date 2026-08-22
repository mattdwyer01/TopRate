// Plain-language labels for wpr_projection.py's ADJ_FEATURES, so the detail
// modal can show what's actually driving a runner's adjustment (not just
// the total) - including small adjustments too small for describe()'s own
// narration threshold (>=3 WPR) to say anything about.
export const ADJUSTMENT_LABELS: Record<string, string> = {
  first_up: 'First-up from a spell',
  second_up: 'Second-up',
  days_since: 'Days since last run',
  runs_this_camp: 'Runs this campaign',
  dist_grad: 'Distance change',
  going_delta: 'Going change',
  today_wet: 'Wet track today',
  cur_surface: 'Non-turf surface',
  class_move: 'Class move',
  field_size: 'Field size',
  trend: 'Recent form trend',
  recent_vs_career: 'Recent vs career average',
  std_last5: 'Recent form consistency',
  avg_margin: 'Average finishing margin',
  consistency_ratio: 'Results consistency',
}

// Not tied to this horse or race - the model's own constant terms (Ridge
// intercept + calibration offset). Kept out of the main "what's driving
// this" list and shown as a single reconciling line instead.
export const BASELINE_KEY = 'baseline'
