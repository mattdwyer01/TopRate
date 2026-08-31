// Plain-language labels for wpr_projection.py's ADJ_TERMS, so the detail
// modal can show what's actually driving a runner's adjustment (not just
// the total) - including small adjustments too small for describe()'s own
// narration threshold (>=3 WPR) to say anything about.
//
// Each term is this horse's own +/- vs its own career average in matching
// past runs (distance/going/first-up/second-up/trend/long-spell), not a
// population-fitted coefficient - see wpr_projection.py's ADJ_TERMS.
export const ADJUSTMENT_LABELS: Record<string, string> = {
  own_distance: 'This trip vs its own average',
  own_going: 'This going vs its own average',
  own_first_up: 'First-up vs its own average',
  own_second_up: 'Second-up vs its own average',
  own_trend: 'Improving/declining trend',
  own_long_spell: 'After a long spell vs its own average',
  track_barrier: 'Barrier draw at this track and trip',
  closing_merit: 'Closing sectionals vs race pace',
}
