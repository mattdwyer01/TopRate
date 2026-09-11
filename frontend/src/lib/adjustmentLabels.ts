// Plain-language labels for wpr_projection.py's ADJ_TERMS, so the detail
// modal can show what's actually driving a runner's adjustment (not just
// the total) - including small adjustments too small for describe()'s own
// narration threshold (>=3 WPR) to say anything about.
//
// own_first_up/own_second_up/own_long_spell: this horse's own +/- vs its
// own career average in matching past runs, shrunk toward 0 the fewer
// matching runs it has (see wpr_projection.py's _shrink()). Everything
// else is population-fitted (a small model trained across every horse,
// not just this one) - see wpr_projection.py's ADJ_TERMS.
export const ADJUSTMENT_LABELS: Record<string, string> = {
  own_distance: 'This trip vs its own average',
  own_going: 'This going vs its own average',
  own_first_up: 'First-up vs its own average',
  own_second_up: 'Second-up vs its own average',
  own_trend: 'Improving/declining trend',
  own_long_spell: 'After a long spell vs its own average',
  track_barrier: 'Barrier draw at this track and trip',
  closing_merit: 'Closing sectionals vs race pace',
  gear_change: 'Gear change today',
  trainer_merit: "Trainer's recent strike rate",
  jockey_merit: "Jockey's recent strike rate",
  pace_shape: "Today's predicted race shape fit",
  // Sep 2026: replaced own_distance/own_going/own_trend (this horse's own
  // history, above) with these three population-fitted terms - see
  // wpr_projection.py's ADJ_TERMS history comment.
  trainer_change: 'Trainer change today',
  pop_distance: 'Distance step-up/down (field-wide pattern)',
  pop_going: 'Wet/dry form profile (field-wide pattern)',
}

// Terms whose model only ever sees a strike-rate PERCENTAGE, never the
// ride/run count behind it - a thin sample (a jockey on 2 rides who won
// 1) can produce as large a number as a genuinely reliable one. See
// wpr_projection.py's _merit_term/_MERIT_SAMPLE_SHRINK_K docstring: the
// live model itself now discounts these by sample size when the count is
// available; this flag is the DISPLAY-side signal that a shown value sits
// in that same thin-sample territory, for whichever runners the shrink
// couldn't fully soften (or where the count still isn't available at all -
// see LOW_SAMPLE_THRESHOLD below).
export const SAMPLE_SIZE_TERMS = new Set(['trainer_merit', 'jockey_merit'])

// Below this many rides/runs in the trailing window, flag the figure as
// low-confidence. Matches wpr_projection.py's own _MERIT_SAMPLE_SHRINK_K
// (10) - same untuned-starting-point caveat applies (no historical
// ride-count data exists yet to validate this number against).
export const LOW_SAMPLE_THRESHOLD = 10
