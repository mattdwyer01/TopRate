// Clean, self-documenting types for the UI to consume. Produced from the raw
// payload (types/data.ts) by api/adapter.ts. Components should only ever
// import from this file, never from types/data.ts directly.

export interface FormRun {
  track: string
  distance: number
  going: string
  finishPosition: number | null
  wpr: number | null
  raceShapeEarly: number | null
  raceShapeMid: number | null
  raceShapeLate: number | null
  sectionalEarly: number | null
  sectionalTo800: number | null
  sectionalLate600: number | null
  barrier: number | null
  margin: number | null
  positionSettled: number | null
  position800m: number | null
  position400m: number | null
  raceClass: string | null
  jockey: string | null
  isPeakRun: boolean
  date?: string
}

export interface FormHistoryEntry {
  wpr: number | null
  going: string
  distance: number
  tempo: 'Fast' | 'Even' | 'Slow' | null
  relativeSettlePosition: number | null
  date: string
}

export interface GoingBreakdown {
  going: string
  starts: number
  wins: number
  places: number
}

export interface Runner {
  runId: string
  horse: string
  jockey: string
  trainer: string
  tabNumber: number
  barrier: number | null

  toprateRating: number | null
  topratePrice: number | null
  speedRating: number | null
  sectionalEarly: number | null
  sectionalMid: number | null
  sectionalLate: number | null
  sectionalTotal: number | null
  weightTrend: number | null
  distanceStarts: number | null
  distanceWins: number | null
  distancePlaces: number | null
  wprAtDistance: number | null
  goingBreakdown: GoingBreakdown[]
  formString: string | null
  marginFinish: number | null
  avgSettledPos: number | null

  wprLast1: number | null
  wprAvgLast3: number | null
  wprTrend: number | null
  wprPeakRank1Yr: number | null
  wprNett: number | null
  weightCarried: number | null
  jockeyWinPct90d: number | null
  trainerWinPct365d: number | null
  jockeyRating: number | null
  trainerRating: number | null

  fixedWinPrice: number | null
  // The fixed price at first capture today (the ~9am AEST daily fetch),
  // frozen server-side and never touched by the 5-min price refresh - see
  // toprate_daily.py's open_price freeze block. null for a runner whose
  // price wasn't yet captured this raceday (rare - only a very late
  // scratch-in or a data gap).
  openFixedPrice: number | null
  // Intraday fixed-price snapshots, oldest first (from toprate_price_history.csv
  // via toprate_daily.py's rebuild_html) - minutesSinceOpen is relative to
  // this runner's own first snapshot, not a fixed clock time. Empty when
  // there's no snapshot history yet (a very recent capture, or a payload
  // from before this field existed).
  priceSeries: { minutesSinceOpen: number; price: number }[]
  silkUrl: string | null
  startingPrice: number | null
  postRaceTopPrice: number | null
  finishPosition: number | null
  won: boolean
  fieldSize: number

  // WPR projection (the additive base+adjustment model - see wpr_projection.py)
  // baseWpr + wprAdjustment == projectedWpr (both null when there's no
  // projection at all - insufficient form history).
  projectedWpr: number | null
  baseWpr: number | null
  wprAdjustment: number | null
  // What drove wprAdjustment, by feature - values sum to wprAdjustment
  // exactly (includes a "baseline" entry for the model's uniform terms).
  // Null when there's no projection.
  adjustmentBreakdown: Record<string, number> | null
  projectionConfidence: number | null
  wprPrice: number | null
  wprRank: number | null
  peakWpr: number | null
  projectedWprAltGoing: number | null
  projectionConfidenceAltGoing: number | null
  projectionDescription: string | null

  // Populated ~5 days post-race once TopRate's own actual rating settles
  actualWpr: number | null
  actualWprRank: number | null

  commentsVideo: string | null
  commentsSteward: string | null

  // Auto-generated explanation for a MATERIAL miss (|actual - projected|
  // >= 4 WPR - see wpr_miss.py's explain_miss()). null when the miss isn't
  // material or the result hasn't settled yet. missCategory is one of
  // 'comment' | 'ceiling' | 'untried' | 'price' | 'unexplained' - the
  // frontend offers a manual-note fallback specifically for 'unexplained'.
  missCategory: string | null
  missReason: string | null

  recentRuns: FormRun[]
  peakRun: FormRun | null
  formHistory: FormHistoryEntry[]
  predictedSettlingBand: string | null
  againstShapeTendency: string | null
}

export interface Race {
  raceId: string
  date: string
  venue: string
  state: string
  raceNumber: number
  raceName: string
  distance: number
  going: string
  trackGrading: number | null
  rail: string | null
  prizeMoney: number | null
  startTime: string
  raceShapeEarly: number | null
  raceShapeMid: number | null
  raceShapeLate: number | null
  // Automated pre-race tempo estimate (race_speed_estimate.py) - a 0-1
  // pressure score and Hot/Fast/Even/Slow label. LOW CONFIDENCE (held-out
  // correlation with actual raceShapeEarly ~+0.24) - context only.
  // raceShapeEarly/Mid/Late above are the real measurement and take
  // priority once the race has actually run - see lib/pace.ts.
  paceEstimateScore: number | null
  paceEstimateLabel: string | null
  hasFirstStarter: boolean
  fieldSize: number
  allResulted: boolean
  runners: Runner[]
}

export interface PriceHistoryEntry {
  openPrice: number | null
  openAt: string | null
  resultPrice: number | null
  resultAt: string | null
  sampleCount: number | null
}

export interface DashboardData {
  races: Race[]
  priceHistory: Record<string, PriceHistoryEntry>
  runDate: string
  runIso: string
  githubRepo: string
  // Softmax beta behind wprPrice - lets the UI replicate the exact price
  // formula when a manual rating override changes the field's ratings.
  priceBeta: number | null
}
