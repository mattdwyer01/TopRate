// Raw shape of toprate_data.json, exactly as toprate_daily.py/toprate_html_v3.py
// produce it. Field names are the SAME short/abbreviated keys the Python
// backend already writes (see toprate_daily.py:2728-2884 for where each one
// comes from) - do not rename anything here. Components should never import
// from this file directly; go through api/adapter.ts's domain types instead.
// Keeping the raw and domain shapes as two separate files means the backend
// contract can be read/verified independently of how the UI wants to consume
// it, and a future backend field rename only touches this file + the adapter.

export interface RawFormRun {
  trk: string
  dist: number
  go: string
  fin: number | null
  wpr: number | null
  se: number | null
  sm: number | null
  sl: number | null
  ie: number | null
  im: number | null
  il: number | null
  bar: number | null
  mgn: number | null
  psl: number | null
  p8: number | null
  p4: number | null
  cls: string | null
  jck: string | null
  pk: 0 | 1
  d?: string
}

export interface RawFormAllEntry {
  w: number | null
  go: string
  ds: number
  tmp: string | null
  rel: number | null
  d: string
}

export interface RawGoingBreakdown {
  [going: string]: { starts: number; wins: number; places: number }
}

export interface RawRunner {
  rid: string
  h: string
  j: string
  tn: string
  tab: number
  t: number
  b: number | null
  trr: number | null
  trp: number | null
  spd: number | null
  es: number | null
  ms: number | null
  ls: number | null
  ts: number | null
  wtr: number | null
  ds: number | null
  dw: number | null
  dp: number | null
  wd: number | null
  gb: RawGoingBreakdown | null
  fm: string | null
  mgnL: number | null
  asp: number | null
  wpr1: number | null
  wpra: number | null
  wprt: number | null
  wprp: number | null
  w: number | null
  wt: number | null
  jw: number | null
  tw: number | null
  jcp: number | null
  jcr: number | null
  jrt: number | null
  trt: number | null
  fx: number | null
  op: number | null
  sk: string | null
  sp: number | null
  top: number | null
  f: number | null
  won: 0 | 1 | null
  fs: number
  // Real, data-driven late scratch (toprate_price_refresh.py rechecking
  // isScratched every ~5 min) - distinct from the manual, this-device-only
  // scratch toggle in wprOverrides.ts. Absent/0 on older cached payloads.
  scr?: 0 | 1
  wpjp: number | null
  wpjb: number | null
  wpjadj: number | null
  wpjcb: Record<string, number> | null
  wpjc: number | null
  wpjpr: number | null
  wpjr: number | null
  wpjpk: number | null
  wpjpA: number | null
  wpjcA: number | null
  wpjd: string | null
  wpja: number | null
  wpjar: number | null
  cmtV: string | null
  cmtS: string | null
  wpjmc: string | null
  wpjmr: string | null
  formRuns: RawFormRun[] | null
  peakRun: RawFormRun | null
  formAll: RawFormAllEntry[] | null
  psBand: string | null
  asTend: string | null
}

export interface RawRace {
  race_id: string
  date: string
  venue: string
  state: string
  race: number
  race_name: string
  distance: number
  going: string
  track_grading: number | null
  rail: string | null
  prize: number | null
  start_time: string
  rse: number | null
  rsm: number | null
  rsl: number | null
  // Automated pre-race tempo estimate (race_speed_estimate.py's trained
  // model) - a 0-1 pressure score and Hot/Fast/Even/Slow label. LOW
  // CONFIDENCE (held-out correlation with actual rse ~+0.24) - context
  // only. rse/rsm/rsl above are the real, post-race measurement and take
  // priority once the race has actually run.
  rs_score: number | null
  rs_label: string | null
  hfs: 0 | 1
  fs: number
  done: 0 | 1
  runners: RawRunner[]
}

export interface RawPriceHistEntry {
  o: number | null // open price
  oat: string | null // open-at timestamp
  r: number | null // result price
  rat: string | null // result-at timestamp
  n: number | null // number of price points sampled
  // Intraday snapshot series: [minutes-since-open, price][], consecutive
  // equal prices collapsed to their endpoints. Empty/absent on older
  // payloads that predate this field.
  s?: [number, number][]
}

export interface RawVenueBias {
  byVenueGoingRail: Record<string, unknown>
  byVenue: Record<string, unknown>
  totalRaces: number
}

export interface RawDashboardPayload {
  RACES: RawRace[]
  PICKS_TODAY: unknown[]
  SETTLED: unknown[]
  PRICE_HIST: Record<string, RawPriceHistEntry>
  MODEL_META: Record<string, unknown>
  MODEL_PICKS: Record<string, unknown>
  ALL_PICKS_FLAT: unknown[]
  PRIMARY_KEY: string
  RUN_DATE: string
  RUN_ISO: string
  GITHUB_REPO: string
  VENUE_BIAS: RawVenueBias
  // Softmax beta behind wpjpr (WPR $) - lets the frontend replicate the
  // exact price formula for a manual-override recompute (see lib/raceModel.ts).
  PRICE_BETA: number | null
}
