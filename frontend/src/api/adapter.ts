import type {
  RawDashboardPayload,
  RawFormAllEntry,
  RawFormRun,
  RawRace,
  RawRunner,
} from '../types/data'
import type {
  DashboardData,
  FormHistoryEntry,
  FormRun,
  GoingBreakdown,
  PriceHistoryEntry,
  Race,
  Runner,
} from '../types/domain'

// Some runners (jockey not yet declared for a future acceptance, mostly)
// carry the raw payload's jockey/trainer field as the literal string "nan"
// rather than a real null - a pandas NaN that got stringified somewhere in
// the pipeline's JSON build rather than nulled. Found via the runner search
// feature, which renders these names directly in a compact list where a
// literal "nan" stood out immediately. Cleaned here at the adapter boundary
// (its whole job is turning the raw payload's rough edges into clean
// domain data) rather than chasing it into the Python payload builder.
function cleanName(v: string | null | undefined): string {
  if (v == null) return ''
  const trimmed = v.trim()
  return trimmed.toLowerCase() === 'nan' ? '' : trimmed
}

function toFormRun(r: RawFormRun): FormRun {
  return {
    track: r.trk,
    distance: r.dist,
    going: r.go,
    finishPosition: r.fin,
    wpr: r.wpr,
    raceShapeEarly: r.se,
    raceShapeMid: r.sm,
    raceShapeLate: r.sl,
    sectionalEarly: r.ie,
    sectionalTo800: r.im,
    sectionalLate600: r.il,
    barrier: r.bar,
    margin: r.mgn,
    positionSettled: r.psl,
    position800m: r.p8,
    position400m: r.p4,
    raceClass: r.cls,
    jockey: r.jck,
    isPeakRun: r.pk === 1,
    date: r.d,
  }
}

function toFormHistoryEntry(r: RawFormAllEntry): FormHistoryEntry {
  return {
    wpr: r.w,
    going: r.go,
    distance: r.ds,
    tempo: r.tmp as FormHistoryEntry['tempo'],
    relativeSettlePosition: r.rel,
    date: r.d,
  }
}

function toGoingBreakdown(
  gb: RawRunner['gb'],
): GoingBreakdown[] {
  if (!gb) return []
  return Object.entries(gb).map(([going, v]) => ({
    going,
    starts: v.starts,
    wins: v.wins,
    places: v.places,
  }))
}

function toRunner(r: RawRunner, priceHist: RawDashboardPayload['PRICE_HIST'] | undefined): Runner {
  const series = priceHist?.[r.rid]?.s ?? []
  return {
    runId: r.rid,
    horse: r.h,
    jockey: cleanName(r.j),
    trainer: cleanName(r.tn),
    tabNumber: r.tab ?? r.t,
    barrier: r.b,

    toprateRating: r.trr,
    topratePrice: r.trp,
    speedRating: r.spd,
    sectionalEarly: r.es,
    sectionalMid: r.ms,
    sectionalLate: r.ls,
    sectionalTotal: r.ts,
    weightTrend: r.wtr,
    distanceStarts: r.ds,
    distanceWins: r.dw,
    distancePlaces: r.dp,
    wprAtDistance: r.wd,
    goingBreakdown: toGoingBreakdown(r.gb),
    formString: r.fm,
    marginFinish: r.mgnL,
    avgSettledPos: r.asp,

    wprLast1: r.wpr1,
    wprAvgLast3: r.wpra,
    wprTrend: r.wprt,
    wprPeakRank1Yr: r.wprp,
    wprNett: r.w,
    weightCarried: r.wt,
    jockeyWinPct90d: r.jw,
    trainerWinPct365d: r.tw,
    jockeyRating: r.jrt,
    trainerRating: r.trt,

    fixedWinPrice: r.fx,
    openFixedPrice: r.op,
    priceSeries: series.map(([mins, price]) => ({ minutesSinceOpen: mins, price })),
    silkUrl: r.sk,
    startingPrice: r.sp,
    postRaceTopPrice: r.top,
    finishPosition: r.f,
    won: r.won === 1,
    fieldSize: r.fs,
    dataScratched: r.scr === 1,

    projectedWpr: r.wpjp,
    baseWpr: r.wpjb,
    wprAdjustment: r.wpjadj,
    adjustmentBreakdown: r.wpjcb,
    projectionConfidence: r.wpjc,
    wprPrice: r.wpjpr,
    wprRank: r.wpjr,
    peakWpr: r.wpjpk,
    projectedWprAltGoing: r.wpjpA,
    projectionConfidenceAltGoing: r.wpjcA,
    projectionDescription: r.wpjd,

    actualWpr: r.wpja,
    actualWprRank: r.wpjar,

    commentsVideo: r.cmtV,
    commentsSteward: r.cmtS,

    missCategory: r.wpjmc,
    missReason: r.wpjmr,

    recentRuns: (r.formRuns ?? []).map(toFormRun),
    peakRun: r.peakRun ? toFormRun(r.peakRun) : null,
    formHistory: (r.formAll ?? []).map(toFormHistoryEntry),
    predictedSettlingBand: r.psBand,
    againstShapeTendency: r.asTend,
  }
}

function toRace(r: RawRace, priceHist: RawDashboardPayload['PRICE_HIST'] | undefined): Race {
  return {
    raceId: r.race_id,
    date: r.date,
    venue: r.venue,
    state: r.state,
    raceNumber: r.race,
    raceName: r.race_name,
    distance: r.distance,
    going: r.going,
    trackGrading: r.track_grading,
    rail: r.rail,
    prizeMoney: r.prize,
    startTime: r.start_time,
    raceShapeEarly: r.rse,
    raceShapeMid: r.rsm,
    raceShapeLate: r.rsl,
    paceEstimateScore: r.rs_score,
    paceEstimateLabel: r.rs_label,
    hasFirstStarter: r.hfs === 1,
    fieldSize: r.fs,
    allResulted: r.done === 1,
    runners: r.runners.map((rr) => toRunner(rr, priceHist)),
  }
}

function toPriceHistoryEntry(
  raw: RawDashboardPayload['PRICE_HIST'][string],
): PriceHistoryEntry {
  return {
    openPrice: raw.o,
    openAt: raw.oat,
    resultPrice: raw.r,
    resultAt: raw.rat,
    sampleCount: raw.n,
  }
}

// Entry point: raw fetched payload -> clean domain data the UI consumes.
// PICKS_TODAY/SETTLED/MODEL_META/MODEL_PICKS/ALL_PICKS_FLAT/PRIMARY_KEY are
// deliberately NOT mapped - confirmed always empty in the current payload
// (bet selection is manual, per CLAUDE.md), so there is nothing there for
// Phase 1 to consume. If that changes, add the mapping then, not preemptively.
export function adaptDashboardPayload(
  raw: RawDashboardPayload,
): DashboardData {
  const priceHistory: Record<string, PriceHistoryEntry> = {}
  for (const [runId, entry] of Object.entries(raw.PRICE_HIST ?? {})) {
    priceHistory[runId] = toPriceHistoryEntry(entry)
  }
  return {
    races: raw.RACES.map((r) => toRace(r, raw.PRICE_HIST)),
    priceHistory,
    runDate: raw.RUN_DATE,
    runIso: raw.RUN_ISO,
    githubRepo: raw.GITHUB_REPO,
    priceBeta: raw.PRICE_BETA,
  }
}
