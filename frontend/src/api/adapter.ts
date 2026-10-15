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

export function toFormRun(r: RawFormRun): FormRun {
  return {
    track: r.trk,
    distance: r.dist,
    going: r.go,
    finishPosition: r.fin ?? null,
    wpr: r.wpr,
    // null-valued keys are left out of the payload (toprate_daily._slim_payload), so every nullable field is read with ?? null
    raceShapeEarly: r.se ?? null,
    raceShapeMid: r.sm ?? null,
    raceShapeLate: r.sl ?? null,
    sectionalEarly: r.ie ?? null,
    sectionalTo800: r.im ?? null,
    sectionalLate600: r.il ?? null,
    sectionalLate200: r.i2 ?? null,
    barrier: r.bar ?? null,
    margin: r.mgn ?? null,
    positionSettled: r.psl ?? null,
    position800m: r.p8 ?? null,
    position400m: r.p4 ?? null,
    raceClass: r.cls ?? null,
    jockey: r.jck ?? null,
    isPeakRun: r.pk === 1,
    date: r.d,
    weight: r.wt ?? null,
    startingPrice: r.sp ?? null,
    raceNumber: r.rn ?? null,
  }
}

function toFormHistoryEntry(r: RawFormAllEntry): FormHistoryEntry {
  return {
    wpr: r.w,
    going: r.go,
    distance: r.ds,
    tempo: (r.tmp ?? null) as FormHistoryEntry['tempo'],
    relativeSettlePosition: r.rel ?? null,
    date: r.d,
    isVoid: r.void === true,
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

    atwOffset: r.atwo ?? null,
    resultsScaleOffset: r.rso ?? null,
    goingBreakdown: toGoingBreakdown(r.gb),
    marginFinish: r.mgnL,
    avgSettledPos: r.asp,

    weightCarried: r.wt,
    jockeyWinPct90d: r.jw,
    trainerWinPct365d: r.tw,
    jockeyStarts90d: r.jwN,
    trainerStarts365d: r.twN,

    fixedWinPrice: r.fx,
    openFixedPrice: r.op,
    priceSeries: series.map(([mins, price]) => ({ minutesSinceOpen: mins, price })),
    silkUrl: r.sk,
    startingPrice: r.sp,
    postRaceTopPrice: r.top,
    finishPosition: r.f,
    won: r.won === 1,
    resultKnown: r.f != null || r.won != null,
    fieldSize: r.fs,
    dataScratched: r.scr === 1,

    projectedWpr: r.wpjp,
    baseWpr: r.wpjb,
    wprAdjustment: r.wpjadj,
    adjustmentBreakdown: r.wpjcb,
    nett: r.wn ?? null,
    projectionSd: r.wpjsd ?? null,
    projectionMade: r.wpjmd ?? null,
    projectionModel: r.wpjm === 'main' || r.wpjm === 'light' ? r.wpjm : null,
    wprPrice: r.wpjpr,
    wprRank: r.wpjr,
    peakWpr: r.wpjpk,
    edge: r.wpje,
    projectionDescription: r.wpjd,

    actualWpr: r.wpja,
    actualWprRank: r.wpjar,

    commentsVideo: r.cmtV,
    commentsSteward: r.cmtS,


    recentRuns: (r.formRuns ?? []).map(toFormRun),
    peakRun: r.peakRun ? toFormRun(r.peakRun) : null,
    formHistory: (r.formAll ?? []).map(toFormHistoryEntry),
    predictedSettlingBand: r.psBand,
    predictedRelSettle: r.psr,
  }
}

export function toRace(r: RawRace, priceHist: RawDashboardPayload['PRICE_HIST'] | undefined): Race {
  const runners = r.runners.map((rr) => toRunner(rr, priceHist))
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
    // From the field itself (the payload's hfs flag was true for almost every race): a runner still in the race with no rated run.
    hasFirstStarter: runners.some((x) => !x.dataScratched && x.formHistory.length === 0),
    fieldSize: r.fs,
    allResulted: r.done === 1,
    provisional: r.prov === 1,
    runners,
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
    historyIso: raw.HISTORY_ISO,
  }
}
