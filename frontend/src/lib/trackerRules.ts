import type { Race, Runner } from '../types/domain'
import { bushMeetingKeys, meetingKey } from './meetings'

// Client-side port of speedmap_jockey_tracker.py's build_candidates() - see
// that file's own docstring for the full rule and the backtest that
// justified solo-only (a race with 2+ base-rule qualifiers silences Tracker
// A entirely; Tracker B's rating-agreement condition is checked against its
// own, independent solo requirement). Kept in exact lockstep with it: same
// thresholds, same field mapping (wpjcb.speed_map -> adjustmentBreakdown.
// speed_map, sp-or-fx -> startingPrice ?? fixedWinPrice, etc) - including
// that solo-only is checked BEFORE price (Sep 2026): a second runner
// meeting speed_map/gap/jw but priced under PRICE_MIN still means the race
// wasn't genuinely uncontested, so it counts toward the solo check even
// though it wouldn't itself qualify.
//
// WHY THIS EXISTS SEPARATELY FROM THE CSV LOG THE TRACKERS TAB READS: that
// log is only written when speedmap_jockey_tracker.py runs, which is once
// per daily.yml trigger (a handful of fixed times a day, see that
// workflow's own cron comment) - a runner whose price only crosses $3, or
// whose gap-to-top only closes to <=6, in between two triggers doesn't get
// logged until the NEXT one fires, which can be after it's already jumped
// (real user feedback, 2026-09-16: "tracker does not showing upcoming
// bets"). This function runs against whatever's CURRENTLY loaded in
// toprate_data.json (refreshed every 5 min by price_refresh.yml, or by the
// user's own "Fetch data" button), so it reflects a qualifying runner
// immediately - both for the race summary's own live flag and for the
// Trackers tab's "not yet logged" section.
export type TrackerTag = 'favoured' | 'neutral'

export interface TrackerQualifier {
  runId: string
  tag: TrackerTag
  gapWpr: number
  jw: number
  price: number | null
  qualifiesA: boolean
  qualifiesB: boolean
  // True when this runner meets Tracker A's/B's tactical criteria but the
  // tracker doesn't fire for this race because 2+ runners do (solo-only
  // failed on the base criteria, independent of any of their prices - see
  // this file's own note above). Real user feedback (2026-09-16): "for
  // those races with more than 1 horse that fits the criteria, these
  // should be flagged as such" - this is that flag, distinct from
  // qualifiesA/B (an actual, firing pick) since a contested runner never
  // produces a pick.
  contestedA: boolean
  contestedB: boolean
}

const DEMEAN_THRESHOLD = 0.5 // matches SpeedMapGrid.tsx's THREAT_THRESHOLD
const GAP_MAX = 6.0
const JW_MIN = 14.0
const PRICE_MIN = 3.0

function rankDesc(value: number | null, allValues: (number | null)[]): number | null {
  if (value == null) return null
  return 1 + allValues.filter((v) => v != null && v > value).length
}

interface RaceQualifier {
  runner: Runner
  tag: TrackerTag
  gap: number
  jw: number
  price: number | null
}

// Every runner in `race` that qualifies for Tracker A (high volume) and/or
// Tracker B (low volume, also #1 in-race by both TopRate rating and
// form-factor) - keyed by runId. isBush: pass bushMeetingKeys(allRaces).has
// (meetingKey(race)) - a bush/picnic meeting never qualifies (see
// speedmap_jockey_tracker.py's own BUSH_TRACK_THRESHOLD).
export function evaluateTrackerQualifiers(race: Race, isBush: boolean): Map<string, TrackerQualifier> {
  const result = new Map<string, TrackerQualifier>()
  if (isBush) return result

  const runners = race.runners.filter((u) => !u.dataScratched)
  const valid: [Runner, number][] = []
  for (const u of runners) {
    const sm = u.adjustmentBreakdown?.speed_map
    if (sm != null) valid.push([u, sm])
  }
  if (valid.length < 2) return result
  const raceMean = valid.reduce((sum, [, sm]) => sum + sm, 0) / valid.length

  const trrVals = runners.map((u) => u.toprateRating)
  const pfmVals = runners.map((u) => u.formFactor)
  const topWpr = runners.reduce<number | null>((max, u) => {
    const v = u.projectedWpr
    return v != null && (max == null || v > max) ? v : max
  }, null)

  const raceQualifiers: RaceQualifier[] = []
  for (const [runner, sm] of valid) {
    const demeaned = sm - raceMean
    if (demeaned <= -DEMEAN_THRESHOLD) continue // unfavoured - never qualifies
    const tag: TrackerTag = demeaned >= DEMEAN_THRESHOLD ? 'favoured' : 'neutral'

    const wpjp = runner.projectedWpr
    if (wpjp == null || topWpr == null) continue
    const gap = topWpr - wpjp
    if (gap > GAP_MAX) continue

    const jw = runner.jockeyWinPct90d
    if (jw == null || jw < JW_MIN) continue

    // Price is deliberately NOT filtered here (Sep 2026) - solo-only means
    // unique on the TACTICAL/rating criteria alone. See this file's own
    // note above and speedmap_jockey_tracker.py's matching comment: a
    // second runner meeting speed_map/gap/jw but priced under PRICE_MIN
    // still means the race wasn't genuinely uncontested (backtest: such
    // "shadow"-affected picks returned roughly half the ROI of genuinely
    // solo ones). PRICE_MIN is applied further below, only to the lone
    // qualifier that survives the solo-only check.
    const price = runner.startingPrice ?? runner.fixedWinPrice
    raceQualifiers.push({ runner, tag, gap, jw, price })
  }
  if (raceQualifiers.length === 0) return result

  const bPool: string[] = []
  const infoByRid = new Map<string, RaceQualifier & { trrRank: number | null; pfmRank: number | null }>()
  for (const q of raceQualifiers) {
    const trrRank = rankDesc(q.runner.toprateRating, trrVals)
    const pfmRank = rankDesc(q.runner.formFactor, pfmVals)
    infoByRid.set(q.runner.runId, { ...q, trrRank, pfmRank })
    if (trrRank === 1 && pfmRank === 1) bPool.push(q.runner.runId)
  }

  // Solo-only is checked above, price-independent - PRICE_MIN is applied
  // here, only to the lone survivor, to decide whether that tracker
  // actually fires for this race. A solo qualifier priced under PRICE_MIN
  // silences that tracker for this race entirely; it does NOT fall
  // through to a "next" qualifier, because solo-only already established
  // there isn't one.
  const soloA = raceQualifiers.length === 1 ? raceQualifiers[0] : null
  const includeARid = soloA != null && soloA.price != null && soloA.price >= PRICE_MIN ? soloA.runner.runId : null
  // Contested: 2+ runners meet A's tactical criteria, price aside - every
  // one of them gets contestedA, not just whichever happens to be
  // shortest/longest priced (there's no "the" contender to single out).
  const contestedARids = new Set(raceQualifiers.length > 1 ? raceQualifiers.map((q) => q.runner.runId) : [])

  const soloBRid = bPool.length === 1 ? bPool[0] : null
  const soloBPrice = soloBRid != null ? infoByRid.get(soloBRid)!.price : null
  const includeBRid = soloBRid != null && soloBPrice != null && soloBPrice >= PRICE_MIN ? soloBRid : null
  const contestedBRids = new Set(bPool.length > 1 ? bPool : [])

  const allRids = new Set<string>([
    ...(includeARid != null ? [includeARid] : []),
    ...(includeBRid != null ? [includeBRid] : []),
    ...contestedARids,
    ...contestedBRids,
  ])

  for (const rid of allRids) {
    const info = infoByRid.get(rid)!
    result.set(rid, {
      runId: rid,
      tag: info.tag,
      gapWpr: info.gap,
      jw: info.jw,
      price: info.price,
      qualifiesA: rid === includeARid,
      qualifiesB: rid === includeBRid,
      contestedA: contestedARids.has(rid),
      contestedB: contestedBRids.has(rid),
    })
  }
  return result
}

// Shape mirrors speedmap_jockey_tracker.py's LOG_COLUMNS / TrackersTab's own
// TrackerRow, so a live candidate can be rendered by the exact same card
// component as a logged one - resulted/finishPosition/won/priceFinal come
// straight off the runner (already resulted post-race, whether or not the
// CSV log has reconciled it yet).
export interface TrackerCandidateRow {
  runId: string
  raceId: string
  date: string
  venue: string
  raceNo: number
  startTime: string
  tab: number
  horse: string
  silkUrl: string
  tag: TrackerTag
  wprPrediction: number | null
  gapWpr: number
  toprateRating: number | null
  formFactor: number | null
  jw: number
  priceAtPick: number | null
  resulted: boolean
  finishPosition: number | null
  won: boolean
  priceFinal: number | null
}

// Every live-qualifying runner across every non-bush race on `targetDate` -
// not filtered against the CSV log (the caller does that, since only it
// knows which runIds are already logged).
export function liveTrackerCandidates(
  races: Race[],
  targetDate: string,
): { high: TrackerCandidateRow[]; low: TrackerCandidateRow[] } {
  const bushKeys = bushMeetingKeys(races)
  const high: TrackerCandidateRow[] = []
  const low: TrackerCandidateRow[] = []
  for (const race of races) {
    if (race.date !== targetDate) continue
    const isBush = bushKeys.has(meetingKey(race))
    const qualifiers = evaluateTrackerQualifiers(race, isBush)
    if (qualifiers.size === 0) continue
    for (const [runId, q] of qualifiers) {
      const runner = race.runners.find((r) => r.runId === runId)
      if (!runner) continue
      const row: TrackerCandidateRow = {
        runId,
        raceId: race.raceId,
        date: race.date,
        venue: race.venue,
        raceNo: race.raceNumber,
        startTime: race.startTime,
        tab: runner.tabNumber,
        horse: runner.horse,
        silkUrl: runner.silkUrl ?? '',
        tag: q.tag,
        wprPrediction: runner.projectedWpr,
        gapWpr: q.gapWpr,
        toprateRating: runner.toprateRating,
        formFactor: runner.formFactor,
        jw: q.jw,
        priceAtPick: q.price,
        resulted: runner.finishPosition != null,
        finishPosition: runner.finishPosition,
        won: runner.won,
        priceFinal: runner.startingPrice ?? runner.fixedWinPrice,
      }
      if (q.qualifiesA) high.push(row)
      if (q.qualifiesB) low.push(row)
    }
  }
  return { high, low }
}

// One contested runner - the display-ready subset of TrackerQualifier a
// contested-group card actually needs.
export interface ContestedRunner {
  runId: string
  tab: number
  horse: string
  tag: TrackerTag
  gapWpr: number
  jw: number
  price: number | null
}

export interface ContestedGroup {
  raceId: string
  date: string
  venue: string
  raceNo: number
  startTime: string
  runners: ContestedRunner[]
}

// Every race on `targetDate` where Tracker A and/or B's solo-only check
// failed on 2+ runners (see evaluateTrackerQualifiers' own contestedA/B
// comment) - one group per race, per tracker, listing every runner that
// contributed to the contest. Powers the Trackers tab's "Contested races"
// section (real user feedback, 2026-09-16): these races produce no pick at
// all, so they'd otherwise be invisible anywhere in the app.
export function contestedTrackerGroups(
  races: Race[],
  targetDate: string,
): { high: ContestedGroup[]; low: ContestedGroup[] } {
  const bushKeys = bushMeetingKeys(races)
  const high: ContestedGroup[] = []
  const low: ContestedGroup[] = []
  for (const race of races) {
    if (race.date !== targetDate) continue
    const isBush = bushKeys.has(meetingKey(race))
    const qualifiers = evaluateTrackerQualifiers(race, isBush)
    if (qualifiers.size === 0) continue

    const contestedA: ContestedRunner[] = []
    const contestedB: ContestedRunner[] = []
    for (const [runId, q] of qualifiers) {
      const runner = race.runners.find((r) => r.runId === runId)
      if (!runner) continue
      const entry: ContestedRunner = {
        runId,
        tab: runner.tabNumber,
        horse: runner.horse,
        tag: q.tag,
        gapWpr: q.gapWpr,
        jw: q.jw,
        price: q.price,
      }
      if (q.contestedA) contestedA.push(entry)
      if (q.contestedB) contestedB.push(entry)
    }

    const base = {
      raceId: race.raceId,
      date: race.date,
      venue: race.venue,
      raceNo: race.raceNumber,
      startTime: race.startTime,
    }
    if (contestedA.length > 0) high.push({ ...base, runners: contestedA })
    if (contestedB.length > 0) low.push({ ...base, runners: contestedB })
  }
  return { high, low }
}
