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
  // True when this runner is the ONLY one meeting the tactical criteria
  // (solo-only passes) but its own price is under PRICE_MIN, so the
  // tracker still doesn't fire - a different reason than contestedA/B
  // (no rival qualifier at all, just too short) that real user feedback
  // (2026-09-16) asked to also surface: "show if there is a solo pick
  // under $3 in a race too".
  underPriceA: boolean
  underPriceB: boolean
}

const DEMEAN_THRESHOLD = 0.5 // matches SpeedMapGrid.tsx's THREAT_THRESHOLD
// Lowered 6 -> 4 (Sep 2026) - see speedmap_jockey_tracker.py's matching
// constant for the re-sweep that picked 4 (post the solo-only-before-price
// fix, which changed the qualifying population enough that the old
// 6-picking sweep no longer applies). Raised 4 -> 5 (Sep 2026, real user
// decision made explicitly against the backtest's own recommendation -
// see speedmap_jockey_tracker.py's matching constant for the numbers).
const GAP_MAX = 5.0
// REPLACED the old absolute jockey_win_pct_90d floor (14 -> 20 -> back to
// 14, see git history) entirely with a race-relative rank (Sep 2026, real
// user proposal: "top x% of jockey sr in the race... floor of at least
// above 10%") - see speedmap_jockey_tracker.py's matching constants for
// the full backtest (top 10% beat the old absolute floor on win%, ROI,
// AND volume simultaneously for Tracker A).
const JW_FLOOR = 10.0
const JW_RELATIVE_TOP_PCT = 10
// jockey_starts_90d floor - see speedmap_jockey_tracker.py's matching
// constant for the full reasoning. null passes rather than fails (most
// runners don't have a real count yet - this is a near no-op today,
// confirmed against the live data, and only starts filtering as more
// days accumulate real counts).
const JW_STARTS_MIN = 25
const PRICE_MIN = 3.0
// A multi-selection (contested) race still fires - on every qualifier in
// it - if all of them are priced above this floor. See
// speedmap_jockey_tracker.py's matching CONTESTED_PRICE_FLOOR comment for
// the backtest that motivated this and its caveat (doesn't fully survive
// an outlier-robustness check; implemented per explicit user decision,
// same as the GAP_MAX 6->4 call).
const CONTESTED_PRICE_FLOOR = 6.0

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
  // Whole field's jw, not just runners already past speed_map/gap - see
  // speedmap_jockey_tracker.py's matching JW_RELATIVE_TOP_PCT comment.
  const jwField = runners.map((u) => u.jockeyWinPct90d).filter((v): v is number => v != null)
  const jwCutoffRank = Math.max(1, Math.round((jwField.length * JW_RELATIVE_TOP_PCT) / 100))

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
    if (jw == null || jw <= JW_FLOOR) continue
    if ((rankDesc(jw, jwField) ?? Infinity) > jwCutoffRank) continue

    // jockeyStarts90d: null passes rather than fails - see
    // speedmap_jockey_tracker.py's matching JW_STARTS_MIN comment.
    const jwStarts = runner.jockeyStarts90d
    if (jwStarts != null && jwStarts < JW_STARTS_MIN) continue

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
  const includeARids = new Set<string>()
  if (soloA != null) {
    if (soloA.price != null && soloA.price >= PRICE_MIN) includeARids.add(soloA.runner.runId)
  } else if (raceQualifiers.length > 1) {
    // Multi-selection floor exception (see CONTESTED_PRICE_FLOOR above) -
    // only fires when EVERY qualifier clears it, not just the
    // shortest-priced one; otherwise the race stays contested (silent)
    // exactly as before.
    if (raceQualifiers.every((q) => q.price != null && q.price > CONTESTED_PRICE_FLOOR)) {
      for (const q of raceQualifiers) includeARids.add(q.runner.runId)
    }
  }
  // Solo, but priced under PRICE_MIN - a different non-fire reason than
  // contested (there's no rival qualifier at all here, just a price too
  // short to bet).
  const underPriceARid = soloA != null && includeARids.size === 0 ? soloA.runner.runId : null
  // Contested: 2+ runners meet A's tactical criteria and the multi-selection
  // floor above didn't clear (still no fire) - every one of them gets
  // contestedA, not just whichever happens to be shortest/longest priced.
  const contestedARids = new Set(
    raceQualifiers.length > 1 && includeARids.size === 0 ? raceQualifiers.map((q) => q.runner.runId) : [],
  )

  const soloBRid = bPool.length === 1 ? bPool[0] : null
  const includeBRids = new Set<string>()
  if (soloBRid != null) {
    const soloBPrice = infoByRid.get(soloBRid)!.price
    if (soloBPrice != null && soloBPrice >= PRICE_MIN) includeBRids.add(soloBRid)
  } else if (bPool.length > 1) {
    if (bPool.every((rid) => {
      const p = infoByRid.get(rid)!.price
      return p != null && p > CONTESTED_PRICE_FLOOR
    })) {
      for (const rid of bPool) includeBRids.add(rid)
    }
  }
  const underPriceBRid = soloBRid != null && includeBRids.size === 0 ? soloBRid : null
  const contestedBRids = new Set(bPool.length > 1 && includeBRids.size === 0 ? bPool : [])

  const allRids = new Set<string>([
    ...includeARids,
    ...includeBRids,
    ...(underPriceARid != null ? [underPriceARid] : []),
    ...(underPriceBRid != null ? [underPriceBRid] : []),
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
      qualifiesA: includeARids.has(rid),
      qualifiesB: includeBRids.has(rid),
      contestedA: contestedARids.has(rid),
      contestedB: contestedBRids.has(rid),
      underPriceA: rid === underPriceARid,
      underPriceB: rid === underPriceBRid,
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
  // Set only by pendingWatchCandidates() below - undefined for a genuine
  // qualifying candidate from liveTrackerCandidates(). Real user request
  // (2026-09-17): a race that's merely contested or under $3 RIGHT NOW,
  // but hasn't run yet, shouldn't drop into "skipped" - price and the
  // field can still move before the jump, so it stays a live watch in the
  // main list (in race order) until the race actually resolves one way or
  // the other.
  watchReason?: 'contested' | 'underPrice'
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
        resulted: runner.resultKnown,
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

// Whether a race has actually run, for the pendingWatchCandidates()/
// skippedTrackerGroups() split below - deliberately NOT race.allResulted
// (found 2026-09-17: that flag needs EVERY runner to carry a known f/won,
// including scratches, which never get one - see toprate_daily.py's
// patch_data_json(). A race with any scratch in the field can sit at
// allResulted=false forever even once its winner is fully known, which
// left resulted races - a real one confirmed: Mornington R2, winner Top
// Conti known, four scratches keeping allResulted false - permanently
// stuck showing "Watching" instead of moving to Skipped races). Any ONE
// runner with a known result is enough: the race has run, so every other
// runner's WPR/price inputs are frozen for good at that point regardless
// of whether the fast patch path ever marks the whole race allResulted.
function raceHasRun(race: Race): boolean {
  return race.runners.some((r) => r.resultKnown)
}

// Every runner meeting the tactical criteria but NOT currently firing
// (contested, or a lone qualifier under $3), for a race that HASN'T
// resulted yet - shaped identically to liveTrackerCandidates() so the
// caller can merge both into one chronological list. Real user request
// (2026-09-17): odds move and fields change right up to the jump, so a
// contested/under-$3 runner in a still-upcoming race isn't a settled
// "skip" yet - it belongs in the main list, in race order, same as a
// genuine live candidate, until the race actually runs. Once the race has
// run (raceHasRun above), this function no longer returns it at all -
// skippedTrackerGroups() below takes over from that point.
export function pendingWatchCandidates(
  races: Race[],
  targetDate: string,
): { high: TrackerCandidateRow[]; low: TrackerCandidateRow[] } {
  const bushKeys = bushMeetingKeys(races)
  const high: TrackerCandidateRow[] = []
  const low: TrackerCandidateRow[] = []
  for (const race of races) {
    if (race.date !== targetDate || raceHasRun(race)) continue
    const isBush = bushKeys.has(meetingKey(race))
    const qualifiers = evaluateTrackerQualifiers(race, isBush)
    if (qualifiers.size === 0) continue
    for (const [runId, q] of qualifiers) {
      const runner = race.runners.find((r) => r.runId === runId)
      if (!runner) continue
      const watchReasonA = q.contestedA ? 'contested' : q.underPriceA ? 'underPrice' : null
      const watchReasonB = q.contestedB ? 'contested' : q.underPriceB ? 'underPrice' : null
      if (watchReasonA == null && watchReasonB == null) continue
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
        // raceHasRun(race) is already false here (guaranteed by the
        // continue above, which checks every runner in this race
        // including this one), so these are always still-unresulted
        // defaults - read straight off the runner rather than hardcoded,
        // same as liveTrackerCandidates(), for consistency.
        resulted: runner.resultKnown,
        finishPosition: runner.finishPosition,
        won: runner.won,
        priceFinal: runner.startingPrice ?? runner.fixedWinPrice,
      }
      if (watchReasonA != null) high.push({ ...row, watchReason: watchReasonA })
      if (watchReasonB != null) low.push({ ...row, watchReason: watchReasonB })
    }
  }
  return { high, low }
}

// One runner in a skipped-race group - the display-ready subset of
// TrackerQualifier a card actually needs.
export interface SkippedRunner {
  runId: string
  tab: number
  horse: string
  tag: TrackerTag
  gapWpr: number
  jw: number
  price: number | null
  resulted: boolean
  finishPosition: number | null
  won: boolean
}

export interface SkippedGroup {
  raceId: string
  date: string
  venue: string
  raceNo: number
  startTime: string
  // 'contested': 2+ runners met the tactical criteria, so solo-only
  // failed - runners lists all of them. 'underPrice': exactly one runner
  // met it (solo-only passed) but its own price was under PRICE_MIN -
  // runners has that one entry.
  reason: 'contested' | 'underPrice'
  runners: SkippedRunner[]
}

// Every RESULTED race on `targetDate` where Tracker A and/or B met the
// tactical criteria but still didn't fire a pick - either contested (2+
// runners, see evaluateTrackerQualifiers' own contestedA/B comment) or a
// lone qualifier priced under PRICE_MIN (underPriceA/B). One group per
// race per tracker. Powers the Trackers tab's "Skipped races" section
// (real user feedback, 2026-09-16): these races produce no pick at all,
// so they'd otherwise be invisible anywhere in the app.
//
// Only ever a FINAL verdict, i.e. raceHasRun(race) above - a still-
// upcoming race that's merely contested or under $3 right now belongs to
// pendingWatchCandidates() above instead (real user request, 2026-09-17:
// odds move and fields change before the jump, so that's not a settled
// skip yet). Once the race actually resolves, this function is what takes
// over and calls it a real, final skip. Uses raceHasRun(), not
// race.allResulted - a race can have a fully known winner yet never flip
// allResulted if anything in its field is scratched (see raceHasRun's own
// comment for the real, confirmed case this caused: a resulted race stuck
// showing "Watching" forever instead of moving here).
export function skippedTrackerGroups(
  races: Race[],
  targetDate: string,
): { high: SkippedGroup[]; low: SkippedGroup[] } {
  const bushKeys = bushMeetingKeys(races)
  const high: SkippedGroup[] = []
  const low: SkippedGroup[] = []
  for (const race of races) {
    if (race.date !== targetDate || !raceHasRun(race)) continue
    const isBush = bushKeys.has(meetingKey(race))
    const qualifiers = evaluateTrackerQualifiers(race, isBush)
    if (qualifiers.size === 0) continue

    const contestedA: SkippedRunner[] = []
    const contestedB: SkippedRunner[] = []
    const underPriceA: SkippedRunner[] = []
    const underPriceB: SkippedRunner[] = []
    for (const [runId, q] of qualifiers) {
      const runner = race.runners.find((r) => r.runId === runId)
      if (!runner) continue
      const entry: SkippedRunner = {
        runId,
        tab: runner.tabNumber,
        horse: runner.horse,
        tag: q.tag,
        gapWpr: q.gapWpr,
        jw: q.jw,
        price: q.price,
        resulted: runner.resultKnown,
        finishPosition: runner.finishPosition,
        won: runner.won,
      }
      if (q.contestedA) contestedA.push(entry)
      if (q.contestedB) contestedB.push(entry)
      if (q.underPriceA) underPriceA.push(entry)
      if (q.underPriceB) underPriceB.push(entry)
    }

    const base = {
      raceId: race.raceId,
      date: race.date,
      venue: race.venue,
      raceNo: race.raceNumber,
      startTime: race.startTime,
    }
    if (contestedA.length > 0) high.push({ ...base, reason: 'contested', runners: contestedA })
    if (underPriceA.length > 0) high.push({ ...base, reason: 'underPrice', runners: underPriceA })
    if (contestedB.length > 0) low.push({ ...base, reason: 'contested', runners: contestedB })
    if (underPriceB.length > 0) low.push({ ...base, reason: 'underPrice', runners: underPriceB })
  }
  return { high, low }
}
