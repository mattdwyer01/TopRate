import type { FormHistoryEntry, Race, Runner } from '../types/domain'
import { goingBand } from './pace'

export interface CareerStatRow {
  label: string
  runs: number
  peak: number | null
  avg: number | null
  vsCareerAvg: number | null
  // WPR values in chronological order (oldest first) for a trend sparkline.
  trend: number[]
  // The wpr_projection.py ADJ_TERMS key this row's condition maps to, if
  // any (e.g. the distance row -> own_distance) - lets the UI show the
  // shrunk/capped adjustment actually applied alongside the raw vsCareerAvg
  // delta, in the same row, instead of a separate table.
  adjKey?: string
}

// Same campaign/spell definition as the backend model (wpr_projection.py
// _SPELL_GAP_DAYS) - a gap longer than this between runs starts a new prep,
// so "this prep" (and first-up/second-up below) mean the same thing the
// projection's own runs_this_camp/first_up features mean.
const SPELL_GAP_DAYS = 60
const MS_PER_DAY = 86_400_000

function sortedWprs(entries: FormHistoryEntry[]): { dated: FormHistoryEntry[]; wprs: number[] } {
  const dated = entries
    .filter((e) => e.wpr != null && e.date)
    .slice()
    .sort((a, b) => a.date.localeCompare(b.date))
  return { dated, wprs: dated.map((e) => e.wpr as number) }
}

function mean(values: number[]): number | null {
  return values.length ? values.reduce((s, v) => s + v, 0) / values.length : null
}

// vsCareerAvg = avg(this condition's runs) - avg(every run) - the same
// quantity (and the same reasoning: does this horse personally run better
// or worse here, using only its own history) as the backend's own_distance/
// own_going adjustment terms, just unshrunk and over a broader set of
// descriptive conditions than the 6 that actually feed the projection. See
// AdjustmentBreakdown for the shrunk/capped version of the subset they share.
function buildRow(
  label: string,
  entries: FormHistoryEntry[],
  careerAvg: number | null,
  adjKey?: string,
): CareerStatRow {
  const { wprs } = sortedWprs(entries)
  const avg = mean(wprs)
  return {
    label,
    runs: wprs.length,
    peak: wprs.length ? Math.max(...wprs) : null,
    avg,
    vsCareerAvg: avg != null && careerAvg != null ? avg - careerAvg : null,
    trend: wprs,
    adjKey,
  }
}

// Runs since the horse's last spell of SPELL_GAP_DAYS+ - empty if it's
// currently first-up (the gap from its last run to today's race already
// exceeds that threshold), matching how the model itself would see it.
function thisPrepEntries(history: FormHistoryEntry[], raceDate: string): FormHistoryEntry[] {
  const { dated } = sortedWprs(history)
  if (!dated.length) return []

  const raceTime = new Date(raceDate).getTime()
  const lastRunTime = new Date(dated[dated.length - 1].date).getTime()
  if ((raceTime - lastRunTime) / MS_PER_DAY > SPELL_GAP_DAYS) return []

  const campaign = [dated[dated.length - 1]]
  for (let i = dated.length - 2; i >= 0; i--) {
    const gapDays = (new Date(dated[i + 1].date).getTime() - new Date(dated[i].date).getTime()) / MS_PER_DAY
    if (gapDays > SPELL_GAP_DAYS) break
    campaign.push(dated[i])
  }
  return campaign
}

// Whether TODAY's race is this horse's first-up or second-up run of its
// current prep, from the same runs-this-campaign logic as thisPrepEntries -
// zero prior runs this prep means today is first-up, exactly one means
// today is second-up.
export function todayCampaignStatus(history: FormHistoryEntry[], raceDate: string): 'first-up' | 'second-up' | null {
  const runsThisPrep = thisPrepEntries(history, raceDate)
  if (runsThisPrep.length === 0) return 'first-up'
  if (runsThisPrep.length === 1) return 'second-up'
  return null
}

// This horse's own PAST runs that were themselves first-up (a gap of
// SPELL_GAP_DAYS+ since its prior run - a true debut doesn't count, since
// "first-up" in racing usage specifically means back from a spell, not a
// first-ever start) or second-up (the run immediately following one of
// those). Used to show "how has this horse gone first/second-up before",
// only when today is itself a first-up or second-up run for it.
function campaignHistoryEntries(history: FormHistoryEntry[], status: 'first-up' | 'second-up'): FormHistoryEntry[] {
  const { dated } = sortedWprs(history)
  const result: FormHistoryEntry[] = []
  let prevWasFirstUp = false
  for (let i = 1; i < dated.length; i++) {
    const gapDays = (new Date(dated[i].date).getTime() - new Date(dated[i - 1].date).getTime()) / MS_PER_DAY
    const isFirstUp = gapDays > SPELL_GAP_DAYS
    if (status === 'first-up' && isFirstUp) result.push(dated[i])
    else if (status === 'second-up' && !isFirstUp && prevWasFirstUp) result.push(dated[i])
    prevWasFirstUp = isFirstUp
  }
  return result
}

// Peak WPR and average-vs-career-average across career and several
// conditions relevant to today's race - "does this horse personally run
// better or worse here", the same question (and the same underlying
// calculation) as the backend's own_distance/own_going adjustment terms,
// just unshrunk and over more conditions than the 6 that actually feed the
// projection (see AdjustmentBreakdown for that shrunk/capped subset).
// Distinct from ComparisonGrid's condition-suitability tables below it,
// which ask a narrower question about today's specific pace/settle shape.
// First-up/second-up only appears when it actually applies to today's
// race - showing it for every other runner would just be noise.
export function computeCareerStats(runner: Runner, race: Race): CareerStatRow[] {
  const history = runner.formHistory
  const careerAvg = mean(sortedWprs(history).wprs)
  const goingToday = goingBand(race.going)
  const sixMonthsAgo = new Date(race.date)
  sixMonthsAgo.setMonth(sixMonthsAgo.getMonth() - 6)
  const sixMonthsAgoMs = sixMonthsAgo.getTime()

  // "This year" (calendar-year cutoff) was dropped - on most of the
  // calendar it's near-identical to "Last 6mo" (a rolling window, and a
  // more meaningful boundary than an arbitrary Jan 1 reset), so it was
  // mostly repeating the row above it rather than adding a read.
  const rows = [
    buildRow('Career', history, careerAvg),
    buildRow(
      `${race.distance}m`,
      // Exact match, not a +/-10% band - matches wpr_projection.py's own
      // own_distance term exactly (switched from a band to an exact match
      // Aug 2026, validated as more accurate: see that function's own
      // docstring). This row used to use the old band logic and drifted
      // out of sync with the backend when that change shipped - found
      // Sep 2026 when a horse's displayed distance-row stats (5 runs)
      // didn't match its own projection description's own figure (2 runs).
      history.filter((e) => e.distance === race.distance),
      careerAvg,
      'own_distance',
    ),
    buildRow(
      goingToday ?? race.going,
      history.filter((e) => goingBand(e.going) === goingToday),
      careerAvg,
      'own_going',
    ),
    buildRow('This prep', thisPrepEntries(history, race.date), careerAvg),
    buildRow('Last 6mo', history.filter((e) => new Date(e.date).getTime() >= sixMonthsAgoMs), careerAvg),
  ]

  const status = todayCampaignStatus(history, race.date)
  if (status != null) {
    const label = status === 'first-up' ? 'First-up' : 'Second-up'
    const adjKey = status === 'first-up' ? 'own_first_up' : 'own_second_up'
    rows.push(buildRow(label, campaignHistoryEntries(history, status), careerAvg, adjKey))
  }

  return rows
}
