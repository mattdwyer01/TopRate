import type { FormHistoryEntry, Race, Runner } from '../types/domain'
import { goingBand } from './pace'

export interface CareerStatRow {
  label: string
  runs: number
  peak: number | null
  p75: number | null
  vsBase: number | null
  // WPR values in chronological order (oldest first) for a trend sparkline.
  trend: number[]
}

// Same campaign/spell definition as the backend model (wpr_projection.py
// _SPELL_GAP_DAYS) - a gap longer than this between runs starts a new prep,
// so "this prep" (and first-up/second-up below) mean the same thing the
// projection's own runs_this_camp/first_up features mean.
const SPELL_GAP_DAYS = 60
const MS_PER_DAY = 86_400_000

// Linear-interpolation percentile (numpy's default method) - degrades
// gracefully to a single value at n=1, unlike "2nd best run" which is
// undefined below n=2. Preferred over a plain average: a mean gets dragged
// down by early-prep or bad-luck runs, understating what the horse has
// actually shown it can do in a condition: a robust read on its upper
// range of form rather than everything it's ever done blended together.
function percentile(sortedAsc: number[], p: number): number | null {
  if (!sortedAsc.length) return null
  if (sortedAsc.length === 1) return sortedAsc[0]
  const idx = (p / 100) * (sortedAsc.length - 1)
  const lo = Math.floor(idx)
  const hi = Math.ceil(idx)
  if (lo === hi) return sortedAsc[lo]
  return sortedAsc[lo] + (sortedAsc[hi] - sortedAsc[lo]) * (idx - lo)
}

function sortedWprs(entries: FormHistoryEntry[]): { dated: FormHistoryEntry[]; wprs: number[] } {
  const dated = entries
    .filter((e) => e.wpr != null && e.date)
    .slice()
    .sort((a, b) => a.date.localeCompare(b.date))
  return { dated, wprs: dated.map((e) => e.wpr as number) }
}

function buildRow(label: string, entries: FormHistoryEntry[], baseWpr: number | null): CareerStatRow {
  const { wprs } = sortedWprs(entries)
  const sorted = [...wprs].sort((a, b) => a - b)
  const p75 = percentile(sorted, 75)
  return {
    label,
    runs: wprs.length,
    peak: wprs.length ? Math.max(...wprs) : null,
    p75,
    vsBase: p75 != null && baseWpr != null ? p75 - baseWpr : null,
    trend: wprs,
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

// Peak/upper-range WPR across career and several conditions relevant to
// today's race, each with how that slice compares to the model's own base
// rating - a quick "is this a career-best ask, or within its normal range"
// read, distinct from ComparisonGrid's condition-suitability tables below
// it. First-up/second-up only appears when it actually applies to today's
// race - showing it for every other runner would just be noise.
export function computeCareerStats(runner: Runner, race: Race): CareerStatRow[] {
  const history = runner.formHistory
  const baseWpr = runner.baseWpr
  const distLo = race.distance * 0.9
  const distHi = race.distance * 1.1
  const goingToday = goingBand(race.going)
  const yearToday = new Date(race.date).getFullYear()
  const sixMonthsAgo = new Date(race.date)
  sixMonthsAgo.setMonth(sixMonthsAgo.getMonth() - 6)
  const sixMonthsAgoMs = sixMonthsAgo.getTime()

  const rows = [
    buildRow('Career', history, baseWpr),
    buildRow(`${race.distance}m`, history.filter((e) => e.distance >= distLo && e.distance <= distHi), baseWpr),
    buildRow(goingToday ?? race.going, history.filter((e) => goingBand(e.going) === goingToday), baseWpr),
    buildRow('This prep', thisPrepEntries(history, race.date), baseWpr),
    buildRow('This year', history.filter((e) => new Date(e.date).getFullYear() === yearToday), baseWpr),
    buildRow('Last 6mo', history.filter((e) => new Date(e.date).getTime() >= sixMonthsAgoMs), baseWpr),
  ]

  const status = todayCampaignStatus(history, race.date)
  if (status != null) {
    const label = status === 'first-up' ? 'First-up' : 'Second-up'
    rows.push(buildRow(label, campaignHistoryEntries(history, status), baseWpr))
  }

  return rows
}
