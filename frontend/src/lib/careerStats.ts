import type { FormHistoryEntry, Race, Runner } from '../types/domain'
import { goingBand } from './pace'

export interface CareerStatRow {
  label: string
  runs: number
  peak: number | null
  avg: number | null
  vsBase: number | null
}

// Same campaign/spell definition as the backend model (wpr_projection.py
// _SPELL_GAP_DAYS) - a gap longer than this between runs starts a new prep,
// so "this prep" here means the same thing the projection's own
// runs_this_camp/first_up features mean.
const SPELL_GAP_DAYS = 60
const MS_PER_DAY = 86_400_000

function mean(values: number[]): number | null {
  return values.length ? values.reduce((s, v) => s + v, 0) / values.length : null
}

function buildRow(label: string, entries: FormHistoryEntry[], baseWpr: number | null): CareerStatRow {
  const wprs = entries.filter((e) => e.wpr != null).map((e) => e.wpr as number)
  const avg = mean(wprs)
  return {
    label,
    runs: wprs.length,
    peak: wprs.length ? Math.max(...wprs) : null,
    avg,
    vsBase: avg != null && baseWpr != null ? avg - baseWpr : null,
  }
}

// Runs since the horse's last spell of SPELL_GAP_DAYS+ - empty if it's
// currently first-up (the gap from its last run to today's race already
// exceeds that threshold), matching how the model itself would see it.
function thisPrepEntries(history: FormHistoryEntry[], raceDate: string): FormHistoryEntry[] {
  const dated = history
    .filter((e) => e.wpr != null && e.date)
    .slice()
    .sort((a, b) => a.date.localeCompare(b.date))
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

// Peak/average/median WPR across career and several conditions relevant to
// today's race, each with how that slice compares to the model's own base
// rating - a quick "is this a career-best ask, or within its normal range"
// read, distinct from ComparisonGrid's condition-suitability tables below it.
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

  return [
    buildRow('Career', history, baseWpr),
    buildRow(`${race.distance}m`, history.filter((e) => e.distance >= distLo && e.distance <= distHi), baseWpr),
    buildRow(goingToday ?? race.going, history.filter((e) => goingBand(e.going) === goingToday), baseWpr),
    buildRow('This prep', thisPrepEntries(history, race.date), baseWpr),
    buildRow('This year', history.filter((e) => new Date(e.date).getFullYear() === yearToday), baseWpr),
    buildRow('Last 6mo', history.filter((e) => new Date(e.date).getTime() >= sixMonthsAgoMs), baseWpr),
  ]
}
