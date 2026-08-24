import type { FormHistoryEntry } from '../types/domain'

// Matches wpr_projection.py's _SPELL_GAP_DAYS - a gap longer than this
// starts a new campaign. Kept in sync with the backend so this column
// agrees with the projection description's own "Nth-up"/"First-up" language.
const SPELL_GAP_DAYS = 60

function parseISO(s: string | undefined | null): Date | null {
  if (!s) return null
  const t = Date.parse(s)
  return Number.isNaN(t) ? null : new Date(t)
}

function daysBetween(a: Date | null, b: Date | null): number | null {
  if (!a || !b) return null
  return Math.round((a.getTime() - b.getTime()) / 86_400_000)
}

export interface SpellInfo {
  // 'FU' (first-up), '2U', '3U', ... or '—' for a debut runner with no
  // prior form at all.
  label: string
  daysSince: number | null
}

// Which run of the current campaign today's race is, and days since the
// horse's last run. formHistory is the horse's full career, oldest-first
// (recentRuns is also full history now, but newest-first and richer per
// row - this uses formHistory since that's what's cheap to pass around
// for a simple date walk). Campaign count here is exact, not a lower
// bound - it walks back from the most recent prior run counting
// consecutive gaps under SPELL_GAP_DAYS, the same walk build_features()
// does server-side over the same underlying data.
export function spellPosition(formHistory: FormHistoryEntry[], raceDate: string | null): SpellInfo {
  if (formHistory.length === 0) return { label: '—', daysSince: null }
  const today = parseISO(raceDate)
  const dates = formHistory.map((r) => parseISO(r.date))
  const lastRunDate = dates[dates.length - 1] ?? null
  const daysSince = daysBetween(today, lastRunDate)
  if (daysSince == null) return { label: '—', daysSince: null }
  if (daysSince > SPELL_GAP_DAYS) return { label: 'FU', daysSince }

  let n = 2 // today's race + the most recent prior run
  for (let i = dates.length - 1; i > 0; i--) {
    // dates is oldest-first (ascending), so dates[i] is more recent than
    // dates[i - 1] - daysBetween(newer, older) to get a positive gap.
    const gap = daysBetween(dates[i], dates[i - 1])
    if (gap == null || gap > SPELL_GAP_DAYS) break
    n++
  }
  return { label: `${n}U`, daysSince }
}
