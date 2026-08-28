import type { Race } from '../types/domain'
import { todayIso } from './meetings'

export interface SearchResult {
  raceId: string
  date: string
  venue: string
  raceNumber: number
  runId: string
  horse: string
  jockey: string
  trainer: string
  matchedField: 'horse' | 'jockey' | 'trainer'
}

const FIELD_ORDER: Record<SearchResult['matchedField'], number> = { horse: 0, jockey: 1, trainer: 2 }

/** Case-insensitive substring search across every runner in every loaded
 * race (the payload's ~45-day window - see CLAUDE.md), checked against
 * horse first, then jockey, then trainer. A horse-name match always ranks
 * above a jockey/trainer match for the same query. Within a field: races
 * today-or-earlier sort most-recent-first (so a name search on someone
 * still racing surfaces their latest run, not a same-named future
 * acceptance that happens to sort later as a raw date string), THEN future
 * races sort soonest-first (so "when's it next racing" also works). */
export function searchRunners(races: Race[], query: string, limit = 40): SearchResult[] {
  const q = query.trim().toLowerCase()
  if (q.length < 2) return []
  const todayStr = todayIso()
  const out: SearchResult[] = []
  for (const race of races) {
    for (const r of race.runners) {
      const horse = r.horse?.toLowerCase() ?? ''
      const jockey = r.jockey?.toLowerCase() ?? ''
      const trainer = r.trainer?.toLowerCase() ?? ''
      let matchedField: SearchResult['matchedField'] | null = null
      if (horse.includes(q)) matchedField = 'horse'
      else if (jockey.includes(q)) matchedField = 'jockey'
      else if (trainer.includes(q)) matchedField = 'trainer'
      if (!matchedField) continue
      out.push({
        raceId: race.raceId,
        date: race.date,
        venue: race.venue,
        raceNumber: race.raceNumber,
        runId: r.runId,
        horse: r.horse,
        jockey: r.jockey,
        trainer: r.trainer,
        matchedField,
      })
    }
  }
  out.sort((a, b) => {
    const fieldDiff = FIELD_ORDER[a.matchedField] - FIELD_ORDER[b.matchedField]
    if (fieldDiff !== 0) return fieldDiff
    const aFuture = a.date > todayStr
    const bFuture = b.date > todayStr
    if (aFuture !== bFuture) return aFuture ? 1 : -1
    return aFuture ? a.date.localeCompare(b.date) : b.date.localeCompare(a.date)
  })
  return out.slice(0, limit)
}
