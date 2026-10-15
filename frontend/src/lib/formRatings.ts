import type { FormHistoryEntry } from '../types/domain'

export interface FormAverage {
  avg: number
  median: number
  n: number // rated runs actually used (can be fewer than asked for)
}

// Average and median of a horse's last `count` rated runs before the race date, on the form table's scale (ATW, the same scale as Proj).
// Compromised runs (isVoid) and unrated runs are skipped, then the last `count` of what is left are used. null when there is no usable run.
export function lastRunsRating(formHistory: FormHistoryEntry[], raceDate: string | null, count: number): FormAverage | null {
  const vals = formHistory
    .filter((r) => r.wpr != null && !r.isVoid && (raceDate == null || r.date < raceDate))
    .sort((a, b) => (a.date < b.date ? -1 : a.date > b.date ? 1 : 0))
    .slice(-count)
    .map((r) => r.wpr as number)
  if (vals.length === 0) return null
  const sorted = [...vals].sort((a, b) => a - b)
  const mid = sorted.length >> 1
  const median = sorted.length % 2 ? sorted[mid] : (sorted[mid - 1] + sorted[mid]) / 2
  return { avg: vals.reduce((s, v) => s + v, 0) / vals.length, median, n: vals.length }
}
