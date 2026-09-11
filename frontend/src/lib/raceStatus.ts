import type { Race } from '../types/domain'

// A race within this many minutes of jumping gets the "soon" highlight.
export const SOON_THRESHOLD_MS = 15 * 60_000

export type RaceStatus = 'resulted' | 'interim' | 'soon' | 'later'

// Four states, not the naive two (resulted/not) - a race that's started but
// doesn't have every runner's finish position yet (TAB's interim feed
// trickling in, or nothing at all so far) used to fall through to looking
// IDENTICAL to a race hours away the moment it passed SOON_THRESHOLD_MS
// post-start, which is exactly backwards: that's the state most worth
// noticing at a glance. Shared between MeetingsGrid (the whole-day view)
// and RaceDetail (the per-meeting race picker) so both read the same status
// the same way - defined once here rather than twice, drifting apart.
export function raceStatus(race: Race, now: number): RaceStatus {
  if (race.allResulted && !race.provisional) return 'resulted'
  if (race.allResulted || race.runners.some((r) => r.finishPosition !== null)) return 'interim'
  const msUntilStart = new Date(race.startTime).getTime() - now
  return msUntilStart <= SOON_THRESHOLD_MS ? 'soon' : 'later'
}

// MeetingsGrid's own pill styling (a plain <button>, not the shared Pill
// component - see its own file for why: sticky-table cell sizing).
export const STATUS_CLASSES: Record<RaceStatus, string> = {
  resulted: 'border-line-soft bg-line-soft text-ink-faint hover:border-line',
  interim: 'border-amber-line bg-amber-bg font-semibold text-amber hover:opacity-80',
  soon: 'border-rose-line bg-rose-bg font-semibold text-rose hover:opacity-80',
  later: 'border-line-soft bg-bg text-ink hover:border-emerald-line hover:bg-emerald-bg',
}

// Colors deliberately don't reuse emerald for "soon" - emerald already
// means "confirmed Resulted" on the race detail page's own header badge,
// so using it here too for "about to jump" would contradict itself.
// All four states listed, including "later" - a race hours away and a
// race that already ran are both some shade of grey/neutral, so without
// "later" spelled out here too a viewer has no way to tell "this pill's
// grey because nothing's happened yet" from "this pill's grey because
// it's genuinely Resulted" (real confusion, reported live 2026-09-11 -
// the swap to showing finishing numbers instead of the time below is the
// real fix for that; the legend entry is just so the neutral state isn't
// left undocumented altogether).
export const STATUS_LEGEND: { status: RaceStatus; label: string; dotClass: string }[] = [
  { status: 'soon', label: 'Jumping soon', dotClass: 'bg-rose' },
  { status: 'interim', label: 'Interim result', dotClass: 'bg-amber' },
  { status: 'resulted', label: 'Resulted', dotClass: 'bg-ink-faint' },
  { status: 'later', label: 'Still to run', dotClass: 'bg-line' },
]

// Top N (by finish position, ascending) TAB numbers for a race - used to
// replace the pill's time-of-day text once a race is resulted/interim, so
// "what happened" is visible without opening the race (and, together with
// the text actually changing rather than just its color, makes a
// resulted/interim pill unmistakable at a glance instead of relying on a
// grey/amber shade someone has to already know the legend for).
export function topFinishers(race: Race, n = 4): number[] {
  return race.runners
    .filter((r): r is typeof r & { finishPosition: number } => r.finishPosition !== null)
    .sort((a, b) => a.finishPosition - b.finishPosition)
    .slice(0, n)
    .map((r) => r.tabNumber)
}

// Maps a status onto the shared Pill component's existing tone options
// (RaceDetail's meeting race-picker uses Pill, unlike MeetingsGrid's plain
// button cells) - 'later' intentionally maps to Pill's neutral 'default'
// tone rather than getting its own, so it reads as "nothing to flag" the
// same way an untouched Pill does elsewhere in the app.
export const STATUS_PILL_TONE: Record<RaceStatus, 'default' | 'emerald' | 'rose' | 'amber' | 'slate'> = {
  resulted: 'slate',
  interim: 'amber',
  soon: 'rose',
  later: 'default',
}
