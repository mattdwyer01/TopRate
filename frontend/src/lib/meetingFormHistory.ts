import type { RawFormRun } from '../types/data'
import type { FormHistoryEntry, FormRun } from '../types/domain'
import { toFormRun } from '../api/adapter'

// Mirrors toprate_daily.py's _slugify_venue() exactly (lowercase,
// non-alphanumeric runs collapsed to a single '-', trimmed) - the two must
// stay in lockstep since this is how the URL is built to match a filename
// toprate_daily.py already wrote.
function slugifyVenue(venue: string): string {
  const s = venue
    .trim()
    .toLowerCase()
    .replace(/[^a-z0-9]+/g, '-')
    .replace(/^-+|-+$/g, '')
  return s || 'venue'
}

function meetingFileUrl(date: string, venue: string): string {
  return `horse_history/${date.slice(0, 10)}_${slugifyVenue(venue)}.json`
}

type MeetingBlob = Record<string, RawFormRun[]>

// One in-flight/resolved fetch per meeting file, shared across every horse
// in that race - a field of 12 runners opened one after another (the common
// case) costs one request total, not one per horse.
const meetingCache = new Map<string, Promise<MeetingBlob | null>>()

function fetchMeetingBlob(date: string, venue: string): Promise<MeetingBlob | null> {
  const url = meetingFileUrl(date, venue)
  let promise = meetingCache.get(url)
  if (!promise) {
    promise = fetch(url, { cache: 'no-cache' })
      .then((res) => (res.ok ? (res.json() as Promise<MeetingBlob>) : null))
      .catch(() => null)
    meetingCache.set(url, promise)
  }
  return promise
}

function tempoOf(early: number | null, late: number | null): 'Fast' | 'Even' | 'Slow' | null {
  if (early == null || late == null) return null
  const diff = early - late
  if (diff >= 2) return 'Fast'
  if (diff <= -2) return 'Slow'
  return 'Even'
}

function relativeSettle(settled: number | null, fieldSize: number | null): number | null {
  if (settled == null || fieldSize == null || fieldSize <= 0 || settled <= 0) return null
  return Math.min(1, settled / fieldSize)
}

export interface MeetingFormHistory {
  runs: FormRun[] // newest first, matches Runner.recentRuns
  formHistory: FormHistoryEntry[] // oldest first, matches Runner.formHistory
}

// Fetches a horse's COMPLETE prior race history from the static per-meeting
// files toprate_daily.py's build_horse_history_files() writes (see
// CLAUDE.md's "horse_history/" note) - the static replacement for the
// decommissioned Supabase live fetch this used to hit
// (lib/supabaseFormHistory.ts, removed once this shipped). Matched by horse
// NAME (case-insensitive/trimmed), the same join key the backend itself
// uses (horse_lc). date/venue identify which meeting file to fetch - pass
// the RACE being viewed (today's run), not the horse's own most recent run.
//
// Returns null if the meeting file doesn't exist (404, e.g. a meeting
// outside the rolling window) or the horse isn't in it, so callers can fall
// back to the embedded static data. Never throws.
export async function fetchMeetingFormHistory(
  date: string,
  venue: string,
  horseName: string,
): Promise<MeetingFormHistory | null> {
  if (!date || !venue || !horseName) return null
  const blob = await fetchMeetingBlob(date, venue)
  if (!blob) return null
  const rawRuns = blob[horseName.trim().toLowerCase()]
  if (!rawRuns || rawRuns.length === 0) return null

  const runs = rawRuns.map(toFormRun) // already newest-first (see _run_record)

  const formHistory: FormHistoryEntry[] = [...rawRuns]
    .reverse() // oldest-first, matches Runner.formHistory
    .map((r) => ({
      wpr: r.wpr,
      going: r.go,
      distance: r.dist,
      tempo: tempoOf(r.ie, r.il),
      relativeSettlePosition: relativeSettle(r.psl, r.fs ?? null),
      date: r.d ?? '',
      // horse_history files don't carry void detection (steward/video
      // comments) - defaults to false (shown as valid) rather than
      // silently misrepresenting an unknown as void, the same tradeoff
      // the old Supabase fetch made for the same reason.
      isVoid: false,
    }))

  return { runs, formHistory }
}
