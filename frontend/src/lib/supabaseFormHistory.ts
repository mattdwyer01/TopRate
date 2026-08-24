import type { FormHistoryEntry, FormRun } from '../types/domain'

// TopRate's Supabase project - same URL supabase_sync.py (the Python
// pipeline) pushes to. This is the project's REST endpoint, not a secret.
const SUPABASE_URL = 'https://lvhgcduztkwkibrrkyqp.supabase.co'

// Public anon key - safe to embed in the built bundle (this file gets
// inlined into toprate_live.html). Access is gated by a Postgres Row Level
// Security policy on wpr_form_history (read-only - see supabase_schema.sql),
// not by keeping this key secret; that is how Supabase's anon key is
// designed to work. NEVER put the service_role key here - that one bypasses
// RLS entirely and must stay server-side only (see supabase_sync.py).
const SUPABASE_ANON_KEY = '__SUPABASE_ANON_KEY__'

const FIELDS = [
  'date', 'track', 'distance', 'going', 'positionfinish', 'wpr',
  'raceshapeearly', 'raceshapemid', 'raceshapelate',
  'sect_i_early', 'sect_i_to600', 'sect_i_l600',
  'barrier', 'marginfinish', 'positionsettled', 'position800m', 'position400m',
  'race_class', 'jockey', 'isbarriertrial', 'field_size', 'scrape_date',
].join(',')

interface RawFormHistoryRow {
  date: string | null
  track: string | null
  distance: number | null
  going: string | null
  positionfinish: number | null
  wpr: number | null
  raceshapeearly: number | null
  raceshapemid: number | null
  raceshapelate: number | null
  sect_i_early: number | null
  sect_i_to600: number | null
  sect_i_l600: number | null
  barrier: number | null
  marginfinish: number | null
  positionsettled: number | null
  position800m: number | null
  position400m: number | null
  race_class: string | null
  jockey: string | null
  isbarriertrial: boolean | null
  field_size: number | null
  scrape_date: string | null
}

export interface LiveFormHistory {
  runs: FormRun[] // newest first, matches Runner.recentRuns
  formHistory: FormHistoryEntry[] // oldest first, matches Runner.formHistory
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

// Fetches a horse's COMPLETE prior race history directly from Supabase
// (wpr_form_history), to replace the static payload's capped-at-10 formRuns
// once it resolves - see RecentRunsTable.tsx. Matched by horse NAME
// (case-insensitive), the same join key the Python pipeline itself already
// uses to build the static payload's own form tables (toprate_daily.py's
// horse_lc dedup key) - not a new/riskier matching strategy, just done
// client-side instead of server-side.
//
// Returns null if the anon key hasn't been configured (so callers can fall
// back to the embedded static data without erroring), and throws on a real
// fetch/HTTP failure so callers can distinguish "not configured" from
// "configured but broken" if they want to.
export async function fetchFullFormHistory(
  horseName: string,
  signal?: AbortSignal,
): Promise<LiveFormHistory | null> {
  if (!horseName || SUPABASE_ANON_KEY.startsWith('__')) return null
  const url =
    `${SUPABASE_URL}/rest/v1/wpr_form_history?` +
    `horse=ilike.${encodeURIComponent(horseName)}&order=date.asc&select=${FIELDS}`
  const res = await fetch(url, {
    signal,
    headers: {
      apikey: SUPABASE_ANON_KEY,
      Authorization: `Bearer ${SUPABASE_ANON_KEY}`,
    },
  })
  if (!res.ok) throw new Error(`Supabase form history fetch failed: ${res.status}`)
  const rows: RawFormHistoryRow[] = await res.json()

  // Dedupe same-date rows captured by more than one scrape - keep the
  // latest scrape_date, mirroring toprate_daily.py's dedup-by-scrape-
  // baseline. Barrier trials are excluded, same as the backend.
  const byDate = new Map<string, RawFormHistoryRow>()
  for (const r of rows) {
    if (r.isbarriertrial) continue
    if (!r.date || r.wpr == null) continue
    const existing = byDate.get(r.date)
    if (!existing || (r.scrape_date ?? '') >= (existing.scrape_date ?? '')) {
      byDate.set(r.date, r)
    }
  }
  const sorted = [...byDate.values()].sort((a, b) => (a.date ?? '').localeCompare(b.date ?? ''))
  if (sorted.length === 0) return { runs: [], formHistory: [] }

  const wprValues = sorted.map((r) => r.wpr).filter((w): w is number => w != null)
  const peakWpr = wprValues.length ? Math.max(...wprValues) : null

  const formHistory: FormHistoryEntry[] = sorted.map((r) => ({
    wpr: r.wpr,
    going: r.going ?? '',
    distance: r.distance ?? 0,
    tempo: tempoOf(r.sect_i_early, r.sect_i_l600),
    relativeSettlePosition: relativeSettle(r.positionsettled, r.field_size),
    date: r.date ?? '',
  }))

  const runs: FormRun[] = sorted
    .map((r) => ({
      track: r.track ?? '',
      distance: r.distance ?? 0,
      going: r.going ?? '',
      finishPosition: r.positionfinish,
      wpr: r.wpr,
      raceShapeEarly: r.raceshapeearly,
      raceShapeMid: r.raceshapemid,
      raceShapeLate: r.raceshapelate,
      sectionalEarly: r.sect_i_early,
      sectionalTo800: r.sect_i_to600,
      sectionalLate600: r.sect_i_l600,
      barrier: r.barrier,
      margin: r.marginfinish,
      positionSettled: r.positionsettled,
      position800m: r.position800m,
      position400m: r.position400m,
      raceClass: r.race_class,
      jockey: r.jockey,
      isPeakRun: peakWpr != null && r.wpr != null && Math.abs(r.wpr - peakWpr) < 0.05,
      date: r.date ?? undefined,
    }))
    .reverse() // newest first, matching Runner.recentRuns

  return { runs, formHistory }
}
