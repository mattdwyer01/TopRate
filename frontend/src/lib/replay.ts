import { useEffect, useState } from 'react'

// Sky Racing race replays. TAB's meeting list gives a replay URL only for today's races, but the file name is
// predictable: YYYYMMDD + Sky venue code + 2-digit race number. replay_codes.json (written by the results poller)
// maps venue -> code, so any date works. Sky kept files for at least a year when checked (Oct 2026). These are Sky's
// own files linked from their CDN, not hosted or licensed by this app.
const BASE = 'https://mediatabs.skyracing.com.au/Race_Replay'

export type ReplayCodes = Record<string, string>

let cached: Promise<ReplayCodes> | null = null
export function fetchReplayCodes(): Promise<ReplayCodes> {
  if (!cached) {
    cached = fetch('replay_codes.json', { cache: 'no-cache' })
      .then((r) => (r.ok ? (r.json() as Promise<ReplayCodes>) : {}))
      .catch(() => ({}))
  }
  return cached
}

export function useReplayCodes(): ReplayCodes | null {
  const [codes, setCodes] = useState<ReplayCodes | null>(null)
  useEffect(() => {
    let live = true
    fetchReplayCodes().then((c) => live && setCodes(c))
    return () => {
      live = false
    }
  }, [])
  return codes
}

export function replayUrl(codes: ReplayCodes | null, venue: string, date: string | undefined, raceNo: number | null | undefined): string | null {
  if (!codes || !date || !raceNo || raceNo < 1 || raceNo > 15) return null
  const code = codes[venue.trim().toLowerCase()]
  const m = /^(\d{4})-(\d{2})-(\d{2})/.exec(date)
  if (!code || !m) return null
  return `${BASE}/${m[1]}/${m[2]}/${m[1]}${m[2]}${m[3]}${code}${String(raceNo).padStart(2, '0')}_V.mp4`
}
