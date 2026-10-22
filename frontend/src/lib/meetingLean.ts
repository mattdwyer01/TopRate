import { useEffect, useState } from 'react'

// Live meeting lean from racing.com GPS (meeting_lean.py, workflow meeting_lean.yml): per race that has run, the rank correlation of where horses sat after 400m
// (lead), distance off the rail (fence) and barrier (draw) with the finishing order. A READING AID: it changes no rating. VIC and SA only, a few minutes after each race.
// Bars from the as-of study (22 Oct 2026): after 3+ races, leaders lean at or above +0.45 or fence lean at or above +0.35 is where the next race carries the most.
export const MIN_LEAN_RACES = 3
export const LEAD_LEAN_MIN = 0.45
export const FENCE_LEAN_MIN = 0.35

interface RaceLean { lead: number | null; fence: number | null; draw: number | null; n: number; t: string }
type LeanFile = Record<string, Record<string, Record<string, RaceLean>>>

export interface MeetingLean { races: number; lead: number | null; fence: number | null; leadStrong: boolean; fenceStrong: boolean }

const mean = (xs: (number | null)[]): number | null => {
  const v = xs.filter((x): x is number => x != null)
  return v.length ? v.reduce((a, b) => a + b, 0) / v.length : null
}

export function meetingLean(file: LeanFile | null, date: string, venue: string, beforeRace: number): MeetingLean | null {
  const races = file?.[date]?.[venue]
  if (!races) return null
  // only races earlier in the card than the one being viewed
  const earlier = Object.entries(races).filter(([n]) => Number(n) < beforeRace).map(([, r]) => r)
  if (earlier.length < MIN_LEAN_RACES) return null
  const lead = mean(earlier.map((r) => r.lead))
  const fence = mean(earlier.map((r) => r.fence))
  return { races: earlier.length, lead, fence, leadStrong: lead != null && lead >= LEAD_LEAN_MIN, fenceStrong: fence != null && fence >= FENCE_LEAN_MIN }
}

let cache: { at: number; p: Promise<LeanFile | null> } | null = null
function load(): Promise<LeanFile | null> {
  if (!cache || Date.now() - cache.at > 90_000) {
    cache = {
      at: Date.now(),
      p: fetch('meeting_lean.json', { cache: 'no-cache' }).then((r) => (r.ok ? (r.json() as Promise<LeanFile>) : null)).catch(() => null),
    }
  }
  return cache.p
}

export function useMeetingLean(date: string, venue: string, raceNumber: number, live: boolean): MeetingLean | null {
  const [file, setFile] = useState<LeanFile | null>(null)
  useEffect(() => {
    if (!live) return
    let on = true
    const go = () => load().then((f) => on && setFile(f))
    go()
    const id = setInterval(go, 120_000)
    return () => { on = false; clearInterval(id) }
  }, [live])
  return live ? meetingLean(file, date, venue, raceNumber) : null
}
