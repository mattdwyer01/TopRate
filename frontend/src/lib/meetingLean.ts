import { useEffect, useState } from 'react'

// Live meeting lean from racing.com GPS (meeting_lean.py, workflow meeting_lean.yml): per race that has run, the rank correlation of where horses sat after 400m
// (lead), distance off the rail (fence) and barrier (draw) with the finishing order. A READING AID: it changes no rating. VIC and SA only, a few minutes after each race.
// Bars from the as-of study (22 Oct 2026): after 3+ races, leaders lean at or above +0.45 or fence lean at or above +0.35 is where the next race carries the most.
export const MIN_LEAN_RACES = 3
export const LEAD_LEAN_MIN = 0.45
export const FENCE_LEAN_MIN = 0.35
// What the fence lean is worth (26 Oct 2026, research/fence_lean_width_study.py, 931 VIC/SA races in 109 meetings): a run's rating vs its last 3 moves by
// FENCE_K x (barrier fraction from the middle, -0.5 rail to +0.5 widest) x (earlier races' mean fence lean). Fitted -12.6 (90% range -17.5 to -7.6) on the
// final-section width this file uses; 12 is used. So the rail draw gains and the widest draw loses FENCE_K x 0.5 x lean points. Reading aid only.
export const FENCE_K = 12
export const FENCE_SHOWN_MIN = 0.1 // under this the lean is too small to say anything

interface RaceLean { lead: number | null; fence: number | null; draw: number | null; n: number; t: string }
type LeanFile = Record<string, Record<string, Record<string, RaceLean>>>

export interface MeetingLean { races: number; lead: number | null; fence: number | null; leadStrong: boolean; fenceStrong: boolean; fenceShown: boolean; railPoints: number | null }

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
  return {
    races: earlier.length,
    lead,
    fence,
    leadStrong: lead != null && lead >= LEAD_LEAN_MIN,
    fenceStrong: fence != null && fence >= FENCE_LEAN_MIN,
    fenceShown: fence != null && Math.abs(fence) >= FENCE_SHOWN_MIN,
    railPoints: fence != null ? FENCE_K * 0.5 * fence : null,
  }
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
