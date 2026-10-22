// Actual running positions of a Hong Kong race, read from HKJC's aerial replay image (research/hk_aerial_build.py ->
// data/hk_aerial/<YYYYMMDD>_<HV|ST>.json). Four snapshots per race: the leader at about 780m, 410m and 200m to go, and the finish.
// Only past races of the 2026-27 season so far, and only once HKJC has published the image (a few days after the meeting).

export interface AerialFrame {
  x: number // pixels along the picture
  rail_m: number | null // metres from the inside rail
}

export interface AerialRunner {
  pla: number | null
  draw: string | null
  lbw: number | null
  frames: (AerialFrame | null)[] // 4 entries
}

export interface AerialRace {
  dist: string | null
  field: number[]
  runners?: Record<string, AerialRunner> // keyed by horse (saddle) number
  err?: string
}

interface AerialMeeting {
  date: string
  course: string
  races: Record<string, AerialRace>
}

export const AERIAL_LABELS = ['About 780m out', 'About 410m out', 'About 200m out', 'Finish']
// Frames 0 and 1 follow the leader at the right of the picture, frames 2 and 3 at the left (the camera turns round).
export const AERIAL_LEADER_RIGHT = [true, true, false, false]
// Pixels per length measured against HKJC's official lengths behind (96 races): Happy Valley 42.8, Sha Tin 40.8.
const PX_PER_LENGTH: Record<string, number> = { HV: 42.8, ST: 40.8 }

export function hkCourse(venue: string): 'HV' | 'ST' | null {
  const v = venue.toLowerCase()
  if (v.includes('happy valley')) return 'HV'
  if (v.includes('sha tin')) return 'ST'
  return null
}

export function pxPerLength(course: string): number {
  return PX_PER_LENGTH[course] ?? 41.8
}

const cache = new Map<string, Promise<AerialMeeting | null>>()

function fetchMeeting(date: string, course: string): Promise<AerialMeeting | null> {
  const url = `data/hk_aerial/${date.slice(0, 10).replace(/-/g, '')}_${course}.json`
  let p = cache.get(url)
  if (!p) {
    p = fetch(url, { cache: 'no-cache' })
      .then((res) => (res.ok ? (res.json() as Promise<AerialMeeting>) : null))
      .catch(() => null)
    cache.set(url, p)
  }
  return p
}

export async function loadAerialRace(date: string, venue: string, raceNumber: number): Promise<{ race: AerialRace; course: string } | null> {
  const course = hkCourse(venue)
  if (!course) return null
  const m = await fetchMeeting(date, course)
  const race = m?.races?.[String(raceNumber)]
  return race && race.runners ? { race, course } : null
}
