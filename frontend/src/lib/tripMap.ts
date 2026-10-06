import { useEffect, useState } from 'react'

// Trip map (Oct 2026): projected running line at about 800m from home for upcoming races at GPS-tracked
// courses (VIC, SA, QLD), produced by analysis/trip_map/build_trip_map.py and committed as trip_map.json.
// Optional: if the file is missing or a race is not in it, the Race tab simply does not offer the view.

export interface TripRunner {
  rid: string // run id, same as Runner.runId
  name: string
  barrier: number
  gap: number | null // projected lengths behind the leader (0 = leader)
  lane: number // projected metres from the inside rail
  nHist: number // how many earlier GPS runs the horse has (0 = forecast from barrier and track alone)
  last: { date: string; track: string; lane: number | null } | null
}

export interface TripRace {
  venue: string
  date: string
  race: number | null
  distance: number
  going: string | null
  rail: string | null
  state: 'VICSA' | 'QLD'
  laneKind: 'avg' | '800m' // VIC/SA GPS only has whole-run average width; QLD has width at 800m from home
  fs: number
  err: { gap: number; lane: number }
  runners: TripRunner[]
}

export interface TripMapPayload {
  generated: string
  trainEnd: string
  races: Record<string, TripRace>
}

const FILE = 'trip_map.json'
const REFRESH_MS = 10 * 60_000

let cached: Promise<TripMapPayload | null> | null = null

function load(force = false): Promise<TripMapPayload | null> {
  if (!cached || force) {
    cached = fetch(FILE, { cache: 'no-cache' })
      .then((r) => (r.ok ? (r.json() as Promise<TripMapPayload>) : null))
      .catch(() => null)
  }
  return cached
}

// One fetch shared by every component that asks, refreshed every 10 minutes.
export function useTripMap(): TripMapPayload | null {
  const [data, setData] = useState<TripMapPayload | null>(null)
  useEffect(() => {
    let alive = true
    load().then((d) => alive && setData(d))
    const id = setInterval(() => load(true).then((d) => alive && setData(d)), REFRESH_MS)
    return () => {
      alive = false
      clearInterval(id)
    }
  }, [])
  return data
}
