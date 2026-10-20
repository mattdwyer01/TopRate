import { useEffect, useState } from 'react'

// Track outlines (Oct 2026): the running rail of each course from OpenStreetMap, produced by research/track_outline_geometry.py and committed as track_outlines.json
// at the repo root. Points are whole metres in a local frame (x east, y north), one every `step` metres around the loop. Optional: a venue not in the file simply has no outline.

export interface TrackOutlineData {
  name: string
  perim: number // metres round the rail
  straight: number // longest straight, metres
  radius: number | null // typical bend radius, metres
  by: 'name' | 'location'
  s0: number // index of the start of the longest straight
  sn: number // its length in points
  pts: [number, number][]
  // Start and finish, read by hand off plan maps (track_marks.json); absent for a track without them. Same metre frame as pts.
  dir?: 'cw' | 'ccw' // racing direction seen from above
  fin?: [number, number] // winning post
  starts?: Record<string, [number, number]> // start distance (m) -> point on the rail
  chutes?: Record<string, [[number, number], [number, number]]> // start distance (m) -> spur from the rail to the start
}

export interface TrackOutlinePayload {
  source: string
  step: number
  tracks: Record<string, TrackOutlineData>
}

const FILE = 'track_outlines.json'

let cached: Promise<TrackOutlinePayload | null> | null = null

function load(): Promise<TrackOutlinePayload | null> {
  if (!cached) {
    cached = fetch(FILE)
      .then((r) => (r.ok ? (r.json() as Promise<TrackOutlinePayload>) : null))
      .catch(() => null)
  }
  return cached
}

// One fetch for the whole session; the file only changes when the outlines are rebuilt.
export function useTrackOutlines(): TrackOutlinePayload | null {
  const [data, setData] = useState<TrackOutlinePayload | null>(null)
  useEffect(() => {
    let alive = true
    load().then((d) => alive && setData(d))
    return () => {
      alive = false
    }
  }, [])
  return data
}

const norm = (s: string) => s.toLowerCase().replace(/[^a-z0-9]/g, '')

export function findOutline(payload: TrackOutlinePayload | null, venue: string): TrackOutlineData | null {
  if (!payload) return null
  const want = norm(venue)
  for (const [k, v] of Object.entries(payload.tracks)) if (norm(k) === want) return v
  return null
}
