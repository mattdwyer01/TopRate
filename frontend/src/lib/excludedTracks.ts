import { useCallback, useState } from 'react'

// Per-device "tracks I don't bet at" list for the Overlays tab (e.g. a venue
// whose fields/prices the user doesn't trust, or just doesn't bet at) -
// persisted so it's a standing preference, not something re-set every visit.
// Scoped to the Overlays tab only (not the Race tab's meetings grid, which is
// for browsing all racing, not filtering a bet list) - same persistence
// pattern as useShowBushMeetings/useBetaOverride.
const STORAGE_KEY = 'toprate_excluded_tracks_v1'

function readStored(): Set<string> {
  try {
    const raw = window.localStorage.getItem(STORAGE_KEY)
    if (!raw) return new Set()
    const arr = JSON.parse(raw)
    return Array.isArray(arr) ? new Set(arr.filter((v): v is string => typeof v === 'string')) : new Set()
  } catch {
    return new Set()
  }
}

function writeStored(tracks: Set<string>) {
  try {
    window.localStorage.setItem(STORAGE_KEY, JSON.stringify([...tracks]))
  } catch {
    // localStorage can throw in private-browsing/storage-full states - the
    // in-memory set still works for the rest of the session.
  }
}

export function useExcludedTracks() {
  const [excludedTracks, setExcludedTracks] = useState<Set<string>>(() => readStored())

  const toggleTrack = useCallback((venue: string) => {
    setExcludedTracks((prev) => {
      const next = new Set(prev)
      if (next.has(venue)) next.delete(venue)
      else next.add(venue)
      writeStored(next)
      return next
    })
  }, [])

  return { excludedTracks, toggleTrack }
}
