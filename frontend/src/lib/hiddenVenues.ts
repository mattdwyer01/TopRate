import { useCallback, useState } from 'react'

// User-curated "never show this venue" list - a manual counterpart to
// useShowBushMeetings' automatic prize-money threshold (see lib/meetings.ts's
// BUSH_TRACK_THRESHOLD). Some meetings aren't bush-grade by prize money but
// the user still doesn't want them cluttering the grid/ticker (e.g. a
// jumps-only or trial-heavy venue) - this is that manual override, keyed by
// the raw venue string (same identity `groupIntoMeetings`/`meetingKey`
// already use, so no new normalization is introduced here).
const STORAGE_KEY = 'toprate_hidden_venues_v1'

function readHiddenSet(): Set<string> {
  try {
    const raw = window.localStorage.getItem(STORAGE_KEY)
    return raw ? new Set(JSON.parse(raw)) : new Set()
  } catch {
    return new Set()
  }
}

function writeHiddenSet(set: Set<string>) {
  try {
    window.localStorage.setItem(STORAGE_KEY, JSON.stringify([...set]))
  } catch {
    // localStorage can throw in private-browsing/storage-full states - the
    // in-memory set still works for the rest of this session.
  }
}

export function useHiddenVenues() {
  const [hiddenVenues, setHiddenVenuesState] = useState<Set<string>>(() => readHiddenSet())

  const hideVenue = useCallback((venue: string) => {
    setHiddenVenuesState((prev) => {
      if (prev.has(venue)) return prev
      const next = new Set(prev)
      next.add(venue)
      writeHiddenSet(next)
      return next
    })
  }, [])

  const unhideVenue = useCallback((venue: string) => {
    setHiddenVenuesState((prev) => {
      if (!prev.has(venue)) return prev
      const next = new Set(prev)
      next.delete(venue)
      writeHiddenSet(next)
      return next
    })
  }, [])

  return { hiddenVenues, hideVenue, unhideVenue }
}
