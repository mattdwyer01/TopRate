import { useCallback, useState } from 'react'

// "Show scratched runners in the table" toggle - persisted per-device, same
// pattern as useTableDensity/useShowBushMeetings. Defaults to showing them
// (matches the existing behaviour: scratched runners sort to the bottom
// rather than disappearing) - this only lets someone opt into hiding them
// for a cleaner view, it doesn't change the default.
const STORAGE_KEY = 'toprate_show_scratched_v1'

function readStored(): boolean {
  try {
    const raw = window.localStorage.getItem(STORAGE_KEY)
    return raw === null ? true : raw === '1'
  } catch {
    return true
  }
}

export function useShowScratched() {
  const [showScratched, setShowScratchedState] = useState<boolean>(() => readStored())

  const setShowScratched = useCallback((value: boolean) => {
    setShowScratchedState(value)
    try {
      window.localStorage.setItem(STORAGE_KEY, value ? '1' : '0')
    } catch {
      // localStorage can throw in private-browsing/storage-full states -
      // the in-memory toggle still works for the rest of the session.
    }
  }, [])

  return { showScratched, setShowScratched }
}
