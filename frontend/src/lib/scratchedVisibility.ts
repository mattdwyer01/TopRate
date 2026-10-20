import { useCallback, useState } from 'react'

// "Show scratched runners in the table" toggle - persisted per-device, same
// pattern as useTableDensity/useShowBushMeetings. With no saved choice they
// are hidden on every screen size (one behaviour on phone and desktop), and
// the pill above the table brings them back. Once the user flips the toggle
// that choice wins.
const STORAGE_KEY = 'toprate_show_scratched_v1'

function defaultShow(): boolean {
  return false
}

function readStored(): boolean {
  try {
    const raw = window.localStorage.getItem(STORAGE_KEY)
    return raw === null ? defaultShow() : raw === '1'
  } catch {
    return defaultShow()
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
