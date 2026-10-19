import { useCallback, useState } from 'react'

// "Show scratched runners in the table" toggle - persisted per-device, same
// pattern as useTableDensity/useShowBushMeetings. With no saved choice it
// shows them on a wide screen (scratched runners sort to the bottom) and
// hides them on a phone, where a dozen dimmed rows push the live field off
// the first screen. Once the user flips the toggle that choice wins.
const STORAGE_KEY = 'toprate_show_scratched_v1'

const PHONE_MAX_WIDTH = 639

function defaultShow(): boolean {
  try {
    return window.innerWidth > PHONE_MAX_WIDTH
  } catch {
    return true
  }
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
