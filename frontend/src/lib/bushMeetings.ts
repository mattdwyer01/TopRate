import { useCallback, useState } from 'react'

// Shared "show bush/picnic meetings" toggle - lives above MeetingsGrid so
// the next-to-jump ticker (a sibling in App.tsx's header) can apply the
// same filter, rather than showing races from meetings the user just chose
// to hide. Persisted per-device, same pattern as useTableDensity/
// useTickerCollapsed.
const STORAGE_KEY = 'toprate_show_bush_meetings_v1'

function readStored(): boolean {
  try {
    return window.localStorage.getItem(STORAGE_KEY) === '1'
  } catch {
    return false
  }
}

export function useShowBushMeetings() {
  const [showBush, setShowBushState] = useState<boolean>(() => readStored())

  const setShowBush = useCallback((value: boolean) => {
    setShowBushState(value)
    try {
      window.localStorage.setItem(STORAGE_KEY, value ? '1' : '0')
    } catch {
      // localStorage can throw in private-browsing/storage-full states -
      // the in-memory toggle still works for the rest of the session.
    }
  }, [])

  return { showBush, setShowBush }
}
