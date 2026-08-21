import { useCallback, useState } from 'react'

// Same localStorage key as the current dashboard
// (toprate_html_v3.py isRaceTableCompact/setRaceTableCompact, L8310-8318) so
// a user's existing device preference carries over unchanged when they first
// load the rebuilt app - they should never see their density setting reset.
const STORAGE_KEY = 'toprate_race_table_compact_v1'

function readStored(): boolean {
  try {
    const raw = window.localStorage.getItem(STORAGE_KEY)
    // Matches the old app's default: compact when unset.
    return raw === null ? true : raw === 'true'
  } catch {
    return true
  }
}

export function useTableDensity() {
  const [compact, setCompactState] = useState<boolean>(() => readStored())

  const setCompact = useCallback((value: boolean) => {
    setCompactState(value)
    try {
      window.localStorage.setItem(STORAGE_KEY, String(value))
    } catch {
      // localStorage can throw in private-browsing/storage-full states -
      // the in-memory toggle still works for the rest of the session.
    }
  }, [])

  return { compact, setCompact }
}
