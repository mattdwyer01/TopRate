import { useCallback, useState } from 'react'

// Same localStorage key and value format as the current dashboard
// (toprate_html_v3.py's ntj-collapsed, L10372) so an existing device
// preference carries over.
const STORAGE_KEY = 'ntj-collapsed'

function readStored(): boolean {
  try {
    return window.localStorage.getItem(STORAGE_KEY) === '1'
  } catch {
    return false
  }
}

export function useTickerCollapsed() {
  const [collapsed, setCollapsedState] = useState<boolean>(() => readStored())

  const setCollapsed = useCallback((value: boolean) => {
    setCollapsedState(value)
    try {
      window.localStorage.setItem(STORAGE_KEY, value ? '1' : '0')
    } catch {
      // localStorage can throw in private-browsing/storage-full states -
      // the in-memory toggle still works for the rest of the session.
    }
  }, [])

  return { collapsed, setCollapsed }
}
