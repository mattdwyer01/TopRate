import { useEffect, useState } from 'react'

// Ticking clock for relative-time displays (data freshness age, etc). 15s
// granularity is plenty for "Xm ago" text - no need for a per-second timer
// outside NextToJumpTicker's own imminent-race countdown.
export function useNow(intervalMs = 15_000): number {
  const [now, setNow] = useState(() => Date.now())
  useEffect(() => {
    const id = setInterval(() => setNow(Date.now()), intervalMs)
    return () => clearInterval(id)
  }, [intervalMs])
  return now
}
