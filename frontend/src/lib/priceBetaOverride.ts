import { useCallback, useState } from 'react'

// A per-device override of the WPR $ price softmax beta (see
// wpr_projection.py project_race / lib/raceModel.ts). Persisted so a
// browsing session keeps the chosen value; null means "use the server's
// own calibrated beta" (DashboardData.priceBeta).
const STORAGE_KEY = 'toprate_price_beta_override_v1'

function readStored(): number | null {
  try {
    const raw = window.localStorage.getItem(STORAGE_KEY)
    if (raw === null) return null
    const v = Number(raw)
    return Number.isFinite(v) ? v : null
  } catch {
    return null
  }
}

export function useBetaOverride() {
  const [betaOverride, setBetaOverrideState] = useState<number | null>(() => readStored())

  const setBetaOverride = useCallback((value: number | null) => {
    setBetaOverrideState(value)
    try {
      if (value == null) window.localStorage.removeItem(STORAGE_KEY)
      else window.localStorage.setItem(STORAGE_KEY, String(value))
    } catch {
      // localStorage can throw in private-browsing/storage-full states -
      // the in-memory value still works for the rest of the session.
    }
  }, [])

  return { betaOverride, setBetaOverride }
}
