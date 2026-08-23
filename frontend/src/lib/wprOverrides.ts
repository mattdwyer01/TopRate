import { useCallback, useState } from 'react'

// Manual rating adjustments, keyed by run_id, persisted to localStorage (this
// device only - no cross-device sync yet). Same key as the old dashboard's
// WPR_OVR_KEY (toprate_html_v3.py L7100) for continuity: a delta added on
// top of the model's own projected WPR.
const DELTA_KEY = 'toprate_wpr_overrides_v1'

// A manually-entered BASE rating for a runner the model couldn't project at
// all (insufficient form history - projectedWpr is null). New in this
// rebuild; the old dashboard had no equivalent. Once set, the runner is
// treated as if the model's own base were this value (deltas still apply on
// top), so it joins the race's price/rank recompute like any rated runner.
const BASE_KEY = 'toprate_manual_base_v1'

// Manual late-scratching flags, keyed by run_id, persisted the same way as
// deltas/bases (this device only). The data source's own scratch signal
// (isScratched, seen in the raw API payload) isn't captured into
// toprate_data.json today, and even if it were, a late scratch needs to be
// reflected the moment it happens, not on the next pipeline run - this is
// the fast, local, reversible path for that. A scratched runner is excluded
// from computeEffectiveRace's field-relative price/rank softmax entirely
// (as if it weren't in the race), so the rest of the field's rated prices
// correctly reset around the smaller field.
const SCRATCHED_KEY = 'toprate_scratched_v1'

type OverrideMap = Record<string, number>

function readScratchedSet(): Set<string> {
  try {
    const raw = window.localStorage.getItem(SCRATCHED_KEY)
    return raw ? new Set(JSON.parse(raw)) : new Set()
  } catch {
    return new Set()
  }
}

function writeScratchedSet(set: Set<string>) {
  try {
    window.localStorage.setItem(SCRATCHED_KEY, JSON.stringify([...set]))
  } catch {
    // localStorage can throw in private-browsing/storage-full states -
    // the in-memory value still works for the rest of the session.
  }
}

function readMap(key: string): OverrideMap {
  try {
    const raw = window.localStorage.getItem(key)
    return raw ? JSON.parse(raw) : {}
  } catch {
    return {}
  }
}

function writeMap(key: string, map: OverrideMap) {
  try {
    window.localStorage.setItem(key, JSON.stringify(map))
  } catch {
    // localStorage can throw in private-browsing/storage-full states -
    // the in-memory value still works for the rest of the session.
  }
}

export function useWprOverrides() {
  const [deltas, setDeltasState] = useState<OverrideMap>(() => readMap(DELTA_KEY))
  const [bases, setBasesState] = useState<OverrideMap>(() => readMap(BASE_KEY))
  const [scratched, setScratchedState] = useState<Set<string>>(() => readScratchedSet())

  const setDelta = useCallback((runId: string, value: number | null) => {
    setDeltasState((prev) => {
      const next = { ...prev }
      if (value == null || Number.isNaN(value)) delete next[runId]
      else next[runId] = value
      writeMap(DELTA_KEY, next)
      return next
    })
  }, [])

  const setBase = useCallback((runId: string, value: number | null) => {
    setBasesState((prev) => {
      const next = { ...prev }
      if (value == null || Number.isNaN(value)) delete next[runId]
      else next[runId] = value
      writeMap(BASE_KEY, next)
      return next
    })
  }, [])

  const setScratched = useCallback((runId: string, value: boolean) => {
    setScratchedState((prev) => {
      const next = new Set(prev)
      if (value) next.add(runId)
      else next.delete(runId)
      writeScratchedSet(next)
      return next
    })
  }, [])

  return { deltas, bases, scratched, setDelta, setBase, setScratched }
}
