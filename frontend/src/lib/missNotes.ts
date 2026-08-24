import { useCallback, useState } from 'react'

// Manual notes for a resulted runner's miss, keyed by run_id, persisted to
// localStorage (this device only - no cross-device sync, matching
// wprOverrides.ts's manual adjustments). Shown alongside the auto-generated
// miss explanation (wpr_miss.py's explain_miss(), see types/domain.ts's
// missCategory/missReason) - specifically offered when missCategory is
// 'unexplained', i.e. nothing in the data explains a material miss and a
// human note is the only way to record why.
const NOTES_KEY = 'toprate_miss_notes_v1'

type NoteMap = Record<string, string>

function readMap(): NoteMap {
  try {
    const raw = window.localStorage.getItem(NOTES_KEY)
    return raw ? JSON.parse(raw) : {}
  } catch {
    return {}
  }
}

function writeMap(map: NoteMap) {
  try {
    window.localStorage.setItem(NOTES_KEY, JSON.stringify(map))
  } catch {
    // localStorage can throw in private-browsing/storage-full states -
    // the in-memory value still works for the rest of the session.
  }
}

export function useMissNotes() {
  const [notes, setNotesState] = useState<NoteMap>(() => readMap())

  const setNote = useCallback((runId: string, value: string) => {
    setNotesState((prev) => {
      const next = { ...prev }
      const trimmed = value.trim()
      if (trimmed === '') delete next[runId]
      else next[runId] = trimmed
      writeMap(next)
      return next
    })
  }, [])

  return { notes, setNote }
}
