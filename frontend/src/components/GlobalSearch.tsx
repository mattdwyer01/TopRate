import { useEffect, useMemo, useRef, useState } from 'react'
import type { Race } from '../types/domain'
import { searchRunners, type SearchResult } from '../lib/search'
import { useBodyScrollLock, useFocusTrap } from '../lib/modalA11y'

interface GlobalSearchProps {
  races: Race[]
  onSelectRunner: (raceId: string, date: string, runId: string) => void
  onClose: () => void
}

const FIELD_LABEL: Record<SearchResult['matchedField'], string> = {
  horse: 'horse',
  jockey: 'jockey',
  trainer: 'trainer',
}

// A single search box for horse/jockey/trainer, reachable from the header
// search icon or the "/" shortcut. Jumps straight to that runner's detail
// panel (via App.tsx's goToRace(raceId, date, runId) -> RaceDetail's
// initialRunId) rather than just the race - the whole point is not having
// to re-find the horse in the runner table after landing.
export function GlobalSearch({ races, onSelectRunner, onClose }: GlobalSearchProps) {
  const [query, setQuery] = useState('')
  const panelRef = useRef<HTMLDivElement>(null)
  const inputRef = useRef<HTMLInputElement>(null)

  useBodyScrollLock()
  useFocusTrap(panelRef)

  useEffect(() => {
    inputRef.current?.focus()
  }, [])

  useEffect(() => {
    function onKey(e: KeyboardEvent) {
      if (e.key === 'Escape') onClose()
    }
    window.addEventListener('keydown', onKey)
    return () => window.removeEventListener('keydown', onKey)
  }, [onClose])

  const results = useMemo(() => searchRunners(races, query), [races, query])

  function select(r: SearchResult) {
    onSelectRunner(r.raceId, r.date, r.runId)
    onClose()
  }

  return (
    <div
      className="fixed inset-0 z-40 flex items-start justify-center overflow-y-auto bg-ink/60 p-3 pt-16 sm:pt-24"
      onClick={onClose}
    >
      <div
        ref={panelRef}
        role="dialog"
        aria-modal="true"
        aria-label="Search"
        tabIndex={-1}
        className="w-full max-w-lg rounded-lg bg-panel shadow-[var(--shadow-2)] outline-none"
        onClick={(e) => e.stopPropagation()}
      >
        <div className="border-b border-line p-3">
          <input
            ref={inputRef}
            type="text"
            value={query}
            onChange={(e) => setQuery(e.target.value)}
            onKeyDown={(e) => {
              if (e.key === 'Enter' && results[0]) select(results[0])
            }}
            placeholder="Search horse, jockey, or trainer..."
            className="w-full rounded-md border border-line bg-bg px-3 py-2 text-sm text-ink outline-none focus:border-emerald"
          />
        </div>
        <div className="max-h-[60vh] overflow-y-auto">
          {query.trim().length < 2 ? (
            <p className="p-4 text-center text-xs text-ink-faint">Type at least 2 characters...</p>
          ) : results.length === 0 ? (
            <p className="p-4 text-center text-xs text-ink-faint">No matches in the last 45 days.</p>
          ) : (
            <ul className="divide-y divide-line-soft">
              {results.map((r) => (
                <li key={`${r.raceId}-${r.runId}`}>
                  <button
                    type="button"
                    onClick={() => select(r)}
                    className="flex w-full flex-col gap-0.5 px-3 py-2 text-left hover:bg-bg"
                  >
                    <span className="text-sm font-medium text-ink">
                      {r.horse}
                      {r.matchedField !== 'horse' && (
                        <span className="ml-1.5 text-xs font-normal text-ink-faint">
                          (matched {FIELD_LABEL[r.matchedField]})
                        </span>
                      )}
                    </span>
                    <span className="text-xs text-ink-mute">
                      {[r.jockey, r.trainer].filter(Boolean).join(' / ') || 'jockey/trainer TBA'}
                      &nbsp;&middot; {r.venue} R{r.raceNumber} &middot; {r.date}
                    </span>
                  </button>
                </li>
              ))}
            </ul>
          )}
        </div>
      </div>
    </div>
  )
}
