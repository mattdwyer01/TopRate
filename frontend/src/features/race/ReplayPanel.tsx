import { useState } from 'react'
import { replayUrl, useReplayCodes } from '../../lib/replay'

// "Replay" pill plus an inline player, shown once the race has a result. The file only exists after the race has run, and
// a venue we have not seen yet has no code, so anything missing just hides the button or shows a short note.
export function ReplayPanel({ venue, date, raceNumber, hasResult }: { venue: string; date: string; raceNumber: number; hasResult: boolean }) {
  const codes = useReplayCodes()
  const [open, setOpen] = useState(false)
  const [failed, setFailed] = useState(false)
  const url = hasResult ? replayUrl(codes, venue, date, raceNumber) : null
  if (!url) return null
  return (
    <div className="mt-2">
      <button
        type="button"
        onClick={() => setOpen((o) => !o)}
        aria-expanded={open}
        className="inline-flex items-center gap-1.5 rounded-full border border-line bg-bg px-2.5 py-0.5 text-xs font-medium text-ink-soft hover:border-emerald-line hover:text-emerald-deep"
      >
        <span aria-hidden>&#9654;</span> {open ? 'Hide replay' : 'Race replay'}
      </button>
      {open &&
        (failed ? (
          <p className="mt-2 text-xs text-ink-mute">
            No replay found for this race yet. <a className="underline" href={url} target="_blank" rel="noopener noreferrer">Try the link directly</a>
          </p>
        ) : (
          <video
            key={url}
            className="mt-2 w-full max-w-3xl rounded-lg border border-line bg-black"
            src={url}
            controls
            autoPlay
            playsInline
            preload="metadata"
            onError={() => setFailed(true)}
          />
        ))}
    </div>
  )
}
