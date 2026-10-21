import { useState } from 'react'
import { replayUrl, useReplayCodes } from '../../lib/replay'

// The race replay as a card beside the Result panel (xl and up; below that the banner's "Watch race replay" button is used).
// The file only exists once the race has run and a venue we have not seen has no code, so a missing replay shows a short note.
export function ReplayCard({ venue, date, raceNumber }: { venue: string; date: string; raceNumber: number }) {
  const codes = useReplayCodes()
  const [failed, setFailed] = useState(false)
  const url = replayUrl(codes, venue, date, raceNumber)
  return (
    <section className="flex h-full flex-col rounded-lg border border-line bg-panel p-3 shadow-[var(--shadow-1)]" aria-label="Race replay">
      <h3 className="mb-2 text-sm font-semibold text-ink">Race replay</h3>
      {url && !failed ? (
        // The box takes whatever height the Result panel sets (the video letterboxes inside it), so the two always end together and the row stays short.
        <div className="relative min-h-[160px] w-full flex-1 overflow-hidden rounded-md border border-line bg-black">
          <video key={url} className="absolute inset-0 h-full w-full object-contain" src={url} controls playsInline preload="metadata" onError={() => setFailed(true)} />
        </div>
      ) : (
        <p className="flex flex-1 items-center justify-center rounded-md bg-bg px-3 py-6 text-center text-xs text-ink-mute">
          {url ? (
            <>
              No replay found for this race yet. <a className="underline" href={url} target="_blank" rel="noopener noreferrer">Try the link directly</a>
            </>
          ) : (
            'Replay not available for this race.'
          )}
        </p>
      )}
    </section>
  )
}
