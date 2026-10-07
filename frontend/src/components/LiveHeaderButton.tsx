import { useState } from 'react'
import { useLiveStreams } from '../lib/liveVision'
import { LivePlayerModal } from './LivePlayerModal'

// Header "Live" button. Only rendered when at least one live-vision stream address has been saved in Settings, so by default
// the header is unchanged. Sky's channels run all day, so this is not tied to a particular race.
export function LiveHeaderButton() {
  const [streams] = useLiveStreams()
  const [open, setOpen] = useState(false)
  if (Object.keys(streams).length === 0) return null
  return (
    <>
      <button
        type="button"
        onClick={() => setOpen(true)}
        aria-label="Watch live vision"
        title="Watch live vision"
        className="flex h-7 items-center gap-1 rounded-full bg-rose px-2 text-[11px] font-semibold uppercase leading-none tracking-wide text-white hover:opacity-90"
      >
        <span aria-hidden="true" className="h-1.5 w-1.5 rounded-full bg-white" />
        Live
      </button>
      {open && <LivePlayerModal onClose={() => setOpen(false)} />}
    </>
  )
}
