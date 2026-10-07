import { useState } from 'react'
import { useLiveStreams } from '../../lib/liveVision'
import { LivePlayerModal } from '../../components/LivePlayerModal'
import { PlayIcon } from '../../components/PlayIcon'

// "Watch live" pill for a race that has not finished. Only shown when the user has saved at least one stream address in
// Settings, so by default nothing changes on the page.
export function LiveWatch({ show }: { show: boolean }) {
  const [streams] = useLiveStreams()
  const [open, setOpen] = useState(false)
  if (!show || Object.keys(streams).length === 0) return null
  return (
    <>
      <button
        type="button"
        onClick={() => setOpen(true)}
        className="mt-2.5 inline-flex items-center justify-center gap-1.5 rounded-full bg-rose px-4 py-1.5 text-sm font-semibold text-white transition-opacity hover:opacity-90 max-sm:w-full"
      >
        <PlayIcon className="h-3 w-3" />
        Watch live
      </button>
      {open && <LivePlayerModal onClose={() => setOpen(false)} />}
    </>
  )
}
