import { useEffect, useRef, useState } from 'react'
import { useBodyScrollLock, useFocusTrap } from '../lib/modalA11y'

// Pop-up player for a Sky Racing replay, opened over whatever is on screen (the runner detail modal, for past runs).
// Esc and a click outside close only this popup, not the modal underneath it.
export function ReplayModal({ url, title, onClose }: { url: string; title: string; onClose: () => void }) {
  const panelRef = useRef<HTMLDivElement>(null)
  const [failed, setFailed] = useState(false)
  useBodyScrollLock()
  useFocusTrap(panelRef)
  useEffect(() => {
    function onKey(e: KeyboardEvent) {
      if (e.key !== 'Escape') return
      e.stopImmediatePropagation()
      onClose()
    }
    window.addEventListener('keydown', onKey, true)
    return () => window.removeEventListener('keydown', onKey, true)
  }, [onClose])
  return (
    <div className="fixed inset-0 z-[70] flex items-center justify-center bg-ink/70 p-3 sm:p-6" onClick={onClose}>
      <div
        ref={panelRef}
        role="dialog"
        aria-modal="true"
        aria-label={`Race replay: ${title}`}
        tabIndex={-1}
        onClick={(e) => e.stopPropagation()}
        className="w-full max-w-3xl overflow-hidden rounded-xl border border-line bg-panel shadow-[var(--shadow-1)] outline-none"
      >
        <div className="flex items-center justify-between gap-3 px-3 py-2">
          <div className="min-w-0 truncate text-sm font-semibold text-ink">{title}</div>
          <button type="button" onClick={onClose} aria-label="Close replay" className="flex-none rounded-md px-2 py-1 text-lg leading-none text-ink-mute hover:bg-bg hover:text-ink">
            &times;
          </button>
        </div>
        {failed ? (
          <p className="px-3 pb-4 text-sm text-ink-mute">
            No replay found for this race. <a className="underline" href={url} target="_blank" rel="noopener noreferrer">Try the link directly</a>
          </p>
        ) : (
          <video key={url} className="aspect-video w-full bg-black" src={url} controls autoPlay playsInline preload="metadata" onError={() => setFailed(true)} />
        )}
      </div>
    </div>
  )
}
