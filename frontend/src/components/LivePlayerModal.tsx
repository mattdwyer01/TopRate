import { useEffect, useRef, useState } from 'react'
import { useBodyScrollLock, useFocusTrap } from '../lib/modalA11y'
import { LIVE_CHANNELS, loadHls, useLiveStreams } from '../lib/liveVision'
import type { LiveChannel } from '../lib/liveVision'

// Popup live-vision player over the page. Plays whichever stream addresses the user has saved in Settings. Esc, the close
// button or a click outside closes only this popup.
export function LivePlayerModal({ onClose }: { onClose: () => void }) {
  const [streams] = useLiveStreams()
  const channels = LIVE_CHANNELS.filter((c) => streams[c.key])
  const [channel, setChannel] = useState<LiveChannel | null>(channels[0]?.key ?? null)
  const [error, setError] = useState<string | null>(null)
  const videoRef = useRef<HTMLVideoElement>(null)
  const panelRef = useRef<HTMLDivElement>(null)
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

  const url = channel ? streams[channel] : undefined
  useEffect(() => {
    const v = videoRef.current
    if (!v || !url) return
    setError(null)
    let cancelled = false
    let hls: { destroy(): void } | null = null
    const fail = () => !cancelled && setError("Couldn't play this stream. The address may have changed, or the provider may have blocked it.")
    if (v.canPlayType('application/vnd.apple.mpegurl')) {
      v.src = url
      v.play().catch(() => {})
    } else {
      loadHls()
        .then((Hls) => {
          if (cancelled) return
          if (!Hls.isSupported()) return fail()
          const h = new Hls({ lowLatencyMode: true })
          hls = h
          h.loadSource(url)
          h.attachMedia(v)
          h.on(Hls.Events.MANIFEST_PARSED, () => v.play().catch(() => {}))
          h.on(Hls.Events.ERROR, (_e: unknown, data: { fatal?: boolean }) => {
            if (data?.fatal) fail()
          })
        })
        .catch(fail)
    }
    return () => {
      cancelled = true
      hls?.destroy()
      v.removeAttribute('src')
      v.load()
    }
  }, [url])

  return (
    <div className="fixed inset-0 z-[70] flex items-center justify-center bg-ink/70 p-3 sm:p-6" onClick={onClose}>
      <div
        ref={panelRef}
        role="dialog"
        aria-modal="true"
        aria-label="Live vision"
        tabIndex={-1}
        onClick={(e) => e.stopPropagation()}
        className="w-full max-w-3xl overflow-hidden rounded-xl border border-line bg-panel shadow-[var(--shadow-1)] outline-none"
      >
        <div className="flex items-center gap-2 px-3 py-2">
          <div className="flex min-w-0 flex-1 flex-wrap gap-1.5">
            {channels.map((c) => (
              <button
                key={c.key}
                type="button"
                onClick={() => setChannel(c.key)}
                className={`rounded-full border px-3 py-1 text-xs font-medium ${c.key === channel ? 'border-ink bg-ink text-white' : 'border-line bg-bg text-ink-soft hover:text-ink'}`}
              >
                {c.label}
              </button>
            ))}
          </div>
          <button type="button" onClick={onClose} aria-label="Close live vision" className="flex-none rounded-md px-2 py-1 text-lg leading-none text-ink-mute hover:bg-bg hover:text-ink">
            &times;
          </button>
        </div>
        {error ? (
          <p className="px-3 pb-4 text-sm text-ink-mute">{error}</p>
        ) : (
          <video ref={videoRef} className="aspect-video w-full bg-black" controls autoPlay playsInline />
        )}
      </div>
    </div>
  )
}
