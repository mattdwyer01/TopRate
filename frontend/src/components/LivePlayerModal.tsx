import { useCallback, useEffect, useRef, useState } from 'react'
import { LIVE_CHANNELS, loadHls, useLiveStreams } from '../lib/liveVision'
import type { LiveChannel } from '../lib/liveVision'

// Floating live-vision player: no backdrop, so the dashboard stays usable underneath. Drag it by the title bar, resize from the
// bottom-right corner (height follows 16:9). Position and width are remembered in localStorage. Below 640px it docks to the bottom
// of the screen instead (dragging is awkward on a phone). Esc or the close button closes it.
const POS_KEY = 'toprate_live_window_v1'
const MIN_W = 280
const MARGIN = 8
const HEADER_H = 40
type Box = { x: number; y: number; w: number }

function clampBox(b: Box): Box {
  const vw = window.innerWidth
  const vh = window.innerHeight
  const w = Math.max(MIN_W, Math.min(b.w, vw - MARGIN * 2, 1200))
  const h = HEADER_H + (w * 9) / 16
  return {
    w,
    x: Math.max(MARGIN, Math.min(b.x, vw - w - MARGIN)),
    y: Math.max(MARGIN, Math.min(b.y, vh - h - MARGIN)),
  }
}

function initialBox(): Box {
  try {
    const raw = window.localStorage.getItem(POS_KEY)
    const o = raw ? JSON.parse(raw) : null
    if (o && [o.x, o.y, o.w].every((n) => typeof n === 'number' && isFinite(n))) return clampBox(o)
  } catch {
    // ignore
  }
  const w = Math.min(480, window.innerWidth - MARGIN * 2)
  return clampBox({ w, x: window.innerWidth - w - 16, y: 72 })
}

export function LivePlayerModal({ onClose }: { onClose: () => void }) {
  const [streams] = useLiveStreams()
  const channels = LIVE_CHANNELS.filter((c) => streams[c.key])
  const [channel, setChannel] = useState<LiveChannel | null>(channels[0]?.key ?? null)
  const [error, setError] = useState<string | null>(null)
  const videoRef = useRef<HTMLVideoElement>(null)
  const panelRef = useRef<HTMLDivElement>(null)
  const [box, setBox] = useState<Box>(initialBox)
  const [docked, setDocked] = useState(() => window.innerWidth < 640)
  const boxRef = useRef(box)
  boxRef.current = box

  useEffect(() => {
    const onResize = () => {
      setDocked(window.innerWidth < 640)
      setBox((b) => clampBox(b))
    }
    window.addEventListener('resize', onResize)
    return () => window.removeEventListener('resize', onResize)
  }, [])

  const persist = useCallback(() => {
    try {
      window.localStorage.setItem(POS_KEY, JSON.stringify(boxRef.current))
    } catch {
      // storage can be unavailable: position just won't be remembered
    }
  }, [])

  // One pointer-drag helper for both the title-bar move and the corner resize.
  const startDrag = (mode: 'move' | 'resize') => (e: React.PointerEvent) => {
    if (docked || (e.target as HTMLElement).closest('button')) return
    e.preventDefault()
    const start = { px: e.clientX, py: e.clientY, ...boxRef.current }
    const target = e.currentTarget as HTMLElement
    target.setPointerCapture(e.pointerId)
    const move = (ev: PointerEvent) => {
      const dx = ev.clientX - start.px
      const dy = ev.clientY - start.py
      setBox(clampBox(mode === 'move' ? { x: start.x + dx, y: start.y + dy, w: start.w } : { x: start.x, y: start.y, w: start.w + Math.max(dx, (dy * 16) / 9) }))
    }
    const up = () => {
      target.removeEventListener('pointermove', move)
      target.removeEventListener('pointerup', up)
      target.removeEventListener('pointercancel', up)
      persist()
    }
    target.addEventListener('pointermove', move)
    target.addEventListener('pointerup', up)
    target.addEventListener('pointercancel', up)
  }

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
    <div
      ref={panelRef}
      role="dialog"
      aria-label="Live vision"
      tabIndex={-1}
      style={docked ? undefined : { left: box.x, top: box.y, width: box.w }}
      className={`fixed z-[70] overflow-hidden border border-line bg-panel shadow-[var(--shadow-1)] outline-none ${docked ? 'inset-x-0 bottom-0 rounded-t-xl' : 'rounded-xl'}`}
    >
      <div
        onPointerDown={startDrag('move')}
        className={`flex items-center gap-2 px-3 py-1.5 touch-none select-none ${docked ? '' : 'cursor-move'}`}
        style={{ minHeight: HEADER_H }}
      >
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
      {!docked && (
        <div
          onPointerDown={startDrag('resize')}
          aria-label="Resize live vision"
          className="absolute bottom-0 right-0 h-5 w-5 cursor-nwse-resize touch-none"
          style={{ background: 'linear-gradient(135deg, transparent 55%, rgba(255,255,255,0.8) 55%, rgba(255,255,255,0.8) 65%, transparent 65%, transparent 78%, rgba(255,255,255,0.8) 78%, rgba(255,255,255,0.8) 88%, transparent 88%)' }}
        />
      )}
    </div>
  )
}
