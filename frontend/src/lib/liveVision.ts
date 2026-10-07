import { useCallback, useEffect, useState } from 'react'

// Live vision stream addresses (HLS .m3u8), entered by the user in Settings and kept ONLY in this browser's localStorage.
// Nothing here ships with a stream address: the app is a public page, so any address in the code or repo would hand a
// login-gated feed to everyone who opens it. Not part of the cross-device sync either, on purpose.
export type LiveChannel = 'sky1' | 'sky2' | 'tc'
export const LIVE_CHANNELS: { key: LiveChannel; label: string }[] = [
  { key: 'sky1', label: 'Sky 1' },
  { key: 'sky2', label: 'Sky 2' },
  { key: 'tc', label: 'Thoroughbred Central' },
]
export type LiveStreams = Partial<Record<LiveChannel, string>>

const STORAGE_KEY = 'toprate_live_streams_v1'
const EVENT = 'toprate-live-streams-changed'

export function isStreamUrl(s: string): boolean {
  try {
    const u = new URL(s.trim())
    return u.protocol === 'https:' && u.pathname.toLowerCase().endsWith('.m3u8')
  } catch {
    return false
  }
}

function read(): LiveStreams {
  try {
    const raw = window.localStorage.getItem(STORAGE_KEY)
    const obj = raw ? JSON.parse(raw) : {}
    const out: LiveStreams = {}
    for (const { key } of LIVE_CHANNELS) if (typeof obj[key] === 'string' && isStreamUrl(obj[key])) out[key] = obj[key]
    return out
  } catch {
    return {}
  }
}

export function useLiveStreams(): [LiveStreams, (channel: LiveChannel, url: string) => void] {
  const [streams, setStreams] = useState<LiveStreams>(read)
  useEffect(() => {
    const sync = () => setStreams(read())
    window.addEventListener(EVENT, sync)
    window.addEventListener('storage', sync)
    return () => {
      window.removeEventListener(EVENT, sync)
      window.removeEventListener('storage', sync)
    }
  }, [])
  const setStream = useCallback((channel: LiveChannel, url: string) => {
    const next = { ...read() }
    const v = url.trim()
    if (v && isStreamUrl(v)) next[channel] = v
    else delete next[channel]
    try {
      window.localStorage.setItem(STORAGE_KEY, JSON.stringify(next))
    } catch {
      // storage can be unavailable (private mode): the in-memory state below still works this session
    }
    setStreams(next)
    window.dispatchEvent(new Event(EVENT))
  }, [])
  return [streams, setStream]
}

// hls.js is only needed where the browser cannot play HLS itself (everything except Safari), so it is loaded on demand from
// a CDN rather than bundled into the single-file build.
type HlsCtor = new (cfg?: object) => {
  loadSource(u: string): void
  attachMedia(v: HTMLVideoElement): void
  on(ev: string, cb: (...a: any[]) => void): void // eslint-disable-line @typescript-eslint/no-explicit-any
  destroy(): void
}
type HlsStatic = HlsCtor & { isSupported(): boolean; Events: { MANIFEST_PARSED: string; ERROR: string } }
let hlsPromise: Promise<HlsStatic> | null = null
export function loadHls(): Promise<HlsStatic> {
  const w = window as unknown as { Hls?: HlsStatic }
  if (w.Hls) return Promise.resolve(w.Hls)
  if (!hlsPromise) {
    hlsPromise = new Promise((resolve, reject) => {
      const s = document.createElement('script')
      s.src = 'https://cdn.jsdelivr.net/npm/hls.js@1.5.17/dist/hls.min.js'
      s.onload = () => (w.Hls ? resolve(w.Hls) : reject(new Error('hls.js missing')))
      s.onerror = () => reject(new Error('hls.js failed to load'))
      document.head.appendChild(s)
    })
    hlsPromise.catch(() => {
      hlsPromise = null
    })
  }
  return hlsPromise
}
