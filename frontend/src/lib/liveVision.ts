import { useCallback, useEffect, useState } from 'react'

// Live vision stream addresses (HLS .m3u8). Built-in defaults below (hard-coded at the owner's explicit request, Oct 2026, knowing
// the app is a public page and these addresses are visible to anyone). A user can still override a channel in Settings (kept in this
// browser's localStorage, not part of the cross-device sync).
export type LiveChannel = 'sky1' | 'sky2' | 'tc'
export const LIVE_CHANNELS: { key: LiveChannel; label: string }[] = [
  { key: 'sky1', label: 'Sky 1' },
  { key: 'sky2', label: 'Sky 2' },
  { key: 'tc', label: 'Thoroughbred Central' },
]
export type LiveStreams = Partial<Record<LiveChannel, string>>

const DEFAULT_STREAMS: Record<LiveChannel, string> = {
  sky1: 'https://skylivetab-new.akamaized.net/hls/live/2038780/sky1/index.m3u8',
  sky2: 'https://skylivetab-new.akamaized.net/hls/live/2038781/sky2/index.m3u8',
  tc: 'https://skylivetab-new.akamaized.net/hls/live/2038782/stcsd/index.m3u8',
}

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
  const out: LiveStreams = { ...DEFAULT_STREAMS }
  try {
    const raw = window.localStorage.getItem(STORAGE_KEY)
    const obj = raw ? JSON.parse(raw) : {}
    for (const { key } of LIVE_CHANNELS) if (typeof obj[key] === 'string' && isStreamUrl(obj[key])) out[key] = obj[key]
  } catch {
    // fall back to the defaults
  }
  return out
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

// One-time setup link: opening <page>#live=<base64url of {"sky1":"https://...m3u8", ...}> saves those addresses in this browser and
// removes the fragment from the address bar. The fragment is never sent to a server, and the link is shared privately (the addresses
// are not in the code or repo). Only valid https .m3u8 addresses for the known channels are kept.
export function importLiveStreamsFromHash(): void {
  try {
    const m = /^#live=([A-Za-z0-9_-]+)$/.exec(window.location.hash)
    if (!m) return
    const b64 = m[1].replace(/-/g, '+').replace(/_/g, '/')
    const json = decodeURIComponent(escape(window.atob(b64 + '='.repeat((4 - (b64.length % 4)) % 4))))
    const obj = JSON.parse(json)
    const next = { ...read() }
    for (const { key } of LIVE_CHANNELS) if (typeof obj[key] === 'string' && isStreamUrl(obj[key])) next[key] = obj[key].trim()
    window.localStorage.setItem(STORAGE_KEY, JSON.stringify(next))
  } catch {
    // a malformed link is ignored
  } finally {
    try {
      window.history.replaceState(null, '', window.location.pathname + window.location.search)
    } catch {
      // ignore
    }
  }
}
