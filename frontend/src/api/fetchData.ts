import type { RawDashboardPayload } from '../types/data'
import { adaptDashboardPayload } from './adapter'
import type { DashboardData } from '../types/domain'

// Same file name and fetch approach as the current dashboard
// (toprate_html_v3.py __bootDashboard, L5427-5462): a separate fetched JSON
// file rather than an inlined blob, specifically to avoid the browser having
// to JS-parse a huge literal embedded in the page itself. Cache-busted with
// no-cache so a stale service-worker/browser cache never shows old races.
const DATA_FILE = 'toprate_data.json'

// Gzip companion (Sep 2026, see toprate_daily.py's _write_data_json) -
// real mobile Safari report of multi-minute loads traced to GitHub Pages'
// CDN not compressing files this large (community-reported ceiling around
// ~10MB - toprate_data.json runs ~85-90MB). Fetching this instead and
// decompressing client-side cuts the download to ~1/5 the size (measured:
// 86MB -> 17.5MB) for identical data. Always written alongside
// toprate_data.json itself (every write site goes through the shared
// helper), so the two can never drift apart on the server - if this fetch
// ever 404s/fails for some other reason (a very old cached deploy, a CDN
// hiccup), fetchDashboardData() below falls back to the plain file rather
// than surfacing an error.
const DATA_FILE_GZ = 'toprate_data.json.gz'

export class DashboardDataError extends Error {}

function supportsGzipDecompression(): boolean {
  return typeof DecompressionStream !== 'undefined'
}

// Wraps already-downloaded gzip bytes in a Blob purely to get a stream to
// pipe through DecompressionStream (the standard, no-extra-dependency way
// to gunzip in a browser) - no data is actually re-read from disk/network,
// the Blob is just an in-memory adapter.
async function decompressGzipBytes(bytes: Uint8Array<ArrayBuffer>): Promise<string> {
  const stream = new Blob([bytes]).stream().pipeThrough(new DecompressionStream('gzip'))
  return new Response(stream).text()
}

async function fetchOk(url: string): Promise<Response> {
  let response: Response
  try {
    response = await fetch(url, { cache: 'no-cache' })
  } catch (err) {
    throw new DashboardDataError(`Could not reach ${url}: ${(err as Error).message}`)
  }
  if (!response.ok) {
    throw new DashboardDataError(`${url} returned HTTP ${response.status}`)
  }
  return response
}

// toprate_data.json runs ~90MB (45 days of race/form history windowed in),
// so a plain response.json() gives no feedback for tens of seconds on a
// slow connection. Streams the body instead when the server sends
// Content-Length, reporting 0-99 as bytes arrive (holding back 100 until
// JSON.parse actually succeeds, so the bar never claims "done" while still
// parsing). Falls back to a plain response.json() when streaming isn't
// available (missing Content-Length, or a browser without
// ReadableStream.getReader on Response bodies).
//
// Two things this deliberately avoids, both of which made an earlier
// version of this function slower than the plain response.json() it
// replaced: decoding+string-concatenating on every chunk (bytes are
// collected raw and decoded ONCE at the end instead - a 90MB file can
// arrive in a four-figure number of chunks, and repeated decode+concat
// added real overhead across all of them), and calling onProgress on every
// chunk (network chunks arrive far more often than the percentage actually
// changes, and each call is a React state update/re-render - throttled to
// fire only when the rounded percentage moves).
export async function fetchDashboardData(onProgress?: (pct: number) => void): Promise<DashboardData> {
  const canDecompress = supportsGzipDecompression()
  let response: Response
  let isGzip = false
  if (canDecompress) {
    try {
      response = await fetchOk(DATA_FILE_GZ)
      // If the CDN already declares Content-Encoding: gzip for this file,
      // fetch() has transparently decompressed the body for us already
      // (that's the Fetch spec's job, below the level a Response exposes)
      // - decompressing it again ourselves would just throw on data that
      // is no longer actually gzip-framed. Only run our own
      // DecompressionStream step when the server sent the raw gzip bytes
      // as-is (no Content-Encoding, or something other than gzip).
      isGzip = response.headers.get('content-encoding') !== 'gzip'
    } catch {
      // .gz missing/blocked/stale - fall back to the plain file. Only ITS
      // failure (network/HTTP) should actually surface to the caller.
      response = await fetchOk(DATA_FILE)
    }
  } else {
    response = await fetchOk(DATA_FILE)
  }

  let raw: RawDashboardPayload
  try {
    const total = Number(response.headers.get('content-length') ?? 0)
    let text: string
    if (onProgress && total > 0 && response.body) {
      const reader = response.body.getReader()
      const chunks: Uint8Array[] = []
      let received = 0
      let lastPct = -1
      for (;;) {
        const { done, value } = await reader.read()
        if (done) break
        chunks.push(value)
        received += value.length
        // Progress tracks bytes actually transferred over the network
        // (the compressed size when isGzip), which is what a user waiting
        // on a slow connection cares about - decompression itself is fast
        // enough afterward not to need its own progress step.
        const pct = Math.min(99, Math.round((received / total) * 100))
        if (pct !== lastPct) {
          lastPct = pct
          onProgress(pct)
        }
      }
      const merged = new Uint8Array(received)
      let offset = 0
      for (const chunk of chunks) {
        merged.set(chunk, offset)
        offset += chunk.length
      }
      text = isGzip ? await decompressGzipBytes(merged) : new TextDecoder().decode(merged)
      onProgress(100)
    } else if (isGzip) {
      text = await decompressGzipBytes(new Uint8Array(await response.arrayBuffer()))
    } else {
      text = await response.text()
    }
    raw = JSON.parse(text)
  } catch (err) {
    throw new DashboardDataError(
      `${DATA_FILE} was not valid JSON: ${(err as Error).message}`,
    )
  }
  return adaptDashboardPayload(raw)
}
