import type { RawDashboardPayload } from '../types/data'
import { adaptDashboardPayload } from './adapter'
import type { DashboardData } from '../types/domain'

// Same file name and fetch approach as the current dashboard
// (toprate_html_v3.py __bootDashboard, L5427-5462): a separate fetched JSON
// file rather than an inlined blob, specifically to avoid the browser having
// to JS-parse a huge literal embedded in the page itself. Cache-busted with
// no-cache so a stale service-worker/browser cache never shows old races.
const DATA_FILE = 'toprate_data.json'

export class DashboardDataError extends Error {}

// toprate_data.json runs ~90MB (45 days of race/form history windowed in),
// so a plain response.json() gives no feedback for tens of seconds on a
// slow connection. Streams the body instead when the server sends
// Content-Length, reporting 0-99 as bytes arrive (holding back 100 until
// JSON.parse actually succeeds, so the bar never claims "done" while still
// parsing). Falls back to a plain response.json() when streaming isn't
// available (missing Content-Length, or a browser without
// ReadableStream.getReader on Response bodies).
export async function fetchDashboardData(onProgress?: (pct: number) => void): Promise<DashboardData> {
  let response: Response
  try {
    response = await fetch(DATA_FILE, { cache: 'no-cache' })
  } catch (err) {
    throw new DashboardDataError(
      `Could not reach ${DATA_FILE}: ${(err as Error).message}`,
    )
  }
  if (!response.ok) {
    throw new DashboardDataError(
      `${DATA_FILE} returned HTTP ${response.status}`,
    )
  }

  let raw: RawDashboardPayload
  try {
    const total = Number(response.headers.get('content-length') ?? 0)
    if (onProgress && total > 0 && response.body) {
      const reader = response.body.getReader()
      const decoder = new TextDecoder()
      let text = ''
      let received = 0
      for (;;) {
        const { done, value } = await reader.read()
        if (done) break
        text += decoder.decode(value, { stream: true })
        received += value.length
        onProgress(Math.min(99, Math.round((received / total) * 100)))
      }
      text += decoder.decode()
      raw = JSON.parse(text)
      onProgress(100)
    } else {
      raw = await response.json()
    }
  } catch (err) {
    throw new DashboardDataError(
      `${DATA_FILE} was not valid JSON: ${(err as Error).message}`,
    )
  }
  return adaptDashboardPayload(raw)
}
