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

export async function fetchDashboardData(): Promise<DashboardData> {
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
    raw = await response.json()
  } catch (err) {
    throw new DashboardDataError(
      `${DATA_FILE} was not valid JSON: ${(err as Error).message}`,
    )
  }
  return adaptDashboardPayload(raw)
}
