// Two related features, both reachable from the Settings modal:
//  1. Fetch data - trigger .github/workflows/daily.yml (toprate_daily.py)
//     via GitHub's workflow_dispatch API, so a fresh pull can be kicked off
//     from the dashboard itself instead of the GitHub Actions UI.
//  2. Cross-device sync - push/pull this device's manual overrides and
//     view preferences to a private GitHub Gist, so a WPR override or
//     density choice made on one device shows up on the other.
//
// Both need a GitHub PAT. Same token works for both if it has the
// 'workflow' scope (dispatch) and 'gist' scope (sync) - a fine-grained PAT
// scoped to just this repo, or a classic PAT with those two scopes, both
// work. Stored in localStorage on this device only - never sent anywhere
// but api.github.com, never bundled into the built file.

import { readStoredPicks, writeStoredPicks, type StrategyPick } from './strategyPicks'

const CONFIG_KEY = 'toprate_gh_sync_v1'
const GIST_FILENAME = 'toprate_sync.json'
const DEFAULT_REPO = 'mattdwyer01/TopRate'

// The 4 pieces of this device's local state actually worth syncing (see
// lib/wprOverrides.ts, density.ts, priceBetaOverride.ts, bushMeetings.ts).
// ntj-collapsed (ticker visibility) is left out deliberately - it's
// display chrome, not a preference or data worth carrying across devices.
const DELTA_KEY = 'toprate_wpr_overrides_v1'
const BASE_KEY = 'toprate_manual_base_v1'
const DENSITY_KEY = 'toprate_race_table_compact_v1'
const BETA_KEY = 'toprate_price_beta_override_v1'
const BUSH_KEY = 'toprate_show_bush_meetings_v1'

export interface SyncConfig {
  pat: string
  repo: string
  gistId: string
}

export function readSyncConfig(): SyncConfig {
  try {
    const raw = window.localStorage.getItem(CONFIG_KEY)
    if (!raw) return { pat: '', repo: DEFAULT_REPO, gistId: '' }
    const parsed = JSON.parse(raw)
    return {
      pat: typeof parsed.pat === 'string' ? parsed.pat : '',
      repo: typeof parsed.repo === 'string' && parsed.repo ? parsed.repo : DEFAULT_REPO,
      gistId: typeof parsed.gistId === 'string' ? parsed.gistId : '',
    }
  } catch {
    return { pat: '', repo: DEFAULT_REPO, gistId: '' }
  }
}

export function writeSyncConfig(cfg: SyncConfig) {
  try {
    window.localStorage.setItem(CONFIG_KEY, JSON.stringify(cfg))
  } catch {
    // localStorage can throw in private-browsing/storage-full states - the
    // in-memory config still works for the rest of this session.
  }
}

function ghHeaders(pat: string): HeadersInit {
  return {
    Authorization: `Bearer ${pat}`,
    Accept: 'application/vnd.github+json',
    'X-GitHub-Api-Version': '2022-11-28',
  }
}

async function readErrorMessage(r: Response): Promise<string> {
  try {
    const body = await r.json()
    return typeof body.message === 'string' ? body.message : r.statusText
  } catch {
    return r.statusText
  }
}

// ---- Fetch data (workflow_dispatch) ----------------------------------

/** Trigger daily.yml. date: 'YYYY-MM-DD', or undefined for today (the
 * workflow's own default). Throws with a readable message on failure. */
export async function dispatchFetch(repo: string, pat: string, date?: string): Promise<string> {
  if (!pat) throw new Error('No GitHub token configured')
  if (!repo) throw new Error('No repo configured')

  const listR = await fetch(`https://api.github.com/repos/${repo}/actions/workflows`, {
    headers: ghHeaders(pat),
  })
  if (!listR.ok) {
    throw new Error(`Repo error ${listR.status} - token may need the 'workflow' scope`)
  }
  const listData = await listR.json()
  const workflows: { id: number; name: string; path: string }[] = listData.workflows || []
  const wf = workflows.find((w) => w.name === 'TopRate Daily' || w.path.includes('daily.yml')) ?? workflows[0]
  if (!wf) {
    throw new Error('No workflows found in this repo')
  }

  const dispR = await fetch(
    `https://api.github.com/repos/${repo}/actions/workflows/${wf.id}/dispatches`,
    {
      method: 'POST',
      headers: { ...ghHeaders(pat), 'Content-Type': 'application/json' },
      body: JSON.stringify({ ref: 'main', inputs: date ? { date } : {} }),
    }
  )
  if (dispR.status !== 204) {
    throw new Error(`Dispatch failed (${dispR.status}): ${await readErrorMessage(dispR)}`)
  }
  return `Triggered ${wf.name} for ${date ?? 'today'}. Data usually lands in a few minutes.`
}

// ---- Cross-device sync (private Gist) ---------------------------------

interface SyncPayload {
  version: number
  deviceTs: string
  wprDeltas: Record<string, number>
  wprBases: Record<string, number>
  density: string | null
  betaOverride: string | null
  showBush: string | null
  // Unlike the fields above (single-value preferences - whichever device
  // synced last simply wins), this is an additive log: losing a pick made
  // on another device would mean losing real tracked-bet history, so it's
  // always merged rather than overwritten on both pull and push.
  strategyPicks: Record<string, StrategyPick>
}

function readLocal(key: string): string | null {
  try {
    return window.localStorage.getItem(key)
  } catch {
    return null
  }
}

function readMap(key: string): Record<string, number> {
  const raw = readLocal(key)
  try {
    return raw ? JSON.parse(raw) : {}
  } catch {
    return {}
  }
}

export function buildSyncPayload(): SyncPayload {
  return {
    version: 1,
    deviceTs: new Date().toISOString(),
    wprDeltas: readMap(DELTA_KEY),
    wprBases: readMap(BASE_KEY),
    density: readLocal(DENSITY_KEY),
    betaOverride: readLocal(BETA_KEY),
    showBush: readLocal(BUSH_KEY),
    strategyPicks: readStoredPicks(),
  }
}

/** Writes a pulled payload back into this device's localStorage. Callers
 * should reload the page afterwards - the values are read once on mount
 * by each lib/*.ts hook, not reactively. */
export function applySyncPayload(payload: Partial<SyncPayload>) {
  try {
    if (payload.wprDeltas) window.localStorage.setItem(DELTA_KEY, JSON.stringify(payload.wprDeltas))
    if (payload.wprBases) window.localStorage.setItem(BASE_KEY, JSON.stringify(payload.wprBases))
    if (payload.density != null) window.localStorage.setItem(DENSITY_KEY, payload.density)
    if (payload.betaOverride != null) window.localStorage.setItem(BETA_KEY, payload.betaOverride)
    if (payload.showBush != null) window.localStorage.setItem(BUSH_KEY, payload.showBush)
    // Merged, not overwritten - see the SyncPayload.strategyPicks comment.
    if (payload.strategyPicks) {
      writeStoredPicks({ ...readStoredPicks(), ...payload.strategyPicks })
    }
  } catch {
    // Best-effort - a partial apply still leaves the device usable.
  }
}

async function gistRequest(method: string, path: string, pat: string, body?: unknown) {
  const r = await fetch(`https://api.github.com${path}`, {
    method,
    headers: body
      ? { ...ghHeaders(pat), 'Content-Type': 'application/json' }
      : ghHeaders(pat),
    body: body ? JSON.stringify(body) : undefined,
  })
  if (!r.ok) {
    throw new Error(`GitHub API ${r.status}: ${await readErrorMessage(r)}`)
  }
  return r.json()
}

export async function createGist(pat: string): Promise<string> {
  if (!pat) throw new Error('No GitHub token configured')
  const data = await gistRequest('POST', '/gists', pat, {
    description: 'TopRate dashboard sync',
    public: false,
    files: { [GIST_FILENAME]: { content: JSON.stringify(buildSyncPayload(), null, 2) } },
  })
  return data.id as string
}

export async function pullFromGist(pat: string, gistId: string): Promise<SyncPayload> {
  if (!pat || !gistId) throw new Error('Need both a token and a Gist ID')
  const data = await gistRequest('GET', `/gists/${gistId}`, pat)
  const file = data.files?.[GIST_FILENAME]
  if (!file?.content) throw new Error('Gist has no sync file yet - push from a device first')
  return JSON.parse(file.content) as SyncPayload
}

export async function pushToGist(pat: string, gistId: string): Promise<void> {
  if (!pat || !gistId) throw new Error('Need both a token and a Gist ID')
  // Strategy picks are additive (see SyncPayload.strategyPicks) - merge in
  // whatever's already in the Gist before overwriting it, so a push from
  // this device can never drop a pick tracked on another device since
  // this one's last pull. Also folds the merge back into this device's
  // own storage, so it doesn't regress on its own next pull.
  try {
    const remote = await pullFromGist(pat, gistId)
    if (remote.strategyPicks) {
      writeStoredPicks({ ...remote.strategyPicks, ...readStoredPicks() })
    }
  } catch {
    // No Gist content yet (first push) or a transient fetch failure -
    // fall through and push this device's own state as-is.
  }
  await gistRequest('PATCH', `/gists/${gistId}`, pat, {
    files: { [GIST_FILENAME]: { content: JSON.stringify(buildSyncPayload(), null, 2) } },
  })
}
