import { useEffect, useRef, useState } from 'react'
import { useBodyScrollLock, useFocusTrap } from '../lib/modalA11y'
import {
  applySyncPayload,
  createGist,
  dispatchFetch,
  pullFromGist,
  pushToGist,
  readSyncConfig,
  writeSyncConfig,
} from '../lib/githubSync'
import { todayIso } from '../lib/meetings'

interface SettingsModalProps {
  serverBeta: number | null
  betaOverride: number | null
  onSetBetaOverride: (v: number | null) => void
  onClose: () => void
  onOpenMethodology: () => void
}

const MIN_BETA = 0.05
const MAX_BETA = 0.6
const STEP = 0.01

type Status = { kind: 'idle' | 'busy' | 'ok' | 'err'; text: string }
const IDLE: Status = { kind: 'idle', text: '' }

// Client-side settings: WPR $ price sharpness, triggering a fresh data
// fetch, and cross-device sync. All per-device (localStorage), reachable
// from the header gear icon rather than a full settings page/route.
export function SettingsModal({
  serverBeta,
  betaOverride,
  onSetBetaOverride,
  onClose,
  onOpenMethodology,
}: SettingsModalProps) {
  const effectiveBeta = betaOverride ?? serverBeta ?? 0.4
  const [draft, setDraft] = useState(effectiveBeta)
  const panelRef = useRef<HTMLDivElement>(null)

  const [cfg, setCfg] = useState(() => readSyncConfig())
  const [fetchDate, setFetchDate] = useState(todayIso())
  const [fetchStatus, setFetchStatus] = useState<Status>(IDLE)
  const [syncStatus, setSyncStatus] = useState<Status>(IDLE)

  useBodyScrollLock()
  useFocusTrap(panelRef)

  useEffect(() => {
    function onKey(e: KeyboardEvent) {
      if (e.key === 'Escape') onClose()
    }
    window.addEventListener('keydown', onKey)
    return () => window.removeEventListener('keydown', onKey)
  }, [onClose])

  function commit(v: number) {
    const clamped = Math.min(MAX_BETA, Math.max(MIN_BETA, v))
    setDraft(clamped)
    onSetBetaOverride(clamped)
  }

  function updateCfg(patch: Partial<typeof cfg>) {
    const next = { ...cfg, ...patch }
    setCfg(next)
    writeSyncConfig(next)
  }

  async function handleFetch(date: string | undefined, label: string) {
    setFetchStatus({ kind: 'busy', text: `${label}...` })
    try {
      const msg = await dispatchFetch(cfg.repo, cfg.pat, date)
      setFetchStatus({ kind: 'ok', text: msg })
    } catch (e) {
      setFetchStatus({ kind: 'err', text: e instanceof Error ? e.message : 'Failed' })
    }
  }

  async function handleCreateGist() {
    setSyncStatus({ kind: 'busy', text: 'Creating Gist...' })
    try {
      const id = await createGist(cfg.pat)
      updateCfg({ gistId: id })
      setSyncStatus({ kind: 'ok', text: `Created Gist ${id.slice(0, 8)}... - use the same ID on your other device.` })
    } catch (e) {
      setSyncStatus({ kind: 'err', text: e instanceof Error ? e.message : 'Failed' })
    }
  }

  async function handlePull() {
    setSyncStatus({ kind: 'busy', text: 'Pulling...' })
    try {
      const payload = await pullFromGist(cfg.pat, cfg.gistId)
      applySyncPayload(payload)
      setSyncStatus({ kind: 'ok', text: 'Pulled. Reloading to apply...' })
      window.setTimeout(() => window.location.reload(), 800)
    } catch (e) {
      setSyncStatus({ kind: 'err', text: e instanceof Error ? e.message : 'Failed' })
    }
  }

  async function handlePush() {
    setSyncStatus({ kind: 'busy', text: 'Pushing...' })
    try {
      await pushToGist(cfg.pat, cfg.gistId)
      setSyncStatus({ kind: 'ok', text: 'Pushed. Pull from your other device to pick it up.' })
    } catch (e) {
      setSyncStatus({ kind: 'err', text: e instanceof Error ? e.message : 'Failed' })
    }
  }

  return (
    <div className="fixed inset-0 z-40 flex items-start justify-center overflow-y-auto bg-ink/60 p-3 sm:items-center sm:p-6" onClick={onClose}>
      <div
        ref={panelRef}
        role="dialog"
        aria-modal="true"
        aria-label="Settings"
        tabIndex={-1}
        className="w-full max-w-md rounded-lg bg-panel shadow-[var(--shadow-2)] outline-none"
        onClick={(e) => e.stopPropagation()}
      >
        <div className="flex items-center justify-between border-b border-line px-4 py-3">
          <span className="text-base font-semibold text-ink">Settings</span>
          <button
            type="button"
            onClick={onClose}
            className="flex h-8 w-8 items-center justify-center rounded-md text-ink-mute transition-colors hover:bg-bg hover:text-ink"
            aria-label="Close"
          >
            ✕
          </button>
        </div>

        <div className="flex flex-col divide-y divide-line-soft">
          <div className="flex flex-col gap-3 p-4">
            <div>
              <div className="mb-1 flex items-baseline justify-between">
                <span className="text-sm font-semibold text-ink">WPR $ price sharpness (beta)</span>
                <span className="font-mono text-lg font-semibold text-emerald-deep">{draft.toFixed(2)}</span>
              </div>
              <p className="text-xs text-ink-mute">
                Controls how much a WPR gap between runners shows up as a price gap. Higher = favourites priced
                shorter and outsiders longer; lower = prices closer together across the field.
              </p>
            </div>

            <input
              type="range"
              min={MIN_BETA}
              max={MAX_BETA}
              step={STEP}
              value={draft}
              onChange={(e) => commit(Number(e.target.value))}
              className="w-full accent-emerald"
            />

            <div className="flex items-center gap-2">
              <label className="flex items-center gap-2 text-sm text-ink-soft">
                Exact value
                <input
                  type="number"
                  min={MIN_BETA}
                  max={MAX_BETA}
                  step={STEP}
                  value={draft}
                  onChange={(e) => commit(Number(e.target.value))}
                  className="w-24 rounded-md border border-line bg-panel px-2 py-1 font-mono text-sm"
                />
              </label>
              {betaOverride != null && (
                <button
                  type="button"
                  onClick={() => {
                    onSetBetaOverride(null)
                    setDraft(serverBeta ?? 0.4)
                  }}
                  className="text-xs text-ink-mute underline hover:text-ink"
                >
                  Reset to default
                </button>
              )}
            </div>

            {serverBeta != null && (
              <p className="text-xs text-ink-faint">
                Pipeline's own current value is {serverBeta.toFixed(2)}. This override only changes what's
                displayed on this device - it doesn't change the pipeline or the underlying WPR projections, only
                how they're converted to a price.
              </p>
            )}
          </div>

          <div className="flex flex-col gap-2 p-4">
            <span className="text-sm font-semibold text-ink">How WPR is calculated</span>
            <p className="text-xs text-ink-mute">
              The full base + adjustment methodology, each term explained, and a worked example using a real
              runner's real numbers.
            </p>
            <button
              type="button"
              onClick={onOpenMethodology}
              className="self-start text-sm font-medium text-emerald-deep underline hover:text-emerald"
            >
              Read the methodology &rarr;
            </button>
          </div>

          <div className="flex flex-col gap-3 p-4">
            <div>
              <span className="text-sm font-semibold text-ink">GitHub token</span>
              <p className="text-xs text-ink-mute">
                A fine-grained PAT scoped to this repo (Actions: write, Contents: read for fetch; Gists: write for
                sync), or a classic PAT with the <code className="font-mono">workflow</code> and{' '}
                <code className="font-mono">gist</code> scopes. Stored in this browser's localStorage only - never
                sent anywhere but api.github.com, never bundled into the site.
              </p>
            </div>
            <input
              type="password"
              autoComplete="off"
              placeholder="ghp_... or github_pat_..."
              value={cfg.pat}
              onChange={(e) => updateCfg({ pat: e.target.value.trim() })}
              className="w-full rounded-md border border-line bg-panel px-2 py-1.5 font-mono text-sm"
            />
            <label className="flex items-center gap-2 text-xs text-ink-soft">
              Repo
              <input
                type="text"
                value={cfg.repo}
                onChange={(e) => updateCfg({ repo: e.target.value.trim() })}
                className="flex-1 rounded-md border border-line bg-panel px-2 py-1 font-mono text-xs"
              />
            </label>
          </div>

          <div className="flex flex-col gap-2 p-4">
            <span className="text-sm font-semibold text-ink">Fetch data</span>
            <p className="text-xs text-ink-mute">
              Triggers the daily pipeline (fetches races from toprate.au and rebuilds the data). Takes a few
              minutes to land.
            </p>
            <div className="flex flex-wrap items-center gap-2">
              <button
                type="button"
                onClick={() => handleFetch(undefined, 'Fetching today')}
                disabled={fetchStatus.kind === 'busy'}
                className="rounded-md bg-emerald px-3 py-1.5 text-sm font-medium text-white transition-colors hover:opacity-90 disabled:opacity-50"
              >
                Fetch today
              </button>
              <input
                type="date"
                value={fetchDate}
                onChange={(e) => setFetchDate(e.target.value)}
                className="rounded-md border border-line bg-panel px-2 py-1 text-sm"
              />
              <button
                type="button"
                onClick={() => handleFetch(fetchDate, `Fetching ${fetchDate}`)}
                disabled={fetchStatus.kind === 'busy' || !fetchDate}
                className="rounded-md border border-line px-3 py-1.5 text-sm font-medium text-ink transition-colors hover:bg-bg disabled:opacity-50"
              >
                Fetch this date
              </button>
            </div>
            {fetchStatus.text && (
              <p
                className={
                  'text-xs ' +
                  (fetchStatus.kind === 'err' ? 'text-rose' : fetchStatus.kind === 'ok' ? 'text-emerald-deep' : 'text-ink-mute')
                }
              >
                {fetchStatus.text}
              </p>
            )}
          </div>

          <div className="flex flex-col gap-2 p-4">
            <span className="text-sm font-semibold text-ink">Cross-device sync</span>
            <p className="text-xs text-ink-mute">
              Syncs manual WPR overrides, view preferences, and tracked Strategy picks between devices via a
              private Gist. Create one on your first device, then paste the same Gist ID on the others.
            </p>
            <label className="flex items-center gap-2 text-xs text-ink-soft">
              Gist ID
              <input
                type="text"
                placeholder="abc123..."
                value={cfg.gistId}
                onChange={(e) => updateCfg({ gistId: e.target.value.trim() })}
                className="flex-1 rounded-md border border-line bg-panel px-2 py-1 font-mono text-xs"
              />
            </label>
            <div className="flex flex-wrap items-center gap-2">
              {!cfg.gistId && (
                <button
                  type="button"
                  onClick={handleCreateGist}
                  disabled={syncStatus.kind === 'busy' || !cfg.pat}
                  className="rounded-md border border-line px-3 py-1.5 text-sm font-medium text-ink transition-colors hover:bg-bg disabled:opacity-50"
                >
                  Create new Gist
                </button>
              )}
              <button
                type="button"
                onClick={handlePull}
                disabled={syncStatus.kind === 'busy' || !cfg.pat || !cfg.gistId}
                className="rounded-md bg-emerald px-3 py-1.5 text-sm font-medium text-white transition-colors hover:opacity-90 disabled:opacity-50"
              >
                Pull from Gist
              </button>
              <button
                type="button"
                onClick={handlePush}
                disabled={syncStatus.kind === 'busy' || !cfg.pat || !cfg.gistId}
                className="rounded-md bg-emerald px-3 py-1.5 text-sm font-medium text-white transition-colors hover:opacity-90 disabled:opacity-50"
              >
                Push to Gist
              </button>
            </div>
            {syncStatus.text && (
              <p
                className={
                  'text-xs ' +
                  (syncStatus.kind === 'err' ? 'text-rose' : syncStatus.kind === 'ok' ? 'text-emerald-deep' : 'text-ink-mute')
                }
              >
                {syncStatus.text}
              </p>
            )}
          </div>
        </div>
      </div>
    </div>
  )
}
