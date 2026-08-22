import { useEffect, useRef, useState } from 'react'
import { useBodyScrollLock, useFocusTrap } from '../lib/modalA11y'

interface SettingsModalProps {
  serverBeta: number | null
  betaOverride: number | null
  onSetBetaOverride: (v: number | null) => void
  onClose: () => void
}

const MIN_BETA = 0.05
const MAX_BETA = 0.6
const STEP = 0.01

// Client-side settings, currently just the WPR $ price softmax beta. This
// is a per-device override, not a change to the pipeline's own calibrated
// value - it recomputes every displayed price live via lib/raceModel.ts,
// same mechanism as a manual per-runner adjustment, just applied to the
// whole field. Reachable from the header gear icon rather than a full
// settings page/route - the only setting so far doesn't warrant one yet.
export function SettingsModal({ serverBeta, betaOverride, onSetBetaOverride, onClose }: SettingsModalProps) {
  const effectiveBeta = betaOverride ?? serverBeta ?? 0.4
  const [draft, setDraft] = useState(effectiveBeta)
  const panelRef = useRef<HTMLDivElement>(null)

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
      </div>
    </div>
  )
}
