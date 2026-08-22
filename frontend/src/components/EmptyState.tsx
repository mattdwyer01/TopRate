// Two visually distinct states, matching the current dashboard's deliberate
// design choice (toprate_html_v3.py __bootDashboard catch block, L5450-5461):
// a genuine "nothing here" empty state reads as neutral, while a fetch
// FAILURE is rose-accented with a retry button, so the two situations never
// look the same to the user.

interface EmptyStateProps {
  message: string
  // 0-100, or null/omitted for no bar (e.g. length unknown, or a state
  // that isn't a data load at all). toprate_data.json runs ~90MB, so this
  // is the difference between a frozen-looking screen and visible progress
  // on a slow connection.
  progress?: number | null
}

export function EmptyState({ message, progress }: EmptyStateProps) {
  return (
    <div className="rounded-lg border border-line-soft bg-panel px-6 py-10 text-center text-ink-mute">
      <p>{message}</p>
      {progress != null && (
        <div className="mx-auto mt-3 h-1.5 w-48 overflow-hidden rounded-full bg-line-soft">
          <div
            className="h-full rounded-full bg-emerald transition-[width]"
            style={{ width: `${progress}%` }}
          />
        </div>
      )}
    </div>
  )
}

interface ErrorStateProps {
  message: string
  onRetry: () => void
}

export function ErrorState({ message, onRetry }: ErrorStateProps) {
  return (
    <div className="rounded-lg border border-rose-line bg-rose-bg px-6 py-10 text-center">
      <p className="text-rose font-medium">Couldn't load the dashboard</p>
      <p className="mt-1 text-sm text-ink-mute">{message}</p>
      <button
        type="button"
        onClick={onRetry}
        className="mt-4 rounded-md border border-rose-line bg-panel px-4 py-1.5 text-sm font-medium text-rose transition-colors hover:bg-rose-bg"
      >
        Retry
      </button>
    </div>
  )
}
