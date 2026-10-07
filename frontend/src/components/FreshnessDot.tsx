import type { FreshnessLevel } from '../hooks/useDashboardData'
import { formatRelativeAge } from '../lib/countdown'

// Header freshness indicator - green/amber/red by data age, matching the
// current dashboard's #freshness-dot behavior.
const levelClasses: Record<FreshnessLevel, string> = {
  fresh: 'bg-emerald',
  aging: 'bg-amber',
  stale: 'bg-rose',
}

const levelLabels: Record<FreshnessLevel, string> = {
  fresh: 'Data is fresh',
  aging: 'Data is aging',
  stale: 'Data is stale',
}

interface FreshnessDotProps {
  level: FreshnessLevel
  runIso: string
  now: number
  // Set when no race is within the poller's window (it reads prices and results only for races from 30 min ago to 2 h ahead), so the
  // file legitimately stops changing: the age is not a fault. Holds the next jump time.
  quietNext?: Date | null
  // A background poll failed since the last good load: the data on screen may be out of date.
  pollFailed?: boolean
}

export function FreshnessDot({ level, runIso, now, quietNext, pollFailed }: FreshnessDotProps) {
  if (pollFailed) {
    return (
      <div className="flex items-center gap-1.5" role="status" title="Could not reach the server on the last refresh. Showing the last data loaded.">
        <span className="h-2 w-2 flex-none rounded-full bg-rose" />
        <span className="whitespace-nowrap font-mono text-xs text-rose">Offline</span>
      </div>
    )
  }
  if (quietNext !== undefined && level !== 'fresh') {
    const at = quietNext ? quietNext.toLocaleTimeString(undefined, { hour: 'numeric', minute: '2-digit' }) : null
    const local0 = new Date(runIso).toLocaleString(undefined, { dateStyle: 'medium', timeStyle: 'short' })
    return (
      <div
        className="flex items-center gap-1.5"
        title={`Up to date. No race is within 2 hours, so prices and results are not polled and the data has not changed. Last change ${local0}.`}
      >
        <span className="h-2 w-2 flex-none rounded-full bg-emerald" />
        <span className="hidden whitespace-nowrap font-mono text-xs text-ink-mute sm:inline">{at ? `quiet, next ${at}` : 'quiet, no more races'}</span>
      </div>
    )
  }
  // The visible text is relative ("3m ago") so it's meaningful at a glance
  // without doing UTC-to-local arithmetic in your head; the full local
  // date/time (not the backend's raw UTC string) is still one hover away.
  const local = new Date(runIso).toLocaleString(undefined, { dateStyle: 'medium', timeStyle: 'short' })
  return (
    <div className="flex items-center gap-1.5" role="img" aria-label={`${levelLabels[level]}, updated ${formatRelativeAge(runIso, now)}`} title={`${levelLabels[level]} - last run ${local}`}>
      <span className={`h-2 w-2 flex-none rounded-full ${levelClasses[level]}`} />
      {/* Hidden below sm: at phone widths this text wraps onto a second line
          right next to the search/settings icons (the header row has no
          space for it alongside the tabs + icons) - the colour-coded dot
          alone still conveys freshness at a glance, and the full date/time
          stays available via the title tooltip above. */}
      <span className="hidden whitespace-nowrap font-mono text-xs text-ink-mute sm:inline">
        {formatRelativeAge(runIso, now)}
      </span>
    </div>
  )
}
