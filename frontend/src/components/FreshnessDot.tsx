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
}

export function FreshnessDot({ level, runIso, now }: FreshnessDotProps) {
  // The visible text is relative ("3m ago") so it's meaningful at a glance
  // without doing UTC-to-local arithmetic in your head; the full local
  // date/time (not the backend's raw UTC string) is still one hover away.
  const local = new Date(runIso).toLocaleString(undefined, { dateStyle: 'medium', timeStyle: 'short' })
  return (
    <div className="flex items-center gap-1.5" title={`${levelLabels[level]} - last run ${local}`}>
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
