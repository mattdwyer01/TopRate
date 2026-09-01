import type { FreshnessLevel } from '../hooks/useDashboardData'

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
  runDate: string
}

export function FreshnessDot({ level, runDate }: FreshnessDotProps) {
  return (
    <div className="flex items-center gap-1.5" title={`${levelLabels[level]} - last run ${runDate}`}>
      <span className={`h-2 w-2 flex-none rounded-full ${levelClasses[level]}`} />
      {/* Hidden below sm: at phone widths this text wraps onto a second line
          right next to the search/settings icons (the header row has no
          space for "01 Sep 2026 06:30 UTC" alongside the tabs + icons) - the
          colour-coded dot alone still conveys freshness at a glance, and the
          full date/time stays available via the title tooltip above. */}
      <span className="hidden whitespace-nowrap font-mono text-xs text-ink-mute sm:inline">
        {runDate}
      </span>
    </div>
  )
}
