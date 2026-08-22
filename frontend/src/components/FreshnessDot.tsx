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
      <span className={`h-2 w-2 rounded-full ${levelClasses[level]}`} />
      <span className="text-xs text-ink-mute font-mono">{runDate}</span>
    </div>
  )
}
