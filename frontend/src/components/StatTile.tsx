// One consolidated stat-tile component. The current dashboard has three
// near-identical implementations of this pattern (.pnl-stat, .acc-stat,
// .hero-stat - see rebuild plan) for P&L stats, Accuracy breakdown stats,
// and hero/summary stats. Collapsing them into one reusable component is a
// deliberate simplification called out in the plan, not scope creep.
interface StatTileProps {
  label: string
  value: string
  sublabel?: string
  tone?: 'default' | 'positive' | 'negative' | 'muted'
}

const toneClasses: Record<NonNullable<StatTileProps['tone']>, string> = {
  default: 'text-ink',
  positive: 'text-emerald',
  negative: 'text-rose',
  muted: 'text-ink-mute',
}

export function StatTile({ label, value, sublabel, tone = 'default' }: StatTileProps) {
  return (
    <div className="rounded-md border border-line bg-panel px-4 py-3 shadow-[var(--shadow-1)]">
      <div className="text-xs font-medium uppercase tracking-wide text-ink-mute">
        {label}
      </div>
      <div className={`mt-1 font-mono text-lg font-semibold ${toneClasses[tone]}`}>
        {value}
      </div>
      {sublabel && <div className="mt-0.5 text-xs text-ink-faint">{sublabel}</div>}
    </div>
  )
}
