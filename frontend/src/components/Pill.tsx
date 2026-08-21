import type { ReactNode } from 'react'

// Reusable pill/chip - the current dashboard's .subtabs-row/.subtab and
// .wpr-pill/.state-pill patterns collapse into this one component (used for
// the density toggle, filter chips, sub-tab selectors, and status badges).
interface PillProps {
  children: ReactNode
  active?: boolean
  onClick?: () => void
  tone?: 'default' | 'emerald' | 'rose' | 'amber' | 'slate'
}

const toneClasses: Record<NonNullable<PillProps['tone']>, string> = {
  default: 'border-line bg-panel text-ink-soft',
  emerald: 'border-emerald-line bg-emerald-bg text-emerald-deep',
  rose: 'border-rose-line bg-rose-bg text-rose',
  amber: 'border-amber-line bg-amber-bg text-amber',
  slate: 'border-line bg-slate-bg text-slate',
}

export function Pill({ children, active, onClick, tone = 'default' }: PillProps) {
  const interactive = typeof onClick === 'function'
  const activeClasses = active
    ? 'border-emerald bg-emerald text-white'
    : toneClasses[tone]
  return (
    <button
      type="button"
      onClick={onClick}
      disabled={!interactive}
      className={`inline-flex items-center rounded-full border px-3 py-1 text-xs font-medium transition-colors ${activeClasses} ${interactive ? 'cursor-pointer hover:opacity-80' : 'cursor-default'}`}
    >
      {children}
    </button>
  )
}
