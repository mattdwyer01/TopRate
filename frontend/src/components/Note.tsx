import { useState, type ReactNode } from 'react'

// A one-line caption with a "?" that opens the longer explanation on tap or click. For the explainer text that used to sit open under headings.
export function Note({ short, children, className = '' }: { short: string; children: ReactNode; className?: string }) {
  const [open, setOpen] = useState(false)
  return (
    <div className={`text-xs text-ink-faint ${className}`}>
      <span>{short}</span>
      <button
        type="button"
        onClick={() => setOpen((v) => !v)}
        aria-expanded={open}
        aria-label={open ? 'Hide explanation' : 'Show explanation'}
        className="ml-1.5 inline-flex h-4 w-4 items-center justify-center rounded-full border border-line text-[10px] font-semibold leading-none text-ink-mute hover:text-ink"
      >
        ?
      </button>
      {open && <p className="mt-1 text-ink-mute">{children}</p>}
    </div>
  )
}
