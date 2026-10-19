import { useEffect, useRef, useState } from 'react'

interface HeaderMenuItem {
  label: string
  onSelect: () => void
  disabled?: boolean
}

// Phone-only "more" menu: refresh, help and settings live here below sm so the header row keeps room for the tabs, freshness dot, search
// and Live. From sm up the same actions are shown as inline icon buttons by App.tsx.
export function HeaderMenu({ items }: { items: HeaderMenuItem[] }) {
  const [open, setOpen] = useState(false)
  const ref = useRef<HTMLDivElement>(null)

  useEffect(() => {
    if (!open) return
    function onDown(e: MouseEvent | TouchEvent) {
      if (ref.current && !ref.current.contains(e.target as Node)) setOpen(false)
    }
    function onKey(e: KeyboardEvent) {
      if (e.key === 'Escape') setOpen(false)
    }
    document.addEventListener('mousedown', onDown)
    document.addEventListener('touchstart', onDown)
    document.addEventListener('keydown', onKey)
    return () => {
      document.removeEventListener('mousedown', onDown)
      document.removeEventListener('touchstart', onDown)
      document.removeEventListener('keydown', onKey)
    }
  }, [open])

  return (
    <div ref={ref} className="relative sm:hidden">
      <button
        type="button"
        aria-label="More"
        aria-haspopup="menu"
        aria-expanded={open}
        onClick={() => setOpen((o) => !o)}
        className="flex h-9 w-9 items-center justify-center rounded-md text-lg leading-none text-ink-mute transition-colors hover:bg-bg hover:text-ink"
      >
        <span aria-hidden="true">&#8943;</span>
      </button>
      {open && (
        <div role="menu" className="absolute right-0 top-full z-40 mt-1 w-48 overflow-hidden rounded-lg border border-line bg-panel py-1 shadow-[var(--shadow-2)]">
          {items.map((it) => (
            <button
              key={it.label}
              type="button"
              role="menuitem"
              disabled={it.disabled}
              onClick={() => {
                setOpen(false)
                it.onSelect()
              }}
              className="block w-full px-4 py-2.5 text-left text-sm text-ink transition-colors hover:bg-bg disabled:opacity-50"
            >
              {it.label}
            </button>
          ))}
        </div>
      )}
    </div>
  )
}
