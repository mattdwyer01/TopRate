import { useEffect, useState } from 'react'

const SECTIONS: { id: string; label: string }[] = [
  { id: 'rv-strike', label: 'Strike rates' },
  { id: 'rv-market', label: 'Market' },
  { id: 'rv-trend', label: 'Trends' },
  { id: 'rv-diag', label: 'Diagnostics' },
  { id: 'rv-quaddie', label: 'Quaddie' },
  { id: 'rv-days', label: 'Day by day' },
]

// A sticky row of jump links under the app header, so a long Review page (the phone page runs to several screens) can be navigated without
// scrolling past everything. Only sections that are actually on the page get a link; the one in view is highlighted.
export function ReviewNav() {
  const [top, setTop] = useState(0)
  const [present, setPresent] = useState<string[]>([])
  const [active, setActive] = useState<string | null>(null)

  useEffect(() => {
    const hdr = document.querySelector('header.sticky') as HTMLElement | null
    const h = () => hdr?.getBoundingClientRect().height ?? 0
    setTop(h())
    const found = SECTIONS.filter((s) => document.getElementById(s.id)).map((s) => s.id)
    setPresent(found)
    const els = found.map((id) => document.getElementById(id) as HTMLElement)
    const io = new IntersectionObserver(
      (entries) => {
        const seen = entries.filter((e) => e.isIntersecting).sort((a, b) => a.boundingClientRect.top - b.boundingClientRect.top)[0]
        if (seen) setActive(seen.target.id)
      },
      { rootMargin: `-${Math.round(h()) + 40}px 0px -55% 0px` },
    )
    els.forEach((el) => io.observe(el))
    const onResize = () => setTop(h())
    window.addEventListener('resize', onResize)
    return () => {
      io.disconnect()
      window.removeEventListener('resize', onResize)
    }
  }, [])

  return (
    <nav aria-label="Review sections" style={{ top }} className="sticky z-20 -mx-1 overflow-x-auto rounded-lg border border-line bg-panel/95 px-2 py-1.5 shadow-[var(--shadow-1)] backdrop-blur">
      <ul className="flex w-max gap-1.5">
        {SECTIONS.filter((s) => present.includes(s.id)).map((s) => (
          <li key={s.id}>
            <button
              type="button"
              onClick={() => document.getElementById(s.id)?.scrollIntoView({ behavior: 'smooth', block: 'start' })}
              aria-current={active === s.id ? 'true' : undefined}
              className={`whitespace-nowrap rounded-full border px-2.5 py-1 text-xs font-medium transition-colors ${active === s.id ? 'border-emerald-line bg-emerald-bg text-emerald-deep' : 'border-line bg-bg text-ink-mute hover:text-ink'}`}
            >
              {s.label}
            </button>
          </li>
        ))}
      </ul>
    </nav>
  )
}
