import { useEffect, useRef, useState } from 'react'

// Tracks whether a horizontally-scrollable element has more content past
// its right edge, so a caller can show a fade-out affordance instead of
// silently truncating content with no hint there's more to scroll to
// (the meetings grid and next-to-jump ticker both cut off mid-row on
// narrow screens with nothing indicating it).
export function useScrollShadow<T extends HTMLElement>() {
  const ref = useRef<T>(null)
  const [canScrollRight, setCanScrollRight] = useState(false)

  useEffect(() => {
    const el = ref.current
    if (!el) return

    function update() {
      if (!el) return
      setCanScrollRight(el.scrollWidth - el.scrollLeft - el.clientWidth > 4)
    }

    update()
    el.addEventListener('scroll', update, { passive: true })
    const ro = new ResizeObserver(update)
    ro.observe(el)
    window.addEventListener('resize', update)
    return () => {
      el.removeEventListener('scroll', update)
      ro.disconnect()
      window.removeEventListener('resize', update)
    }
  }, [])

  return { ref, canScrollRight }
}
