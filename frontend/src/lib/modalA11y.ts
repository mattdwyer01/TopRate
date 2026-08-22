import { useEffect, useRef, type RefObject } from 'react'

// Locks background scroll while a modal is mounted. Restores whatever
// overflow value was already set (rather than assuming empty string) so it
// doesn't clobber anything else that might be managing it.
export function useBodyScrollLock() {
  useEffect(() => {
    const prev = document.body.style.overflow
    document.body.style.overflow = 'hidden'
    return () => {
      document.body.style.overflow = prev
    }
  }, [])
}

const FOCUSABLE_SELECTOR =
  'a[href], button:not([disabled]), input:not([disabled]), select:not([disabled]), textarea:not([disabled]), [tabindex]:not([tabindex="-1"])'

// Keeps Tab/Shift+Tab cycling within the modal panel instead of escaping
// into the dimmed page behind it, focuses the panel on open, and restores
// focus to whatever triggered the modal once it closes - standard
// modal-dialog keyboard behaviour that a plain fixed-overlay div doesn't
// get for free.
export function useFocusTrap(containerRef: RefObject<HTMLElement | null>) {
  const previouslyFocused = useRef<HTMLElement | null>(null)

  useEffect(() => {
    previouslyFocused.current = document.activeElement as HTMLElement | null
    containerRef.current?.focus()

    function onKeyDown(e: KeyboardEvent) {
      if (e.key !== 'Tab' || !containerRef.current) return
      const focusable = Array.from(containerRef.current.querySelectorAll<HTMLElement>(FOCUSABLE_SELECTOR))
      if (focusable.length === 0) return
      const first = focusable[0]
      const last = focusable[focusable.length - 1]
      if (e.shiftKey && document.activeElement === first) {
        e.preventDefault()
        last.focus()
      } else if (!e.shiftKey && document.activeElement === last) {
        e.preventDefault()
        first.focus()
      }
    }

    window.addEventListener('keydown', onKeyDown)
    return () => {
      window.removeEventListener('keydown', onKeyDown)
      previouslyFocused.current?.focus()
    }
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [])
}
