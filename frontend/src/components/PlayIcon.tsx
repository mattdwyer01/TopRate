// A plain SVG play triangle. The text character (U+25B6) is drawn as a colour emoji on iOS, which looked wrong next to the
// rest of the UI, so replay controls use this instead.
export function PlayIcon({ className = 'h-3 w-3' }: { className?: string }) {
  return (
    <svg viewBox="0 0 10 10" aria-hidden="true" className={className} fill="currentColor">
      <path d="M2 1.2v7.6a.5.5 0 0 0 .76.43l6.2-3.8a.5.5 0 0 0 0-.86l-6.2-3.8A.5.5 0 0 0 2 1.2Z" />
    </svg>
  )
}
