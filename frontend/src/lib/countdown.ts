export function formatTimeOfDay(startTime: string): string {
  const d = new Date(startTime)
  if (Number.isNaN(d.getTime())) return ''
  return d.toLocaleTimeString('en-AU', { hour: '2-digit', minute: '2-digit', hour12: false })
}

// Seconds-precision countdown for the next-to-jump ticker, which ticks every
// second (formatCountdown below is minute-precision, for the race header).
export function formatSecondsCountdown(secs: number): string {
  if (secs <= 0) return 'LIVE'
  if (secs < 60) return `${secs}s`
  const m = Math.floor(secs / 60)
  const s = secs % 60
  if (m < 60) return `${m}m ${s < 10 ? '0' : ''}${s}s`
  const h = Math.floor(m / 60)
  const mm = m % 60
  return `${h}h ${mm < 10 ? '0' : ''}${mm}m`
}

export function formatCountdown(startTime: string, now = new Date()): string {
  const start = new Date(startTime)
  const diffMs = start.getTime() - now.getTime()
  if (Number.isNaN(diffMs)) return ''
  if (diffMs <= 0) return 'Jumped'
  const totalMinutes = Math.round(diffMs / 60_000)
  const hours = Math.floor(totalMinutes / 60)
  const minutes = totalMinutes % 60
  if (hours > 0) return `${hours}h ${minutes}m`
  return `${minutes}m`
}
