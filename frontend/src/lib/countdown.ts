export function formatTimeOfDay(startTime: string): string {
  const d = new Date(startTime)
  if (Number.isNaN(d.getTime())) return ''
  return d.toLocaleTimeString('en-AU', { hour: '2-digit', minute: '2-digit', hour12: false })
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
