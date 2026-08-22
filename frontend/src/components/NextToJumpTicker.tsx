import { useEffect, useState } from 'react'
import type { Race } from '../types/domain'
import { formatSecondsCountdown } from '../lib/countdown'
import { useTickerCollapsed } from '../lib/ticker'

interface NextToJumpTickerProps {
  races: Race[]
  onSelectRace: (raceId: string, date: string) => void
}

interface UpcomingRace {
  race: Race
  secsUntil: number
}

const WINDOW_PAST_SECS = -180 // still show a race up to 3 min after jump
const WINDOW_FUTURE_SECS = 86_400 // look ahead 24h
const MAX_PILLS = 6

function countdownTone(secsUntil: number): string {
  if (secsUntil <= 0) return 'bg-amber text-ink font-semibold'
  if (secsUntil <= 120) return 'bg-rose text-white font-semibold'
  if (secsUntil <= 600) return 'bg-amber/80 text-ink font-semibold'
  return 'bg-white/15 text-white/85'
}

// Sticky "next to jump" strip - the races closest to starting, from
// anywhere in the app, one tap away. Ported from the old dashboard's
// renderNtjTicker (toprate_html_v3.py L10314-10363); the reviewed-race
// filter it applied doesn't exist in this rebuild yet (that's the Phase 2
// race-review workflow), so for now every upcoming race is eligible.
export function NextToJumpTicker({ races, onSelectRace }: NextToJumpTickerProps) {
  const { collapsed, setCollapsed } = useTickerCollapsed()
  const [now, setNow] = useState(() => Date.now())

  useEffect(() => {
    const id = setInterval(() => setNow(Date.now()), 1000)
    return () => clearInterval(id)
  }, [])

  const upcoming: UpcomingRace[] = races
    .filter((r) => !r.allResulted && r.startTime)
    .map((r) => ({ race: r, secsUntil: Math.round((new Date(r.startTime).getTime() - now) / 1000) }))
    .filter((u) => u.secsUntil >= WINDOW_PAST_SECS && u.secsUntil <= WINDOW_FUTURE_SECS)
    .sort((a, b) => a.secsUntil - b.secsUntil)
    .slice(0, MAX_PILLS)

  return (
    <div
      className={`flex items-center gap-3 rounded-md bg-ink text-white ${collapsed ? 'px-3 py-1.5' : 'px-3 py-2'}`}
    >
      <button
        type="button"
        onClick={() => setCollapsed(!collapsed)}
        aria-label="Toggle next-to-jump ticker"
        className="flex h-6 w-6 shrink-0 items-center justify-center rounded border border-white/20 text-[9px] text-white/70 transition-colors hover:bg-white/10 hover:text-white"
      >
        {collapsed ? '▶' : '▼'}
      </button>
      <div className="hidden shrink-0 whitespace-nowrap text-[10px] font-semibold uppercase tracking-wide text-white/60 sm:block">
        Next to jump
      </div>
      {!collapsed &&
        (upcoming.length === 0 ? (
          <div className="font-mono text-xs italic text-white/40">Nothing jumping soon.</div>
        ) : (
          <div className="flex flex-1 gap-2 overflow-x-auto">
            {upcoming.map(({ race, secsUntil }) => (
              <button
                key={race.raceId}
                type="button"
                onClick={() => onSelectRace(race.raceId, race.date)}
                className="flex shrink-0 items-center gap-2 rounded-md border border-white/10 bg-white/5 px-3 py-1.5 text-xs transition-colors hover:border-white/25 hover:bg-white/10"
              >
                <span className="whitespace-nowrap font-medium text-white">
                  {race.venue} R{race.raceNumber}
                </span>
                <span className={`whitespace-nowrap rounded px-1.5 py-0.5 font-mono text-[10px] ${countdownTone(secsUntil)}`}>
                  {formatSecondsCountdown(secsUntil)}
                </span>
              </button>
            ))}
          </div>
        ))}
    </div>
  )
}
