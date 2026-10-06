import { useEffect, useState } from 'react'
import type { Race } from '../../types/domain'
import { estimatePace } from '../../lib/pace'
import { formatCountdown, formatTimeOfDay } from '../../lib/countdown'
import { Pill } from '../../components/Pill'
import { raceStatus, STATUS_PILL_TONE } from '../../lib/raceStatus'
import { fmtPrize, goingChange, goingTone } from './raceFacts'

interface RaceHeaderProps {
  race: Race
  meeting: Race[]
  scratchedInRace: number
  hasAnyResult: boolean
  activeRunners: Race['runners']
}

type Tone = 'good' | 'warn' | 'bad' | 'plain'
const TILE_TONE: Record<Tone, string> = {
  good: 'border-emerald-line bg-emerald-bg text-emerald-deep',
  warn: 'border-amber-line bg-amber-bg text-amber',
  bad: 'border-rose-line bg-rose-bg text-rose',
  plain: 'border-line bg-bg text-ink',
}

function Tile({ label, value, sub, tone, title }: { label: string; value: string; sub?: string | null; tone: Tone; title?: string }) {
  return (
    <div title={title} className={`min-w-0 rounded-lg border px-3 py-2 ${TILE_TONE[tone]}`}>
      <div className="text-[10px] font-semibold uppercase tracking-wide opacity-70">{label}</div>
      <div className="truncate text-base font-semibold leading-tight">{value}</div>
      {sub && <div className="truncate text-xs opacity-80">{sub}</div>}
    </div>
  )
}

function Chip({ children, className = '' }: { children: React.ReactNode; className?: string }) {
  return <span className={`inline-flex items-center rounded-full border px-2.5 py-0.5 text-xs font-medium ${className || 'border-line bg-bg text-ink-soft'}`}>{children}</span>
}

function useConditions(race: Race, meeting: Race[], activeRunners: Race['runners']) {
  const change = goingChange(race, meeting)
  const pace = estimatePace(race, activeRunners)
  const leaders = activeRunners.filter((r) => r.predictedRelSettle != null && r.predictedRelSettle < 0.2).length
  const rail = race.rail && race.rail !== 'nan' ? race.rail : null
  const paceTone: Tone = pace.tempoBucket === 'Fast' ? 'warn' : pace.tempoBucket === 'Slow' ? 'plain' : 'good'
  const gt = goingTone(race.going)
  const goingTileTone: Tone = gt === 'dry' ? 'good' : gt === 'soft' ? 'warn' : gt === 'heavy' ? 'bad' : 'plain'
  return { change, pace, leaders, rail, paceTone, goingTileTone }
}

// The race and its conditions in one banner. The things that change the result (track, pace, rail) get tiles coloured by what they mean,
// the rest stay as chips.
export function RaceHeader({ race, meeting, scratchedInRace, hasAnyResult, activeRunners }: RaceHeaderProps) {
  const { change, pace, leaders, rail, paceTone, goingTileTone } = useConditions(race, meeting, activeRunners)
  const prize = fmtPrize(race.prizeMoney)
  const time = formatTimeOfDay(race.startTime)
  return (
    <section className="rounded-lg border border-line bg-panel p-4 shadow-[var(--shadow-1)]">
      <div className="flex flex-wrap items-start justify-between gap-x-4 gap-y-2">
        <div className="min-w-0">
          <div className="text-xs font-semibold uppercase tracking-wide text-ink-faint">
            {race.venue} &middot; {race.state} &middot; Race {race.raceNumber} &middot; {race.distance}m
            {prize ? ` · ${prize}` : ''}
          </div>
          <h2 className="mt-0.5 text-xl font-semibold leading-tight text-ink sm:text-2xl">{race.raceName}</h2>
        </div>
        <div className="flex-none text-right">
          {race.allResulted && !race.provisional ? (
            <span className="rounded-full border border-emerald-line bg-emerald-bg px-2.5 py-1 font-mono text-xs font-semibold text-emerald-deep">Resulted</span>
          ) : hasAnyResult ? (
            <span
              className="rounded-full border border-amber-line bg-amber-bg px-2.5 py-1 font-mono text-xs font-semibold text-amber"
              title="TAB's fast provisional feed - toprate.au's confirmed result lands once the whole meeting finishes"
            >
              Interim result
            </span>
          ) : (
            <div>
              <div className="font-mono text-2xl font-semibold leading-none text-emerald-deep">{formatCountdown(race.startTime) || '-'}</div>
              <div className="mt-1 text-[11px] uppercase tracking-wide text-ink-faint">to jump{time ? ` · ${time}` : ''}</div>
            </div>
          )}
        </div>
      </div>

      <div className="mt-3 grid grid-cols-2 gap-2 sm:grid-cols-3">
        {race.going && (
          <Tile
            label="Track"
            value={race.going}
            sub={change ? `was ${change.from} at R${change.race}` : null}
            tone={change ? 'bad' : goingTileTone}
            title="Going the projections for this race are made on"
          />
        )}
        <Tile
          label="Pace"
          value={pace.display.replace(' (predicted)', '')}
          sub={pace.fromShape ? 'measured' : leaders > 0 ? `${leaders} likely leader${leaders === 1 ? '' : 's'}` : 'predicted'}
          tone={paceTone}
          title={pace.fromShape ? 'Measured early pace' : 'Predicted early pace'}
        />
        {rail && <Tile label="Rail" value={rail.replace(/\.\s*$/, '')} tone="plain" title="Rail position" />}
      </div>

      <div className="mt-3 flex flex-wrap gap-1.5">
        <Chip>
          {race.runners.length} runners
          {scratchedInRace > 0 && <span className="text-rose">&nbsp;({scratchedInRace} scratched)</span>}
        </Chip>
        {race.hasFirstStarter && <Chip className="border-amber-line bg-amber-bg text-amber">First starter in field</Chip>}
      </div>
    </section>
  )
}

// A one-line version that sticks under the app header once the banner has scrolled away, so the countdown, conditions and race switcher
// stay in view over a long field.
export function RaceMiniBar({
  race,
  meeting,
  activeRunners,
  anchorRef,
  onSelectRace,
}: {
  race: Race
  meeting: Race[]
  activeRunners: Race['runners']
  anchorRef: React.RefObject<HTMLElement | null>
  onSelectRace: (raceId: string, date: string) => void
}) {
  const [visible, setVisible] = useState(false)
  const [top, setTop] = useState(0)
  useEffect(() => {
    const el = anchorRef.current
    if (!el) return
    const hdr = document.querySelector('header.sticky') as HTMLElement | null
    const h = () => hdr?.getBoundingClientRect().height ?? 0
    setTop(h())
    const io = new IntersectionObserver(([e]) => setVisible(!e.isIntersecting && e.boundingClientRect.top < h()), { rootMargin: `-${Math.round(h())}px 0px 0px 0px` })
    io.observe(el)
    const onResize = () => setTop(h())
    window.addEventListener('resize', onResize)
    return () => {
      io.disconnect()
      window.removeEventListener('resize', onResize)
    }
  }, [anchorRef])
  const { change, pace, paceTone } = useConditions(race, meeting, activeRunners)
  if (!visible) return null
  const goingClass = change ? TILE_TONE.bad : TILE_TONE[goingToneKey(race.going)]
  return (
    <div style={{ top }} className="sticky z-20 -mx-1 flex flex-wrap items-center gap-x-2 gap-y-1 rounded-lg border border-line bg-panel/95 px-3 py-1.5 shadow-[var(--shadow-1)] backdrop-blur">
      <span className="text-sm font-semibold text-ink">
        {race.venue} R{race.raceNumber}
      </span>
      {race.going && <span className={`rounded-full border px-2 py-0.5 text-xs font-medium ${goingClass}`}>{race.going}</span>}
      <span className={`rounded-full border px-2 py-0.5 text-xs font-medium ${TILE_TONE[paceTone]}`}>{pace.display.replace(' (predicted)', '')}</span>
      <span className="font-mono text-sm font-semibold text-emerald-deep">{formatCountdown(race.startTime) || ''}</span>
      <span className="flex-1" />
      <span className="hidden flex-wrap gap-1 sm:flex">
        {meeting.map((r) => (
          <Pill key={r.raceId} active={r.raceId === race.raceId} tone={STATUS_PILL_TONE[raceStatus(r, Date.now())]} onClick={() => onSelectRace(r.raceId, r.date)}>
            R{r.raceNumber}
          </Pill>
        ))}
      </span>
    </div>
  )
}

function goingToneKey(going: string | null | undefined): Tone {
  const t = goingTone(going)
  return t === 'dry' ? 'good' : t === 'soft' ? 'warn' : t === 'heavy' ? 'bad' : 'plain'
}
