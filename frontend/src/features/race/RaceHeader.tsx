import { useEffect, useState } from 'react'
import { useNow } from '../../hooks/useNow'
import type { Race } from '../../types/domain'
import { estimatePace } from '../../lib/pace'
import { formatCountdown, formatTimeOfDay } from '../../lib/countdown'
import { Pill } from '../../components/Pill'
import { raceStatus, STATUS_PILL_TONE } from '../../lib/raceStatus'
import { fmtPrize, goingChange, goingTone } from './raceFacts'
import { ReplayPanel } from './ReplayPanel'

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

// On the dark banner (every width) every chip shares one translucent style and the meaning (good / warn / bad) moves into a small dot,
// so the colours no longer fight the green.
const DARK_CHIP = 'border-white/20 bg-white/10 text-white'
const DOT: Record<Tone, string> = { good: 'bg-[#34d399]', warn: 'bg-[#fbbf24]', bad: 'bg-[#fb7185]', plain: '' }

function Chip({ children, title, tone }: { children: React.ReactNode; className?: string; title?: string; tone?: Tone }) {
  return (
    <span title={title} className={`inline-flex min-w-0 items-center rounded-full border px-2.5 py-0.5 text-xs font-medium ${DARK_CHIP}`}>
      {tone && DOT[tone] && <span className={`mr-1.5 inline-block h-1.5 w-1.5 flex-none rounded-full ${DOT[tone]}`} aria-hidden="true" />}
      {children}
    </span>
  )
}

// The distance is the first thing to read about a race, so it is a brighter, bolder chip than the others (same size), in the banner and in the sticky bar.
function DistanceChip({ metres }: { metres: number }) {
  return (
    <span title="Race distance" className="inline-flex flex-none items-center rounded-full border border-white/30 bg-white/20 px-2.5 py-0.5 text-xs font-bold text-white">
      {metres}m
    </span>
  )
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
    <section className="rounded-2xl border border-transparent bg-[#0B3B2A] px-3 py-2.5 shadow-[var(--shadow-1)] sm:px-4 md:px-7 md:py-5">
      <div className="flex items-start justify-between gap-x-3">
        <div className="min-w-0">
          <div className="truncate text-[11px] font-semibold uppercase tracking-wide text-[#A9CDBB]">
            {race.venue} &middot; {race.state} &middot; R{race.raceNumber}
            {prize ? ` · ${prize}` : ''}
          </div>
          <h2 className="text-lg font-semibold leading-tight text-white sm:text-xl md:text-3xl md:tracking-tight">{race.raceName}</h2>
        </div>
        <div className="flex-none text-right">
          {race.allResulted && !race.provisional ? (
            <span className="inline-flex items-center rounded-full border border-white/20 bg-white/10 px-2.5 py-1 font-mono text-xs font-semibold text-white"><span className="mr-1.5 inline-block h-1.5 w-1.5 rounded-full bg-[#34d399]" aria-hidden="true" />Resulted</span>
          ) : hasAnyResult ? (
            <span
              className="inline-flex items-center rounded-full border border-white/20 bg-white/10 px-2.5 py-1 font-mono text-xs font-semibold text-white"
              title="Provisional result from TAB's fast feed; the racing.com result and our rating follow overnight"
            >
              <span className="mr-1.5 inline-block h-1.5 w-1.5 rounded-full bg-[#fbbf24]" aria-hidden="true" />
              Interim result
            </span>
          ) : (
            <div>
              <div className="font-mono text-xl font-semibold leading-none text-white md:text-4xl">{formatCountdown(race.startTime) || '-'}</div>
              <div className="mt-0.5 text-[10px] uppercase tracking-wide text-[#A9CDBB] md:text-xs">to jump{time ? ` · ${time}` : ''}</div>
            </div>
          )}
        </div>
      </div>

      <div className="mt-2 flex flex-wrap items-center gap-1.5 md:mt-3">
        <DistanceChip metres={race.distance} />
        {race.going && (
          <Chip tone={change ? 'bad' : goingTileTone} className={TILE_TONE[change ? 'bad' : goingTileTone]} title={change ? `Going the projections are made on (was ${change.from} at R${change.race})` : 'Going the projections for this race are made on'}>
            <b className="mr-1 text-[10px] uppercase opacity-70">Track</b>
            {race.going}
            {change && <span className="ml-1 font-normal opacity-80">(was {change.from})</span>}
          </Chip>
        )}
        <Chip tone={paceTone} className={TILE_TONE[paceTone]} title={pace.fromShape ? 'Measured early pace' : `Predicted early pace${leaders > 0 ? `, ${leaders} likely leader${leaders === 1 ? '' : 's'}` : ''}`}>
          <b className="mr-1 text-[10px] uppercase opacity-70">Pace</b>
          {pace.display.replace(' (predicted)', '')}
        </Chip>
        {rail && (
          <Chip className={`max-w-full ${TILE_TONE.plain}`} title={rail}>
            <b className="mr-1 flex-none text-[10px] uppercase opacity-70">Rail</b>
            <span className="truncate">{rail.replace(/\.\s*$/, '')}</span>
          </Chip>
        )}
        <Chip>
          {race.runners.length} runners
          {scratchedInRace > 0 && <span className="text-[#fda4af]">&nbsp;({scratchedInRace} scr)</span>}
        </Chip>
        {race.hasFirstStarter && <Chip tone="warn" className="border-amber-line bg-amber-bg text-amber">First starter</Chip>}
      </div>
      <div className="xl:hidden"><ReplayPanel venue={race.venue} date={race.date} raceNumber={race.raceNumber} hasResult={hasAnyResult || race.allResulted} /></div>
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
  const now = useNow(30_000)
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
  const goingT: Tone = change ? 'bad' : goingToneKey(race.going)
  return (
    <div style={{ top }} className="sticky z-20 -mx-1 flex flex-wrap items-center gap-x-2 gap-y-1 rounded-lg border border-transparent bg-[#0B3B2A]/95 px-3 py-1.5 text-white shadow-[var(--shadow-1)] backdrop-blur">
      <span className="text-sm font-semibold text-white">
        {race.venue} R{race.raceNumber}
      </span>
      <DistanceChip metres={race.distance} />
      {race.going && <Chip tone={goingT}>{race.going}</Chip>}
      <Chip tone={paceTone}>{pace.display.replace(' (predicted)', '')}</Chip>
      <span className="font-mono text-sm font-semibold text-white">{formatCountdown(race.startTime) || ''}</span>
      <span className="flex-1" />
      <span className="hidden flex-wrap gap-1 sm:flex">
        {meeting.map((r) => (
          <Pill key={r.raceId} active={r.raceId === race.raceId} tone={STATUS_PILL_TONE[raceStatus(r, now)]} onClick={() => onSelectRace(r.raceId, r.date)}>
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
