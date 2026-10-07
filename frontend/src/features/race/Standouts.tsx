import { useMemo, useState } from 'react'
import type { Race } from '../../types/domain'
import { Pill } from '../../components/Pill'
import { projectedAtActualScale } from '../../lib/atw'
import { formatTimeOfDay } from '../../lib/countdown'
import { raceStatus } from '../../lib/raceStatus'
import { speedMapDemeanedByRunId, SPEED_MAP_TINT_THRESHOLD } from '../../lib/raceModel'

type Runner = Race['runners'][number]
type Mode = 'leader' | 'map'
type Band = 2 | 4 | 6

const BANDS: Band[] = [2, 4, 6]
const MAP_LIST_LIMIT = 8
const LEADER_LIST_LIMIT = 5

// Map value a runner needs to be listed. 1.0 rather than the tint threshold (0.5): tested 8 Oct 2026, +0.5 lifted the win rate by 1 to 2 points
// (intervals mostly spanning zero), +1.0 by 6 to 8 points with both halves of the window agreeing, at about 3 to 6 runners a day.
const MAP_MIN = 1.0

// Logged projections, 1 Jul to 5 Oct 2026 (2,863 races of 5+ runners, rated on the same scale as this list): win rate of runners inside the band
// with a map of +1.0 or better vs every runner inside it. The ROI of this group was positive but did not survive removing its 3 biggest winners
// in 2 of 3 bands, so no price edge is claimed.
const MAP_HISTORY: Record<Band, { withMap: number; all: number }> = {
  2: { withMap: 29.6, all: 22.6 },
  4: { withMap: 26.7, all: 18.5 },
  6: { withMap: 24.0, all: 15.8 },
}

interface Entry {
  race: Race
  runner: Runner
  gap: number
  sm: number | null
  // The field's second-best rating gap, used by the leader list.
  lead: number
}

function mapTone(sm: number | null): { label: string; cls: string } | null {
  if (sm == null) return null
  if (sm >= SPEED_MAP_TINT_THRESHOLD) return { label: 'Map +' + sm.toFixed(1), cls: 'border-emerald-line bg-emerald-bg text-emerald-deep' }
  if (sm <= -SPEED_MAP_TINT_THRESHOLD) return { label: 'Map ' + sm.toFixed(1), cls: 'border-rose-line bg-rose-bg text-rose' }
  return { label: 'Map neutral', cls: 'border-line bg-bg text-ink-faint' }
}

function MapChip({ sm }: { sm: number | null }) {
  const t = mapTone(sm)
  if (!t) return null
  return <span className={`flex-none rounded-full border px-1.5 py-px font-mono text-[10px] ${t.cls}`}>{t.label}</span>
}

// Upcoming races on the grid's day, read two ways: where the top projection leads by the most, and which runners inside 2, 4 or 6 WPR of the top
// also have a positive speed map (the suitability adjustment, demeaned against its own race). Separation and a filter only, never a tip.
export function Standouts({ races, now, onSelectRace }: { races: Race[]; now: number; onSelectRace: (raceId: string, date: string) => void }) {
  const [mode, setMode] = useState<Mode>('leader')
  const [band, setBand] = useState<Band>(4)
  const [showAll, setShowAll] = useState(false)

  const perRace = useMemo(() => {
    const out: { race: Race; ranked: { runner: Runner; score: number; sm: number | null }[] }[] = []
    for (const race of races) {
      const st = raceStatus(race, now)
      if (st === 'resulted' || st === 'interim') continue
      const live = race.runners.filter((r) => !r.dataScratched)
      const sm = speedMapDemeanedByRunId(live)
      const ranked = live
        .filter((r) => r.projectedWpr != null)
        .map((r) => ({ runner: r, score: projectedAtActualScale(r) as number, sm: sm.get(r.runId) ?? null }))
        .sort((a, b) => b.score - a.score)
      if (ranked.length < 5) continue
      out.push({ race, ranked })
    }
    return out
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [races])

  const leaders = useMemo<Entry[]>(
    () =>
      perRace
        .map(({ race, ranked }) => ({ race, runner: ranked[0].runner, gap: 0, sm: ranked[0].sm, lead: ranked[0].score - ranked[1].score }))
        .sort((a, b) => b.lead - a.lead)
        .slice(0, LEADER_LIST_LIMIT),
    [perRace],
  )

  const mapEntries = useMemo<Entry[]>(() => {
    const out: Entry[] = []
    for (const { race, ranked } of perRace) {
      const top = ranked[0].score
      for (const x of ranked) {
        if (top - x.score > band) break
        if (x.sm != null && x.sm >= MAP_MIN) out.push({ race, runner: x.runner, gap: top - x.score, sm: x.sm, lead: 0 })
      }
    }
    // Jumping order, so the next chance is at the top.
    return out.sort((a, b) => (a.race.startTime ?? '').localeCompare(b.race.startTime ?? '') || a.gap - b.gap)
  }, [perRace, band])

  const shownMap = showAll ? mapEntries : mapEntries.slice(0, MAP_LIST_LIMIT)
  const racesWithMap = new Set(mapEntries.map((e) => e.race.raceId)).size
  if (perRace.length === 0) return null

  const row = (e: Entry, right: React.ReactNode) => (
    <li key={`${e.race.raceId}-${e.runner.runId}`}>
      <button type="button" onClick={() => onSelectRace(e.race.raceId, e.race.date)} className="flex w-full items-center justify-between gap-2 py-1.5 text-left hover:text-emerald-deep">
        <span className="min-w-0">
          <span className="block font-mono text-[11px] text-ink-mute">{e.race.venue} R{e.race.raceNumber} {formatTimeOfDay(e.race.startTime)}</span>
          <span className="block truncate text-sm">{e.runner.tabNumber}. {e.runner.horse}</span>
        </span>
        <span className="flex flex-none items-center gap-1.5">{right}</span>
      </button>
    </li>
  )

  return (
    <div className="rounded-lg border border-line bg-panel p-3">
      <div className="flex flex-wrap items-center justify-between gap-2">
        <div className="text-xs font-semibold uppercase tracking-wide text-ink-faint">Standouts still to run</div>
        <div className="flex gap-1.5">
          <Pill active={mode === 'leader'} onClick={() => setMode('leader')}>Clear leader</Pill>
          <Pill active={mode === 'map'} onClick={() => setMode('map')}>Positive map</Pill>
        </div>
      </div>

      {mode === 'leader' ? (
        <>
          <p className="mb-1 mt-1 text-[11px] text-ink-faint">Top projection leads the second by the most WPR. Separation only, not a tip.</p>
          <ul className="flex flex-col divide-y divide-line-soft">
            {leaders.map((e) => row(e, <><MapChip sm={e.sm} /><span className="font-mono text-xs text-ink-soft">+{e.lead.toFixed(1)}</span></>))}
          </ul>
        </>
      ) : (
        <>
          <div className="mb-1 mt-2 flex flex-wrap items-center gap-1.5">
            <span className="text-[11px] text-ink-faint">Within</span>
            {BANDS.map((b) => (
              <Pill key={b} active={band === b} onClick={() => { setBand(b); setShowAll(false) }}>{b} WPR</Pill>
            ))}
            <span className="text-[11px] text-ink-faint">of the top rated</span>
          </div>
          <p className="mb-1 text-[11px] text-ink-faint">
            Runners with a positive speed map (+{MAP_MIN.toFixed(1)} or better against their own field), in jumping order. {mapEntries.length} runners in {racesWithMap} races.
          </p>
          {mapEntries.length === 0 ? (
            <p className="py-2 text-sm text-ink-mute">None inside {band} WPR with a map of +{MAP_MIN.toFixed(1)} or better.</p>
          ) : (
            <ul className="flex flex-col divide-y divide-line-soft">
              {shownMap.map((e) =>
                row(e, <><MapChip sm={e.sm} /><span className="w-14 text-right font-mono text-xs text-ink-soft">{e.gap < 0.05 ? 'top' : `-${e.gap.toFixed(1)}`}</span></>),
              )}
            </ul>
          )}
          {mapEntries.length > MAP_LIST_LIMIT && (
            <button type="button" onClick={() => setShowAll((v) => !v)} className="mt-1 text-xs font-medium text-emerald-deep underline">
              {showAll ? 'Show fewer' : `Show all ${mapEntries.length}`}
            </button>
          )}
          <p className="mt-2 text-[11px] text-ink-faint">
            Past results (1 Jul to 5 Oct): inside {band} WPR, runners with a map of +{MAP_MIN.toFixed(1)} or better won {MAP_HISTORY[band].withMap}% against {MAP_HISTORY[band].all}% for everyone inside. A real lift in who wins, but a price edge is not proven. A filter, not a tip.
          </p>
        </>
      )}
    </div>
  )
}
