import { useEffect, useMemo, useState } from 'react'
import type { Race } from '../../types/domain'
import { Pill } from '../../components/Pill'
import { EmptyState } from '../../components/EmptyState'
import { fmtPrice, fmtWpr } from '../../lib/format'
import { formatTimeOfDay } from '../../lib/countdown'
import { computePriceMove } from '../../lib/priceMove'
import { spellPosition } from '../../lib/spellPosition'
import { bushMeetingKeys, meetingKey, todayIso } from '../../lib/meetings'
import { computePlays, PLAY_KINDS, TRACK_ROWS, tally, type Play, type PlayKind } from '../../lib/plays'
import { HorseHero } from '../race/horseParts'

// The Plays tab (replaces "Standouts still to run" on the meetings page): every runner the dashboard flags for the day, in race order, in the
// same hero layout as the runner page, and kept after the race has run with how it went. A collapsed scoreboard below follows how each flag has done.
// Nothing here is a tip: out-of-sample no flag has shown a robust profit, the scoreboard is how that gets checked going forward.

type Period = 'day' | '7' | 'all'
type KindFilter = 'all' | PlayKind

const SEEN_KEY = 'toprate_plays_seen_v1'
const SEEN_KEEP_DAYS = 14

function shiftDate(iso: string, days: number): string {
  const d = new Date(`${iso}T00:00:00Z`)
  d.setUTCDate(d.getUTCDate() + days)
  return d.toISOString().slice(0, 10)
}

function ordinal(n: number): string {
  const v = n % 100
  if (v >= 11 && v <= 13) return `${n}th`
  return `${n}${({ 1: 'st', 2: 'nd', 3: 'rd' } as Record<number, string>)[n % 10] ?? 'th'}`
}

// Kinds each runner qualified for today, remembered on this device so a play that drops out before the jump stays listed (marked).
function readSeen(): Record<string, string[]> {
  try {
    const raw = window.localStorage.getItem(SEEN_KEY)
    const v = raw ? JSON.parse(raw) : {}
    return v && typeof v === 'object' ? v : {}
  } catch {
    return {}
  }
}

function writeSeen(v: Record<string, string[]>) {
  try {
    window.localStorage.setItem(SEEN_KEY, JSON.stringify(v))
  } catch {
    // Storage can be blocked; plays just will not be remembered across reloads.
  }
}

function seenMapFor(date: string): Map<string, PlayKind[]> {
  const m = new Map<string, PlayKind[]>()
  for (const entry of readSeen()[date] ?? []) {
    const [raceId, runId, kind] = entry.split('|')
    if (!raceId || !runId || !kind) continue
    const k = `${raceId}|${runId}`
    m.set(k, [...(m.get(k) ?? []), kind as PlayKind])
  }
  return m
}

function fmtRoi(v: number | null): string {
  return v == null ? '-' : `${v >= 0 ? '+' : ''}${(v * 100).toFixed(0)}%`
}

function pct(a: number, b: number): string {
  return b > 0 ? `${Math.round((a / b) * 100)}%` : '-'
}

const KIND_CHIP: Record<PlayKind, string> = {
  lead: 'border-line bg-indigo-bg text-indigo',
  map4: 'border-emerald-line bg-emerald-bg text-emerald-deep',
  value: 'border-amber-line bg-amber-bg text-amber',
}

function Chip({ kind, play, dropped, byBias }: { kind: PlayKind; play: Play; dropped?: boolean; byBias?: boolean }) {
  const meta = PLAY_KINDS.find((k) => k.kind === kind)!
  const detail =
    kind === 'lead' ? `${meta.short} +${play.lead.toFixed(1)}` : `${meta.short} (${play.sm != null ? (play.sm >= 0 ? '+' : '') + play.sm.toFixed(1) : '-'}), ${play.gap < 0.05 ? 'top' : `-${play.gap.toFixed(1)}`}`
  return (
    <span title={meta.help} className={`rounded-full border px-2 py-0.5 font-mono text-[11px] ${dropped ? 'border-line bg-bg text-ink-faint line-through' : KIND_CHIP[kind]}`}>
      {detail}
      {byBias && <span className="ml-1 font-sans font-semibold text-amber">{dropped ? 'lost to track bias' : 'from track bias'}</span>}
    </span>
  )
}

function ResultStrip({ play }: { play: Play }) {
  const { outcome, price, runner } = play
  const fin = runner.finishPosition
  if (outcome === 'pending') {
    return <span className="text-ink-mute">To run &middot; {formatTimeOfDay(play.race.startTime)}</span>
  }
  const ret = outcome === 'won' && price != null ? price - 1 : -1
  const label = outcome === 'won' ? 'Won' : outcome === 'placed' ? `Placed ${fin != null ? ordinal(fin) : ''}` : fin != null ? `${ordinal(fin)}` : 'Unplaced'
  const tone = outcome === 'won' ? 'text-emerald-deep' : outcome === 'placed' ? 'text-amber' : 'text-rose'
  return (
    <span>
      <span className={`font-semibold ${tone}`}>{label}</span>
      {price != null && (
        <span className="text-ink-mute">
          {' '}
          at {fmtPrice(price)} &middot; <span className={`font-mono ${ret >= 0 ? 'text-emerald-deep' : 'text-rose'}`}>{ret >= 0 ? '+' : '-'}${Math.abs(ret).toFixed(2)}</span> on $1 to win
        </span>
      )}
    </span>
  )
}

function PlayCard({ play, onOpen }: { play: Play; onOpen: () => void }) {
  const { race, runner, eff } = play
  const scratched = eff?.scratched ?? false
  const effectiveWpr = scratched ? null : (eff?.effectiveProjectedWpr ?? runner.projectedWpr)
  const atwOff = eff != null && Math.abs(eff.atwOff) >= 0.05 ? eff.atwOff : null
  const projAtw = effectiveWpr != null && atwOff != null ? effectiveWpr : null
  const spell = spellPosition(runner.formHistory, race.date)
  const fixedMove = computePriceMove(runner.openFixedPrice, runner.fixedWinPrice)
  const tone = play.outcome === 'won' ? 'bg-emerald-bg' : play.outcome === 'placed' ? 'bg-amber-bg' : 'bg-panel'
  return (
    <div className={`flex flex-col gap-1 rounded-md p-1 ${tone}`}>
      <button type="button" onClick={onOpen} className="flex w-full items-start gap-2.5 rounded-md px-1.5 py-0.5 text-left hover:bg-bg">
        {runner.silkUrl ? <img src={runner.silkUrl} alt="" className="h-8 w-8 shrink-0 rounded-sm object-contain" /> : <div className="h-8 w-8 shrink-0 rounded-sm bg-bg" />}
        <div className="min-w-0 flex-1">
          <div className={`truncate text-[15px] font-semibold text-ink ${scratched ? 'line-through' : ''}`}>
            {runner.tabNumber}. {runner.horse}
          </div>
          <div className="truncate text-xs text-ink-mute">
            {runner.jockey || 'Jockey TBA'} / {runner.trainer}
          </div>
        </div>
        <span className="mt-0.5 shrink-0 text-ink-faint">&rsaquo;</span>
      </button>
      <div className="flex flex-wrap items-center gap-1.5 px-1.5">
        {play.kinds.map((k) => (
          <Chip key={k} kind={k} play={play} byBias={play.biasGained.includes(k)} />
        ))}
        {play.droppedKinds.map((k) => (
          <Chip key={'d' + k} kind={k} play={play} dropped byBias={play.biasLost.includes(k)} />
        ))}
        {play.droppedKinds.length > 0 && play.kinds.length === 0 && play.outcome === 'pending' && <span className="text-[11px] text-ink-faint">no longer qualifies</span>}
      </div>
      <HorseHero
        runner={runner}
        race={race}
        proj={effectiveWpr}
        scratched={scratched}
        rank={play.rank}
        fieldSize={play.fieldSize}
        fieldTop={play.fieldTop}
        fieldLow={play.fieldLow}
        fair={eff?.effectivePrice ?? null}
        market={runner.fixedWinPrice}
        fixedMove={fixedMove}
        hasOverride={eff?.hasOverride ?? false}
        spellLabel={spell.label}
        daysSince={spell.daysSince}
        projAtw={projAtw}
        compact
      />
      <div className="flex flex-wrap items-center justify-between gap-x-4 gap-y-0.5 px-2 pb-1 text-xs">
        <ResultStrip play={play} />
        <span className="text-ink-faint">
          {play.rank === 1 ? `lead ${fmtWpr(play.lead)} WPR` : ''}
          {play.isFavourite ? `${play.rank === 1 ? ' · ' : ''}favourite` : ''}
          {runner.startingPrice != null && runner.fixedWinPrice != null && runner.startingPrice !== runner.fixedWinPrice ? ` · SP ${fmtPrice(runner.startingPrice)}` : ''}
        </span>
      </div>
    </div>
  )
}

function RaceGroup({ plays, onOpen }: { plays: Play[]; onOpen: (p: Play) => void }) {
  const race = plays[0].race
  return (
    <article className="overflow-hidden rounded-lg border-2 border-ink-faint/60 bg-panel shadow-md">
      <div className="flex flex-wrap items-baseline gap-x-2 border-b border-line bg-bg px-3 py-1.5">
        <span className="font-mono text-sm font-semibold text-ink">{formatTimeOfDay(race.startTime)}</span>
        <span className="text-sm font-medium text-ink">
          {race.venue} R{race.raceNumber}
        </span>
        <span className="text-xs text-ink-mute">
          {race.distance ? `${race.distance}m` : ''}
          {race.going ? ` · ${race.going}` : ''}
          {` · ${plays[0].fieldSize} runners`}
        </span>
        {plays.length > 1 && (
          <span
            title="Races with several plays: a play wins in about 42% of 2-play races and 57% of 3+ (28% with one), at longer prices. Not a profit once the biggest winners are removed."
            className={`ml-auto rounded-full border px-2 py-0.5 text-[11px] font-semibold ${plays.length >= 3 ? 'border-emerald bg-emerald text-white' : 'border-emerald-line bg-emerald-bg text-emerald-deep'}`}
          >
            {plays.length} plays
          </span>
        )}
      </div>
      <div className="flex flex-col divide-y divide-line">
        {plays.map((p) => (
          <PlayCard key={p.key} play={p} onOpen={() => onOpen(p)} />
        ))}
      </div>
    </article>
  )
}

export function PlaysTab({
  races,
  date,
  onDateChange,
  onOpen,
  priceBeta,
  deltas,
  bases,
  scratched,
  showBush,
  hiddenVenues,
}: {
  races: Race[]
  date: string
  onDateChange: (d: string) => void
  onOpen: (raceId: string, date: string, runId: string) => void
  priceBeta: number | null
  deltas: Record<string, number>
  bases: Record<string, number>
  scratched: Set<string>
  showBush: boolean
  hiddenVenues: Set<string>
}) {
  const [period, setPeriod] = useState<Period>('day')
  const [kindFilter, setKindFilter] = useState<KindFilter>('all')
  const [seenTick, setSeenTick] = useState(0)

  const visible = useMemo(() => {
    const bush = showBush ? null : bushMeetingKeys(races)
    return races.filter((r) => !hiddenVenues.has(r.venue) && !(bush && bush.has(meetingKey(r))))
  }, [races, showBush, hiddenVenues])

  const dayRaces = useMemo(() => visible.filter((r) => r.date === date), [visible, date])
  const seen = useMemo(() => seenMapFor(date), [date, seenTick]) // eslint-disable-line react-hooks/exhaustive-deps
  const ctx = useMemo(() => ({ deltas, bases, scratched, priceBeta }), [deltas, bases, scratched, priceBeta])
  const dayPlays = useMemo(() => computePlays(dayRaces, ctx, seen), [dayRaces, ctx, seen])

  // Remember what qualified before the jump (a race that has run keeps its logged projection, so nothing new is learned from it).
  useEffect(() => {
    const fresh = dayPlays.filter((p) => p.outcome === 'pending').flatMap((p) => p.kinds.map((k) => `${p.race.raceId}|${p.runner.runId}|${k}`))
    if (fresh.length === 0) return
    const all = readSeen()
    const have = new Set(all[date] ?? [])
    const add = fresh.filter((k) => !have.has(k))
    if (add.length === 0) return
    all[date] = [...have, ...add]
    const cutoff = shiftDate(todayIso(), -SEEN_KEEP_DAYS)
    for (const d of Object.keys(all)) if (d < cutoff) delete all[d]
    writeSeen(all)
    setSeenTick((t) => t + 1)
  }, [dayPlays, date])

  const periodPlays = useMemo(() => {
    if (period === 'day') return dayPlays
    const from = period === '7' ? shiftDate(date, -6) : '0000-00-00'
    const rs = visible.filter((r) => r.date >= from && r.date <= date)
    return computePlays(rs, ctx)
  }, [period, dayPlays, visible, date, ctx])

  const listed = useMemo(
    () => dayPlays.filter((p) => kindFilter === 'all' || p.kinds.includes(kindFilter) || p.droppedKinds.includes(kindFilter)),
    [dayPlays, kindFilter],
  )

  const groups = useMemo(() => {
    const m = new Map<string, Play[]>()
    for (const p of listed) m.set(p.race.raceId, [...(m.get(p.race.raceId) ?? []), p])
    // Within a race, best projected rating first.
    return [...m.values()].map((g) => g.sort((a, b) => a.rank - b.rank))
  }, [listed])

  const dayTally = tally(dayPlays)

  return (
    <div className="flex flex-col gap-4">
      <div className="flex flex-wrap items-center gap-2">
        <button type="button" aria-label="Previous day" onClick={() => onDateChange(shiftDate(date, -1))} className="rounded-md border border-line bg-panel px-2 py-1 text-sm text-ink-mute hover:text-ink">
          &lsaquo;
        </button>
        <input type="date" value={date} onChange={(e) => e.target.value && onDateChange(e.target.value)} className="rounded-md border border-line bg-panel px-2 py-1 text-sm font-mono" />
        <button type="button" aria-label="Next day" onClick={() => onDateChange(shiftDate(date, 1))} className="rounded-md border border-line bg-panel px-2 py-1 text-sm text-ink-mute hover:text-ink">
          &rsaquo;
        </button>
        {date !== todayIso() && (
          <Pill active={false} onClick={() => onDateChange(todayIso())}>
            Today
          </Pill>
        )}
        {dayTally.run > 0 && (
          <span className="ml-auto text-xs text-ink-mute">
            {dayTally.wins} won, {dayTally.places} placed of {dayTally.run} run
          </span>
        )}
      </div>

      <div className="flex flex-wrap items-center gap-1.5">
        <Pill active={kindFilter === 'all'} onClick={() => setKindFilter('all')}>
          All ({dayPlays.length})
        </Pill>
        {PLAY_KINDS.map((k) => (
          <Pill key={k.kind} active={kindFilter === k.kind} onClick={() => setKindFilter(k.kind)}>
            {k.label} ({dayPlays.filter((p) => p.kinds.includes(k.kind)).length})
          </Pill>
        ))}
      </div>

      {listed.length === 0 ? (
        <EmptyState message={dayPlays.length === 0 ? 'No plays for this day yet. They appear once projections are in.' : 'No plays match this filter.'} progress={null} />
      ) : (
        <div className="flex flex-col gap-3">
          {groups.map((g) => (
            <RaceGroup key={g[0].race.raceId} plays={g} onOpen={(p) => onOpen(p.race.raceId, p.race.date, p.runner.runId)} />
          ))}
        </div>
      )}

      <details className="rounded-lg border border-line bg-panel p-3">
        <summary className="cursor-pointer text-sm font-semibold text-ink">Scoreboard: how each flag has done</summary>
        <div className="mt-2 flex flex-wrap items-center justify-end gap-2">
          <div className="flex gap-1.5">
            <Pill active={period === 'day'} onClick={() => setPeriod('day')}>
              This day
            </Pill>
            <Pill active={period === '7'} onClick={() => setPeriod('7')}>
              7 days
            </Pill>
            <Pill active={period === 'all'} onClick={() => setPeriod('all')}>
              All loaded
            </Pill>
          </div>
        </div>
        <div className="mt-2 overflow-x-auto">
          <table className="w-full text-xs">
            <thead className="text-left text-ink-mute">
              <tr>
                <th className="py-1 pr-2 font-medium">Flag</th>
                <th className="px-1 text-right font-medium">Run</th>
                <th className="px-1 text-right font-medium">Won</th>
                <th className="px-1 text-right font-medium">Strike</th>
                <th className="pl-1 text-right font-medium">$1 win</th>
              </tr>
            </thead>
            <tbody>
              {TRACK_ROWS.map((row) => {
                const t = tally(periodPlays.filter(row.test))
                return (
                  <tr key={row.id} className="border-t border-line-soft">
                    <td className="py-1 pr-2 text-ink" title={row.label}><span className="sm:hidden">{row.short}</span><span className="hidden sm:inline">{row.label}</span></td>
                    <td className="px-1 text-right font-mono">{t.run}</td>
                    <td className="px-1 text-right font-mono">{t.wins}</td>
                    <td className="px-1 text-right font-mono">{pct(t.wins, t.run)}</td>
                    <td className={`pl-1 text-right font-mono ${t.roi == null ? '' : t.roi >= 0 ? 'text-emerald-deep' : 'text-rose'}`}>{fmtRoi(t.roi)}</td>
                  </tr>
                )
              })}
            </tbody>
          </table>
        </div>
      </details>
    </div>
  )
}
