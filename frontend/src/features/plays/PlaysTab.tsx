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
import { fmtBias, hasRunnerBias } from '../../lib/bias'

// The Plays tab (replaces "Standouts still to run" on the meetings page): every runner the dashboard flags for the day, in race order, in the
// same hero layout as the runner page, and kept after the race has run with how it went. A scoreboard above follows how each flag has done.
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
  const tone =
    play.outcome === 'won' ? 'border-emerald bg-emerald-bg/40' : play.outcome === 'placed' ? 'border-amber-line bg-amber-bg/40' : play.outcome === 'unplaced' ? 'border-line bg-bg' : 'border-line bg-bg'
  return (
    <article className={`flex flex-col gap-1.5 rounded-lg border p-1.5 ${tone}`}>
      <button type="button" onClick={onOpen} className="flex w-full items-start gap-2.5 rounded-md px-1.5 py-1 text-left hover:bg-panel/60">
        {runner.silkUrl ? <img src={runner.silkUrl} alt="" className="h-10 w-10 shrink-0 rounded-sm object-contain" /> : <div className="h-10 w-10 shrink-0 rounded-sm bg-panel" />}
        <div className="min-w-0 flex-1">
          <div className="flex flex-wrap items-baseline gap-x-2">
            <span className="font-mono text-sm font-semibold text-ink">{formatTimeOfDay(race.startTime)}</span>
            <span className="text-xs text-ink-mute">
              {race.venue} R{race.raceNumber}
              {race.distance ? ` · ${race.distance}m` : ''}
              {race.going ? ` · ${race.going}` : ''}
            </span>
          </div>
          <div className={`truncate text-base font-semibold text-ink ${scratched ? 'line-through' : ''}`}>
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
        {hasRunnerBias(play.runner) && (
          <span title="How far the track bias read from earlier races at this meeting moved this runner's projection (already inside Proj and SM)" className="rounded-full border border-amber-line bg-amber-bg px-2 py-0.5 font-mono text-[11px] font-semibold text-amber">
            bias {fmtBias(play.bias)}
          </span>
        )}
        {play.droppedKinds.length > 0 && play.kinds.length === 0 && play.outcome === 'pending' && <span className="text-[11px] text-ink-faint">no longer qualifies</span>}
        {(play.price ?? 0) > 5 && <span className="rounded-full border border-line bg-panel px-2 py-0.5 font-mono text-[11px] text-ink-soft">over $5</span>}
        {play.isFavourite && <span className="rounded-full border border-line bg-panel px-2 py-0.5 font-mono text-[11px] text-ink-soft">favourite</span>}
        {play.fieldSize >= 10 && <span className="rounded-full border border-line bg-panel px-2 py-0.5 font-mono text-[11px] text-ink-soft">{play.fieldSize} runners</span>}
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
      />
      <div className="flex flex-wrap items-center justify-between gap-x-4 gap-y-0.5 px-2 pb-1 text-xs">
        <ResultStrip play={play} />
        <span className="text-ink-faint">
          {play.rank === 1 ? `lead ${fmtWpr(play.lead)} WPR` : `${fmtWpr(play.gap)} off the top`}
          {runner.startingPrice != null && runner.fixedWinPrice != null && runner.startingPrice !== runner.fixedWinPrice ? ` · SP ${fmtPrice(runner.startingPrice)}` : ''}
        </span>
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
  historyPending,
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
  historyPending: boolean
}) {
  const [period, setPeriod] = useState<Period>('day')
  const [kindFilter, setKindFilter] = useState<KindFilter>('all')
  const [overFive, setOverFive] = useState(false)
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
    () => dayPlays.filter((p) => (kindFilter === 'all' || p.kinds.includes(kindFilter) || p.droppedKinds.includes(kindFilter)) && (!overFive || (p.price ?? 0) > 5)),
    [dayPlays, kindFilter, overFive],
  )

  const dayTally = tally(dayPlays)
  const quickDates = [
    { label: 'Yesterday', d: todayIso(-1) },
    { label: 'Today', d: todayIso() },
    { label: 'Tomorrow', d: todayIso(1) },
  ]

  return (
    <div className="flex flex-col gap-4">
      <div className="flex flex-wrap items-center gap-2">
        {quickDates.map((b) => (
          <Pill key={b.label} active={date === b.d} onClick={() => onDateChange(b.d)}>
            {b.label}
          </Pill>
        ))}
        <div className="flex items-center gap-1">
          <button type="button" aria-label="Previous day" onClick={() => onDateChange(shiftDate(date, -1))} className="rounded-md border border-line bg-panel px-2 py-1 text-sm text-ink-mute hover:text-ink">
            &lsaquo;
          </button>
          <input type="date" value={date} onChange={(e) => e.target.value && onDateChange(e.target.value)} className="rounded-md border border-line bg-panel px-2 py-1 text-sm font-mono" />
          <button type="button" aria-label="Next day" onClick={() => onDateChange(shiftDate(date, 1))} className="rounded-md border border-line bg-panel px-2 py-1 text-sm text-ink-mute hover:text-ink">
            &rsaquo;
          </button>
        </div>
      </div>

      <section className="rounded-lg border border-line bg-panel p-3">
        <div className="flex flex-wrap items-center justify-between gap-2">
          <h2 className="text-sm font-semibold text-ink">Scoreboard</h2>
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
                <th className="hidden px-1 text-right font-medium sm:table-cell">Plays</th>
                <th className="px-1 text-right font-medium">Run</th>
                <th className="px-1 text-right font-medium">Won</th>
                <th className="px-1 text-right font-medium">Strike</th>
                <th className="px-1 text-right font-medium">Placed</th>
                <th className="hidden px-1 text-right font-medium sm:table-cell">Avg $</th>
                <th className="pl-1 text-right font-medium">$1 win</th>
              </tr>
            </thead>
            <tbody>
              {TRACK_ROWS.map((row) => {
                const t = tally(periodPlays.filter(row.test))
                return (
                  <tr key={row.id} className="border-t border-line-soft">
                    <td className="py-1 pr-2 text-ink" title={row.label}><span className="sm:hidden">{row.short}</span><span className="hidden sm:inline">{row.label}</span></td>
                    <td className="hidden px-1 text-right font-mono sm:table-cell">{t.plays}</td>
                    <td className="px-1 text-right font-mono">{t.run}</td>
                    <td className="px-1 text-right font-mono">{t.wins}</td>
                    <td className="px-1 text-right font-mono">{pct(t.wins, t.run)}</td>
                    <td className="px-1 text-right font-mono">{pct(t.places, t.run)}</td>
                    <td className="hidden px-1 text-right font-mono sm:table-cell">{t.avgPrice != null ? `$${t.avgPrice.toFixed(2)}` : '-'}</td>
                    <td className={`pl-1 text-right font-mono ${t.roi == null ? '' : t.roi >= 0 ? 'text-emerald-deep' : 'text-rose'}`}>{fmtRoi(t.roi)}</td>
                  </tr>
                )
              })}
            </tbody>
          </table>
        </div>
        <p className="mt-2 text-[11px] text-ink-faint">
          A play is kept from the moment it qualifies and stays after the race has run. Placed counts the paying places (3 for 8+ runners, 2 for 5 to 7). $1 win is a flat
          $1 to win at SP, else the last fixed price. Out of sample (15 months) none of these showed a robust profit and the live speed map is flatter than the one tested,
          so this table is how that gets checked. A filter, not a tip.{historyPending && period !== 'day' ? ' Earlier days are still loading.' : ''}
        </p>
      </section>

      <div className="flex flex-wrap items-center gap-1.5">
        <Pill active={kindFilter === 'all'} onClick={() => setKindFilter('all')}>
          All ({dayPlays.length})
        </Pill>
        {PLAY_KINDS.map((k) => (
          <Pill key={k.kind} active={kindFilter === k.kind} onClick={() => setKindFilter(k.kind)}>
            {k.label} ({dayPlays.filter((p) => p.kinds.includes(k.kind)).length})
          </Pill>
        ))}
        <Pill active={overFive} onClick={() => setOverFive(!overFive)}>
          Over $5
        </Pill>
        {dayTally.run > 0 && (
          <span className="ml-auto text-xs text-ink-mute">
            {dayTally.wins} won, {dayTally.places} placed of {dayTally.run} run
          </span>
        )}
      </div>

      {listed.length === 0 ? (
        <EmptyState message={dayPlays.length === 0 ? 'No plays for this day yet. They appear once projections are in.' : 'No plays match these filters.'} progress={null} />
      ) : (
        <div className="flex flex-col gap-3">
          {listed.map((p) => (
            <PlayCard key={p.key} play={p} onOpen={() => onOpen(p.race.raceId, p.race.date, p.runner.runId)} />
          ))}
        </div>
      )}
    </div>
  )
}
