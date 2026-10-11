import { useEffect, useMemo, useState } from 'react'
import type { Race } from '../../types/domain'
import { Pill } from '../../components/Pill'
import { EmptyState } from '../../components/EmptyState'
import { fmtPrice } from '../../lib/format'
import { formatCountdown, formatTimeOfDay } from '../../lib/countdown'
import { bushMeetingKeys, meetingKey, todayIso } from '../../lib/meetings'
import { computeBets, tally, type Bet } from '../../lib/bets'
import { fmtEv, fmtStake, modelPrice, TIER_HELP, TIER_LABEL, TIER_UNITS, type BetSignals } from '../../lib/betSignals'

// The Plays tab: bets from the bet-signal model (lib/betSignals.ts), EXPERIMENTAL. Select is the tier with a backtested edge; Volume is the
// near break-even action tier, small stakes. Everything is judged at the fixed price when the pass was made (not SP), and the scoreboard
// below counts only those, so it is the live check on a backtest that was run against closing SP.

type Period = 'day' | '7' | 'all'

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

const fmtUnits = (u: number) => `${u >= 0 ? '+' : ''}${u.toFixed(1)}u`
const fmtRoi = (v: number | null) => (v == null ? '-' : `${v >= 0 ? '+' : ''}${(v * 100).toFixed(0)}%`)
const pct = (a: number, b: number) => (b > 0 ? `${Math.round((a / b) * 100)}%` : '-')

function Result({ bet }: { bet: Bet }) {
  const fin = bet.runner.finishPosition
  if (bet.outcome === 'pending') return <span className="text-ink-faint">To run</span>
  const label = bet.outcome === 'won' ? 'Won' : bet.outcome === 'placed' ? `Placed ${fin != null ? ordinal(fin) : ''}` : fin != null ? ordinal(fin) : 'Unplaced'
  const tone = bet.outcome === 'won' ? 'text-emerald-deep' : bet.outcome === 'placed' ? 'text-amber' : 'text-rose'
  return (
    <span>
      <span className={`font-semibold ${tone}`}>{label}</span>
      <span className={`ml-1 font-mono ${bet.profit >= 0 ? 'text-emerald-deep' : 'text-rose'}`} title={`${bet.units}u at ${fmtPrice(bet.price)}`}>
        {fmtUnits(bet.profit)}
      </span>
    </span>
  )
}

function BetCard({ bet, onOpen }: { bet: Bet; onOpen: () => void }) {
  const { runner, race, sig } = bet
  const tone = bet.outcome === 'won' ? 'bg-emerald-bg' : bet.outcome === 'placed' ? 'bg-amber-bg' : 'bg-panel'
  return (
    <button type="button" onClick={onOpen} className={`flex w-full items-start gap-2.5 rounded-lg border border-line px-3 py-2 text-left hover:bg-bg ${tone}`}>
      {runner.silkUrl ? <img src={runner.silkUrl} alt="" className="mt-0.5 h-8 w-8 shrink-0 rounded-sm object-contain" /> : <div className="mt-0.5 h-8 w-8 shrink-0 rounded-sm bg-bg" />}
      <div className="min-w-0 flex-1">
        <div className="flex flex-wrap items-baseline gap-x-2">
          <span className="font-mono text-xs font-semibold text-ink">{formatTimeOfDay(race.startTime)}</span>
          <span className="text-xs text-ink-mute">
            {race.venue} R{race.raceNumber}
            {race.distance ? ` · ${race.distance}m` : ''}
            {` · ${bet.fieldSize} runners`}
          </span>
        </div>
        <div className="truncate text-[15px] font-semibold text-ink">
          {runner.tabNumber}. {runner.horse}
        </div>
        <div className="truncate text-xs text-ink-mute">
          {runner.jockey || 'Jockey TBA'} / {runner.trainer}
        </div>
        <div className="mt-1 flex flex-wrap items-center gap-x-3 gap-y-1 text-xs">
          <span className="font-mono text-ink" title="Fixed price when the pass was made">
            {fmtPrice(bet.price)}
          </span>
          <span className="font-mono text-ink-mute" title={`Model win chance ${(sig.m * 100).toFixed(1)}%`}>
            model {fmtPrice(modelPrice(sig.m))}
          </span>
          <span className="font-mono font-semibold text-emerald-deep" title="Model win chance x price, minus 1">
            EV {fmtEv(sig.e)}
          </span>
          <span className="text-ink-faint">{sig.k === 1 ? 'favourite' : `${ordinal(sig.k)} in market`}</span>
          {bet.backfilled && (
            <span className="rounded-full border border-line px-1.5 text-[10px] text-ink-faint" title="Scored after the event by the model as it stood before that day, not a live pass: judged at the closing starting price (or the last recorded fixed price), not a price taken before the jump.">
              backfilled at {bet.backfilled === 'sp' ? 'SP' : 'last price'}
            </span>
          )}
        </div>
      </div>
      <div className="flex shrink-0 flex-col items-end text-right">
        <span className="font-mono text-base font-bold text-ink">
          {bet.units}u
        </span>
        <span className="font-mono text-[11px] text-ink-faint">{fmtStake(bet.units)}</span>
        <span className="mt-0.5 text-xs">
          <Result bet={bet} />
        </span>
      </div>
    </button>
  )
}

function Section({ tier, bets, onOpen }: { tier: 'S' | 'V'; bets: Bet[]; onOpen: (b: Bet) => void }) {
  const units = bets.reduce((s, b) => s + b.units, 0)
  const t = tally(bets)
  return (
    <section className="flex flex-col gap-2">
      <div className="flex flex-wrap items-baseline gap-x-2" title={TIER_HELP[tier]}>
        <h2 className="text-sm font-semibold text-ink">{TIER_LABEL[tier]}</h2>
        <span className="text-xs text-ink-mute">
          {bets.length} {bets.length === 1 ? 'bet' : 'bets'} · {TIER_UNITS[tier]}u ({fmtStake(TIER_UNITS[tier])}) each · {units}u staked
        </span>
        {t.run > 0 && (
          <span className="ml-auto text-xs text-ink-mute">
            {t.wins} won of {t.run} run, <span className={t.profit >= 0 ? 'text-emerald-deep' : 'text-rose'}>{fmtUnits(t.profit)}</span>
          </span>
        )}
      </div>
      {bets.length === 0 ? (
        <p className="rounded-md border border-line-soft bg-panel px-3 py-2 text-xs text-ink-faint">
          {tier === 'S' ? 'No Select bets yet. These are rare (under one a Saturday on average) and only appear once a race is drawn and priced.' : 'No Volume bets yet.'}
        </p>
      ) : (
        <div className="flex flex-col gap-2">
          {bets.map((b) => (
            <BetCard key={b.key} bet={b} onOpen={() => onOpen(b)} />
          ))}
        </div>
      )}
    </section>
  )
}

export function PlaysTab({
  races,
  date,
  onDateChange,
  onOpen,
  signals,
  scratched,
  showBush,
  hiddenVenues,
}: {
  races: Race[]
  date: string
  onDateChange: (d: string) => void
  onOpen: (raceId: string, date: string, runId: string) => void
  signals: BetSignals | null
  scratched: Set<string>
  showBush: boolean
  hiddenVenues: Set<string>
}) {
  const [period, setPeriod] = useState<Period>('day')
  const [now, setNow] = useState(() => Date.now())
  useEffect(() => {
    const t = window.setInterval(() => setNow(Date.now()), 30_000)
    return () => window.clearInterval(t)
  }, [])

  const visible = useMemo(() => {
    const bush = showBush ? null : bushMeetingKeys(races)
    return races.filter((r) => !hiddenVenues.has(r.venue) && !(bush && bush.has(meetingKey(r))))
  }, [races, showBush, hiddenVenues])

  const dayBets = useMemo(() => computeBets(visible.filter((r) => r.date === date), signals, scratched), [visible, date, signals, scratched])
  const periodBets = useMemo(() => {
    if (period === 'day') return dayBets
    const from = period === '7' ? shiftDate(date, -6) : '0000-00-00'
    return computeBets(visible.filter((r) => r.date >= from && r.date <= date), signals, scratched)
  }, [period, dayBets, visible, date, signals, scratched])

  const select = dayBets.filter((b) => b.tier === 'S')
  const volume = dayBets.filter((b) => b.tier === 'V')
  const open = (b: Bet) => onOpen(b.race.raceId, b.race.date, b.runner.runId)
  const dayTally = tally(dayBets)
  const next = date === todayIso() ? dayBets.find((b) => b.outcome === 'pending' && new Date(b.race.startTime).getTime() > now) : undefined

  return (
    <div className="flex flex-col gap-4">
      <div className="rounded-md border border-amber-line bg-amber-bg px-3 py-2 text-xs text-amber">
        <span className="font-semibold">Experimental.</span> A model that starts from the market price and corrects it. Backtested against closing SP only (2022 to 2026): Select about +53%, Volume about -3% on its own
        (it is the action tier, small stakes) and worse if the price you get is 10% below SP. Not yet shown to hold at a price taken before the jump. The scoreboard below is that check. These are the pure model's tiers, not the blended Rating. Not a tip.
      </div>

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
        <span className="ml-auto text-xs text-ink-mute">
          {dayBets.length} {dayBets.length === 1 ? 'bet' : 'bets'} · {dayBets.reduce((s, b) => s + b.units, 0)}u staked
          {dayTally.run > 0 && (
            <>
              {' · '}
              {dayTally.wins} won of {dayTally.run}, <span className={dayTally.profit >= 0 ? 'text-emerald-deep' : 'text-rose'}>{fmtUnits(dayTally.profit)}</span>
            </>
          )}
        </span>
      </div>

      {!signals ? (
        <EmptyState message="Bet signals are not available yet. They are written by the scoring step once a race is drawn and priced." progress={null} />
      ) : (
        <>
          {next && (
            <button
              type="button"
              onClick={() => open(next)}
              className="self-start rounded-full border border-emerald-line bg-emerald-bg px-3 py-1 text-xs font-semibold text-emerald-deep"
            >
              Next: {next.race.venue} R{next.race.raceNumber} in {formatCountdown(next.race.startTime, new Date(now))}
            </button>
          )}
          <Section tier="S" bets={select} onOpen={open} />
          <Section tier="V" bets={volume} onOpen={open} />
        </>
      )}

      <details className="rounded-lg border border-line bg-panel p-3">
        <summary className="cursor-pointer text-sm font-semibold text-ink">Scoreboard: how each tier has done (live: at the price when the pass was made; backfilled: at SP or the last price)</summary>
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
                <th className="py-1 pr-2 font-medium">Tier</th>
                <th className="px-1 text-right font-medium">Run</th>
                <th className="px-1 text-right font-medium">Won</th>
                <th className="px-1 text-right font-medium">Strike</th>
                <th className="px-1 text-right font-medium">Avg $</th>
                <th className="px-1 text-right font-medium">Staked</th>
                <th className="px-1 text-right font-medium">Profit</th>
                <th className="pl-1 text-right font-medium" title="Profit over units staked">ROI</th>
                <th className="pl-1 text-right font-medium" title="Flat 1u per bet, comparable with the backtest">Flat</th>
              </tr>
            </thead>
            <tbody>
              {([
                ['S', 'Select, live', periodBets.filter((b) => b.tier === 'S' && !b.backfilled)],
                ['V', 'Volume, live', periodBets.filter((b) => b.tier === 'V' && !b.backfilled)],
                ['all', 'Both, live, as staked', periodBets.filter((b) => !b.backfilled)],
                ['S', 'Select, backfilled', periodBets.filter((b) => b.tier === 'S' && b.backfilled)],
                ['V', 'Volume, backfilled', periodBets.filter((b) => b.tier === 'V' && b.backfilled)],
                ['all', 'Both, backfilled, as staked', periodBets.filter((b) => b.backfilled)],
              ] as const).map(([, label, list]) => {
                const t = tally(list)
                return (
                  <tr key={label} className={`border-t border-line-soft ${label.includes('backfilled') ? 'text-ink-mute' : ''}`}>
                    <td className="py-1 pr-2 text-ink">{label}</td>
                    <td className="px-1 text-right font-mono">{t.run}</td>
                    <td className="px-1 text-right font-mono">{t.wins}</td>
                    <td className="px-1 text-right font-mono">{pct(t.wins, t.run)}</td>
                    <td className="px-1 text-right font-mono">{t.avgPrice != null ? fmtPrice(t.avgPrice) : '-'}</td>
                    <td className="px-1 text-right font-mono">{t.staked.toFixed(1)}u</td>
                    <td className={`px-1 text-right font-mono ${t.profit >= 0 ? 'text-emerald-deep' : 'text-rose'}`}>{t.run ? fmtUnits(t.profit) : '-'}</td>
                    <td className={`pl-1 text-right font-mono ${t.roi == null ? '' : t.roi >= 0 ? 'text-emerald-deep' : 'text-rose'}`}>{fmtRoi(t.roi)}</td>
                    <td className={`pl-1 text-right font-mono ${t.flatRoi == null ? '' : t.flatRoi >= 0 ? 'text-emerald-deep' : 'text-rose'}`}>{fmtRoi(t.flatRoi)}</td>
                  </tr>
                )
              })}
            </tbody>
          </table>
        </div>
        <p className="mt-2 text-[11px] text-ink-faint">
          Backtest for comparison (SP, 2022 to 2026): Select flat ROI about +53% (about 120 bets a year, 0.7 a Saturday), Volume bets alone about -3% (-13% with a price 10% worse).
          Backfilled rows are out-of-sample but judged at SP / the last recorded price, so they are for context only: the live rows are the real test. A few weeks of live bets cannot separate those from luck: judge it over months.
        </p>
      </details>
    </div>
  )
}
