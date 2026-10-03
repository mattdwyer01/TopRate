import { useMemo, useState } from 'react'
import { StatTile } from '../../components/StatTile'
import { formatTimeOfDay } from '../../lib/countdown'
import { useBetsLog, type LoggedBet } from '../../lib/betsLog'

// Bets tab: every bet the betting rules made for a day and how it went. Reads bets_log.json, written by the TAB poller
// (bet_log.py): each bet is frozen ~10 minutes before its race (a quaddie before its first leg) from the data as it
// was then, and settled from TAB's real dividends (exotics return dividend x stake / combinations, i.e. the flexi %).

const LABEL: Record<LoggedBet['bet'], string> = { Win: 'WIN', Trifecta: 'TRI', Quinella: 'QUIN', Quaddie: 'QUAD', EarlyQuaddie: 'EARLY' }
const TAG: Record<LoggedBet['bet'], string> = {
  Win: 'bg-emerald text-white',
  Trifecta: 'bg-indigo text-white',
  Quinella: 'bg-indigo-bg text-indigo border border-indigo',
  Quaddie: 'bg-amber text-white',
  EarlyQuaddie: 'bg-amber-bg text-amber border border-amber-line',
}
// within a race: win first, then quinella, trifecta, quaddies
const ORDER: Record<LoggedBet['bet'], number> = { Win: 0, Quinella: 1, Trifecta: 2, EarlyQuaddie: 3, Quaddie: 4 }
const STATUS: Record<LoggedBet['status'], string> = {
  pending: 'text-ink-faint',
  won: 'text-emerald font-semibold',
  lost: 'text-rose',
  refund: 'text-ink-mute',
  void: 'text-ink-mute',
}

const money = (v: number | null | undefined, sign = false) =>
  v == null ? '-' : `${sign && v > 0 ? '+' : v < 0 ? '−' : ''}$${Math.abs(v).toFixed(0)}`

function melbourneToday(): string {
  return new Date().toLocaleDateString('en-CA', { timeZone: 'Australia/Melbourne' })
}

function shiftDay(d: string, n: number): string {
  const t = new Date(`${d}T12:00:00Z`)
  t.setUTCDate(t.getUTCDate() + n)
  return t.toISOString().slice(0, 10)
}

export function BetsTab({ onSelectRace }: { onSelectRace: (raceId: string, date: string) => void }) {
  const { bets, error } = useBetsLog()
  const [day, setDay] = useState(melbourneToday())

  const dayBets = useMemo(
    () =>
      (bets ?? [])
        .filter((b) => b.date === day)
        .sort((a, b) => a.start_utc.localeCompare(b.start_utc) || ORDER[a.bet] - ORDER[b.bet]),
    [bets, day],
  )
  const settled = dayBets.filter((b) => b.status !== 'pending')
  const staked = settled.reduce((s, b) => s + b.stake, 0)
  const returned = settled.reduce((s, b) => s + (b.return ?? 0), 0)
  const profit = returned - staked
  const pending = dayBets.filter((b) => b.status === 'pending')
  const byType = (['Win', 'Quinella', 'Trifecta', 'EarlyQuaddie', 'Quaddie'] as const).map((t) => {
    const g = settled.filter((b) => b.bet === t)
    const st = g.reduce((s, b) => s + b.stake, 0)
    const rt = g.reduce((s, b) => s + (b.return ?? 0), 0)
    return { t, n: g.length, won: g.filter((b) => b.status === 'won').length, st, pr: rt - st }
  })

  // running total across every logged day (settled bets only)
  const allSettled = (bets ?? []).filter((b) => b.status !== 'pending')
  const allProfit = allSettled.reduce((s, b) => s + (b.return ?? 0) - b.stake, 0)
  const allStaked = allSettled.reduce((s, b) => s + b.stake, 0)

  return (
    <div className="flex flex-col gap-4">
      <div className="flex flex-wrap items-center justify-between gap-2">
        <div className="flex items-center gap-1">
          <button type="button" className="rounded border border-line bg-panel px-2 py-1 text-sm" onClick={() => setDay(shiftDay(day, -1))} aria-label="Previous day">
            ‹
          </button>
          <input
            id="bets-day"
            type="date"
            value={day}
            onChange={(e) => e.target.value && setDay(e.target.value)}
            className="rounded border border-line bg-panel px-2 py-1 font-mono text-sm text-ink"
          />
          <button type="button" className="rounded border border-line bg-panel px-2 py-1 text-sm" onClick={() => setDay(shiftDay(day, 1))} aria-label="Next day">
            ›
          </button>
        </div>
        <span className="text-xs text-ink-mute">
          All days: {allSettled.length} bets · {money(allProfit, true)}
          {allStaked > 0 && ` (${((allProfit / allStaked) * 100).toFixed(0)}%)`}
        </span>
      </div>

      {error && !bets && <div className="rounded-md border border-line bg-panel p-4 text-sm text-ink-mute">{error}</div>}

      <div className="grid grid-cols-2 gap-2 sm:grid-cols-4">
        <StatTile label="Bets" value={String(dayBets.length)} sublabel={pending.length ? `${pending.length} pending` : 'all settled'} />
        <StatTile label="Staked" value={money(staked)} sublabel="settled bets" />
        <StatTile label="Returned" value={money(returned)} />
        <StatTile
          label="Profit"
          value={money(profit, true)}
          sublabel={staked > 0 ? `${((profit / staked) * 100).toFixed(0)}% on turnover` : undefined}
          tone={profit > 0 ? 'positive' : profit < 0 ? 'negative' : 'default'}
        />
      </div>

      <div className="flex flex-col divide-y divide-line-soft overflow-hidden rounded-lg border border-line bg-panel">
        {dayBets.length === 0 && (
          <div className="px-3 py-6 text-center text-sm text-ink-mute">
            {bets ? 'No bets logged for this day. Bets are locked about 10 minutes before each race.' : 'Loading…'}
          </div>
        )}
        {dayBets.map((b) => (
          <div key={b.bet_id} className="flex flex-col gap-1 px-3 py-2.5">
            <div className="flex items-center gap-2">
              <span className="w-10 flex-none font-mono text-xs text-ink-mute">{formatTimeOfDay(b.start_utc)}</span>
              <span className={`w-12 flex-none rounded px-1 text-center text-[10px] font-bold tracking-wide ${TAG[b.bet]}`}>{LABEL[b.bet]}</span>
              <button
                type="button"
                className="min-w-0 flex-1 truncate text-left text-sm font-medium text-ink hover:underline"
                onClick={() => onSelectRace(b.race_id, b.date)}
              >
                {b.venue} R{b.bet === 'Win' || b.bet === 'Trifecta' || b.bet === 'Quinella' ? b.race : b.legs.replace('-', '-R')}
              </button>
              <span
                className={`flex-none font-mono text-sm font-semibold ${
                  b.status === 'pending' ? 'text-ink-faint' : (b.profit ?? 0) > 0 ? 'text-emerald' : (b.profit ?? 0) < 0 ? 'text-rose' : 'text-ink'
                }`}
              >
                {b.status === 'pending' ? 'pending' : b.status === 'refund' || b.status === 'void' ? b.status : money(b.profit, true)}
              </span>
            </div>
            <div className="pl-12 text-xs text-ink">{b.selection}</div>
            <div className="flex flex-wrap gap-x-3 gap-y-0.5 pl-12 font-mono text-[11px] text-ink-mute">
              <span>
                stake {money(b.stake)}
                {b.bet === 'Win' ? (b.price ? ` @ $${b.price.toFixed(2)}` : '') : ` · ${b.combos} combos · ${b.flexi_pct}%`}
              </span>
              {b.bet !== 'Win' && b.dividend != null && <span>div ${b.dividend.toFixed(2)}</span>}
              {b.winners && <span>result {b.winners}</span>}
              {b.status !== 'pending' && <span className={STATUS[b.status]}>return {money(b.return)}</span>}
            </div>
          </div>
        ))}
      </div>

      {settled.length > 0 && (
        <div className="grid grid-cols-2 gap-2 text-xs sm:grid-cols-4">
          {byType.filter((x) => x.n).map((x) => (
            <div key={x.t} className="rounded-md border border-line bg-panel px-3 py-2">
              <span className={`rounded px-1.5 text-[10px] font-bold tracking-wide ${TAG[x.t]}`}>{LABEL[x.t]}</span>
              <div className="mt-1 text-ink-mute">
                {x.won}/{x.n} won · staked {money(x.st)}
              </div>
              <div className={`font-mono font-semibold ${x.pr > 0 ? 'text-emerald' : x.pr < 0 ? 'text-rose' : 'text-ink'}`}>{money(x.pr, true)}</div>
            </div>
          ))}
        </div>
      )}

      <p className="text-xs text-ink-faint">
        Bets are locked about 10 minutes before each race (a quaddie before its first leg) from the dashboard data at that
        moment, so later changes never rewrite them. Win: stake returns $200 at the fixed price then. Exotics: TAB dividend ×
        flexi % (stake ÷ combinations). Rules are on the race page's Bets box.
      </p>
    </div>
  )
}
