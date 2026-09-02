import { useMemo, useState } from 'react'
import type { Race, Runner } from '../../types/domain'
import { bushMeetingKeys, meetingKey, todayIso } from '../../lib/meetings'
import { fmtPrice } from '../../lib/format'
import { StatTile } from '../../components/StatTile'
import { Pill } from '../../components/Pill'

interface SummaryTabProps {
  races: Race[]
  onSelectRace: (raceId: string, date: string, runId?: string) => void
  showBush: boolean
  onShowBushChange: (v: boolean) => void
}

// Three qualifying tiers on WPR's own edge (model price vs market price,
// price<=$26 throughout) - thresholds and the backtest numbers below are
// from a genuinely leak-free walk-forward test (every population artifact
// fit on one date-half, scored purely on the other, both directions
// pooled - see wpr_bet_selection_leakfree_eval.py, chat Sep 2026), not a
// live guarantee. Ordered strongest-signal-first for display.
const TIERS = [
  {
    key: 'value',
    label: 'Value',
    minEdge: 0.20,
    backtest: 'edge ≥ 20%, price ≤ $26: n=790, ROI +53.3%, t=4.55 (leak-free backtest)',
  },
  {
    key: 'mid',
    label: 'Mid',
    minEdge: 0.10,
    backtest: 'edge ≥ 10%, price ≤ $26: n=2,720, ROI +44.7%, t=6.68 (leak-free backtest)',
  },
  {
    key: 'volume',
    label: 'High Volume',
    minEdge: 0.05,
    backtest: 'edge ≥ 5%, price ≤ $26: n=5,994, ROI +31.4%, t=6.79 (leak-free backtest)',
  },
] as const

type Tier = (typeof TIERS)[number]

const PRICE_CAP = 26
// Proportional ("to return") staking: stake sized so a WIN returns exactly
// this many units total (stake back + profit), regardless of price - a
// short-priced favourite needs a bigger stake to return the same amount as
// a long shot. 1 unit = $50 elsewhere in this dashboard, kept in units here
// (not converted to $) since that's how a staking plan is normally talked
// about. stake = RETURN_UNITS / price; win profit = RETURN_UNITS - stake;
// loss profit = -stake. Per explicit user decision (Sep 2026) - confirmed
// "return" means total payback, not profit-on-top.
const RETURN_UNITS = 4

interface Pick {
  race: Race
  runner: Runner
  tier: Tier
  price: number
}

/** The price basis actually used to compute this runner's stored edge
 * (see toprate_daily.py's compute_edge_score/wpr_backfill_historical_
 * projections.py: fixed_win_price, falling back to starting_price_sp then
 * price_top) - matched here so a pick's qualification, displayed market
 * price, and P&L all agree on the same number. */
function marketPrice(runner: Runner): number | null {
  return runner.fixedWinPrice ?? runner.startingPrice ?? runner.postRaceTopPrice
}

/** Every non-scratched runner on the given date that clears a tier's edge
 * threshold with a market price under the cap - assigned to the single
 * HIGHEST tier it clears (a big edge shouldn't also clutter the lower
 * tiers). Mirrors the exact "edge" WPR already computes (WPR's own price
 * vs the market's, see wpr_projection.compute_edge_scores) - no separate
 * blend, no re-derivation here. Requires a live projectedWpr - a small,
 * permanent fraction of races never get a result recorded at all
 * (abandoned meetings, missing results feeds), and some pre-WPR-alone-edge
 * rows still carry a stale edge value computed under the old blend formula
 * - both filtered out by requiring a current projection alongside the
 * edge. Included regardless of whether the race has resulted yet - the
 * caller decides whether to show a live shortlist or a P&L review from
 * that alone. */
function collectPicks(races: Race[], date: string): Pick[] {
  const picks: Pick[] = []
  for (const race of races) {
    if (race.date !== date) continue
    for (const runner of race.runners) {
      if (runner.dataScratched) continue
      if (runner.projectedWpr == null || runner.edge == null) continue
      const price = marketPrice(runner)
      if (price == null || price > PRICE_CAP) continue
      const tier = TIERS.find((t) => runner.edge! >= t.minEdge)
      if (!tier) continue
      picks.push({ race, runner, tier, price })
    }
  }
  return picks
}

function raceTime(race: Race): number {
  const t = Date.parse(race.startTime)
  return Number.isNaN(t) ? Infinity : t
}

// A handful of races carry no start_time at all (a genuine gap in the
// source data, not a bug - see toprate_daily.py's rebuild_html) -
// Date.parse('') is NaN, and new Date(NaN).toLocaleTimeString() renders
// the literal text "Invalid Date" rather than throwing, so this needs an
// explicit guard rather than relying on it to fail loudly.
function fmtRaceTime(race: Race): string {
  const t = raceTime(race)
  if (!Number.isFinite(t)) return '-'
  return new Date(t).toLocaleTimeString([], { hour: '2-digit', minute: '2-digit' })
}

interface PickResult {
  resulted: boolean
  won: boolean
  stake: number
  profit: number
}

function resultOf(pick: Pick): PickResult {
  if (pick.runner.finishPosition == null) {
    return { resulted: false, won: false, stake: 0, profit: 0 }
  }
  const stake = RETURN_UNITS / pick.price
  const profit = pick.runner.won ? RETURN_UNITS - stake : -stake
  return { resulted: true, won: pick.runner.won, stake, profit }
}

function fmtUnits(v: number): string {
  return `${v > 0 ? '+' : ''}${v.toFixed(2)}u`
}

function fmtRoiPct(v: number): string {
  return `${v > 0 ? '+' : ''}${v.toFixed(1)}%`
}

const DATE_QUICK_BUTTONS: { label: string; offset: number }[] = [
  { label: 'Yesterday', offset: -1 },
  { label: 'Today', offset: 0 },
  { label: 'Tomorrow', offset: 1 },
]

export function SummaryTab({ races, onSelectRace, showBush, onShowBushChange }: SummaryTabProps) {
  const [date, setDate] = useState(() => todayIso())
  const [activeTierKey, setActiveTierKey] = useState<Tier['key']>(TIERS[0].key)
  const activeTier = TIERS.find((t) => t.key === activeTierKey)!

  const scoped = useMemo(() => {
    if (showBush) return races
    const bushKeys = bushMeetingKeys(races)
    return races.filter((r) => !bushKeys.has(meetingKey(r)))
  }, [races, showBush])

  const allPicks = useMemo(() => collectPicks(scoped, date), [scoped, date])
  const byTier = useMemo(() => {
    const m = new Map<string, Pick[]>()
    for (const tier of TIERS) m.set(tier.key, [])
    for (const p of allPicks) m.get(p.tier.key)!.push(p)
    for (const list of m.values()) list.sort((a, b) => raceTime(a.race) - raceTime(b.race))
    return m
  }, [allPicks])

  const list = byTier.get(activeTierKey) ?? []
  const stats = useMemo(() => {
    let resulted = 0
    let wins = 0
    let staked = 0
    let profit = 0
    for (const pick of list) {
      const r = resultOf(pick)
      if (!r.resulted) continue
      resulted++
      if (r.won) wins++
      staked += r.stake
      profit += r.profit
    }
    return {
      n: list.length,
      resulted,
      wins,
      strikePct: resulted > 0 ? (wins / resulted) * 100 : null,
      staked,
      profit,
      roiPct: staked > 0 ? (profit / staked) * 100 : null,
    }
  }, [list])

  return (
    <div className="flex flex-col gap-5">
      <div className="flex items-center justify-between">
        <div>
          <h2 className="text-base font-semibold text-ink">Betting Options</h2>
          <p className="mt-0.5 text-sm text-ink-mute">
            Runners where WPR rates them shorter than the market by a validated margin. Not a bet
            log - a live shortlist, with a P&amp;L review of what proportional staking (to return{' '}
            {RETURN_UNITS} units) would have made once a date's races have resulted.
          </p>
        </div>
        <label className="flex items-center gap-1.5 text-sm text-ink-mute">
          <input
            type="checkbox"
            checked={showBush}
            onChange={(e) => onShowBushChange(e.target.checked)}
          />
          Show bush meetings
        </label>
      </div>

      <div className="flex flex-wrap items-center gap-2">
        {DATE_QUICK_BUTTONS.map((btn) => {
          const btnDate = todayIso(btn.offset)
          return (
            <Pill key={btn.label} active={date === btnDate} onClick={() => setDate(btnDate)}>
              {btn.label}
            </Pill>
          )
        })}
        <input
          type="date"
          value={date}
          onChange={(e) => setDate(e.target.value)}
          className="rounded-md border border-line bg-panel px-2 py-1 text-sm font-mono"
        />
      </div>

      <div className="flex flex-wrap gap-2">
        {TIERS.map((tier) => (
          <Pill key={tier.key} active={tier.key === activeTierKey} onClick={() => setActiveTierKey(tier.key)}>
            {tier.label} ({byTier.get(tier.key)?.length ?? 0})
          </Pill>
        ))}
      </div>

      <section className="flex flex-col gap-3">
        <div className="grid grid-cols-2 gap-3 sm:grid-cols-4">
          <StatTile label="Picks" value={String(stats.n)} sublabel={activeTier.backtest} />
          <StatTile
            label="Strike rate"
            value={stats.strikePct != null ? `${stats.strikePct.toFixed(1)}%` : '-'}
            sublabel={stats.resulted > 0 ? `${stats.wins} wins / ${stats.resulted} resulted` : 'none resulted yet'}
          />
          <StatTile
            label="Staked"
            value={stats.resulted > 0 ? `${stats.staked.toFixed(2)}u` : '-'}
          />
          <StatTile
            label="P&L"
            value={stats.resulted > 0 ? fmtUnits(stats.profit) : '-'}
            sublabel={stats.roiPct != null ? `ROI ${fmtRoiPct(stats.roiPct)}` : undefined}
            tone={stats.resulted === 0 ? 'muted' : stats.profit >= 0 ? 'positive' : 'negative'}
          />
        </div>

        {list.length === 0 ? (
          <p className="rounded-md border border-line bg-panel px-3 py-2 text-sm text-ink-faint">
            No qualifying runners on {date}.
          </p>
        ) : (
          <div className="overflow-x-auto rounded-md border border-line bg-panel">
            <table className="w-full text-left text-sm">
              <thead>
                <tr className="border-b border-line text-xs uppercase tracking-wide text-ink-mute">
                  <th className="px-3 py-2 font-medium">Time</th>
                  <th className="px-3 py-2 font-medium">Race</th>
                  <th className="px-3 py-2 font-medium">Horse</th>
                  <th className="px-3 py-2 font-medium text-right">WPR $</th>
                  <th className="px-3 py-2 font-medium text-right">Market $</th>
                  <th className="px-3 py-2 font-medium text-right">Edge</th>
                  <th className="px-3 py-2 font-medium text-right">Result</th>
                  <th className="px-3 py-2 font-medium text-right">Stake</th>
                  <th className="px-3 py-2 font-medium text-right">P&amp;L</th>
                </tr>
              </thead>
              <tbody>
                {list.map((pick) => {
                  const { race, runner } = pick
                  const r = resultOf(pick)
                  return (
                    <tr
                      key={runner.runId}
                      className="cursor-pointer border-b border-line last:border-0 hover:bg-bg"
                      onClick={() => onSelectRace(race.raceId, race.date, runner.runId)}
                    >
                      <td className="px-3 py-2 text-ink-mute">{fmtRaceTime(race)}</td>
                      <td className="px-3 py-2 text-ink-mute">
                        {race.venue} R{race.raceNumber}
                      </td>
                      <td className="px-3 py-2 font-medium text-ink">{runner.horse}</td>
                      <td className="px-3 py-2 text-right font-mono text-ink">{fmtPrice(runner.wprPrice)}</td>
                      <td className="px-3 py-2 text-right font-mono text-ink-mute">{fmtPrice(pick.price)}</td>
                      <td className="px-3 py-2 text-right font-mono text-emerald">
                        +{((runner.edge ?? 0) * 100).toFixed(1)}%
                      </td>
                      <td className="px-3 py-2 text-right text-ink-mute">
                        {r.resulted ? (r.won ? 'WON' : 'LOST') : '-'}
                      </td>
                      <td className="px-3 py-2 text-right font-mono text-ink-mute">
                        {r.resulted ? `${r.stake.toFixed(2)}u` : '-'}
                      </td>
                      <td
                        className={`px-3 py-2 text-right font-mono ${
                          !r.resulted ? 'text-ink-faint' : r.profit >= 0 ? 'text-emerald' : 'text-rose'
                        }`}
                      >
                        {r.resulted ? fmtUnits(r.profit) : '-'}
                      </td>
                    </tr>
                  )
                })}
              </tbody>
            </table>
          </div>
        )}
      </section>
    </div>
  )
}
