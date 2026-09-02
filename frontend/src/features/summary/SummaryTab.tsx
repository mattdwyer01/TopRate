import { useMemo, useState } from 'react'
import type { Race, Runner } from '../../types/domain'
import { bushMeetingKeys, meetingKey, todayIso } from '../../lib/meetings'
import { fmtPrice } from '../../lib/format'
import { computeEffectiveRace, type EffectiveRunner } from '../../lib/raceModel'
import { StatTile } from '../../components/StatTile'
import { Pill } from '../../components/Pill'

interface SummaryTabProps {
  races: Race[]
  onSelectRace: (raceId: string, date: string, runId?: string) => void
  showBush: boolean
  onShowBushChange: (v: boolean) => void
  deltas: Record<string, number>
  bases: Record<string, number>
  scratched: Set<string>
  priceBeta: number | null
}

const DEFAULT_BETA = 0.4

// Three qualifying tiers on WPR's own edge (model price vs market price,
// price<=$26 throughout) - thresholds and the backtest numbers below are
// from a genuinely leak-free walk-forward test (every population artifact
// fit on one date-half, scored purely on the other, both directions
// pooled - see wpr_bet_selection_leakfree_eval.py, chat Sep 2026), not a
// live guarantee. Cumulative, not exclusive: a pick that clears Value's
// 20% bar also shows up under Mid and High Volume (each tab is just "edge
// >= this threshold"), so High Volume is the broadest tab and Value the
// narrowest - per explicit user decision (Sep 2026), reversing the earlier
// single-highest-tier-only design. Ordered loosest-threshold-first to
// match that same left-to-right tab order (most inclusive tab first).
const TIERS = [
  {
    key: 'volume',
    label: 'High Volume',
    badgeLabel: 'VOLUME',
    minEdge: 0.05,
    backtest: 'edge ≥ 5%, price ≤ $26: n=5,994, ROI +31.4%, t=6.79 (leak-free backtest)',
    chipClass: 'bg-slate-bg text-slate',
    edgeClass: 'text-slate',
  },
  {
    key: 'mid',
    label: 'Mid',
    badgeLabel: 'MID',
    minEdge: 0.10,
    backtest: 'edge ≥ 10%, price ≤ $26: n=2,720, ROI +44.7%, t=6.68 (leak-free backtest)',
    chipClass: 'bg-indigo-bg text-indigo',
    edgeClass: 'text-indigo',
  },
  {
    key: 'value',
    label: 'Value',
    badgeLabel: 'VALUE',
    minEdge: 0.20,
    backtest: 'edge ≥ 20%, price ≤ $26: n=790, ROI +53.3%, t=4.55 (leak-free backtest)',
    chipClass: 'bg-amber-bg text-amber',
    edgeClass: 'text-amber',
  },
] as const

type Tier = (typeof TIERS)[number]

// Strongest-first, for finding the highest tier a given edge clears (used
// for the row badge - a Value-grade pick shown on the High Volume tab
// should still read as a Value pick, not a generic volume one).
const TIERS_BY_STRENGTH = [...TIERS].sort((a, b) => b.minEdge - a.minEdge)

function strongestTier(edge: number): Tier {
  return TIERS_BY_STRENGTH.find((t) => edge >= t.minEdge) ?? TIERS_BY_STRENGTH[TIERS_BY_STRENGTH.length - 1]
}

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
  price: number
  // WPR's own fair price/edge for this runner, recomputed client-side from
  // EFFECTIVE ratings (model projection, or a manually-entered base/delta
  // override) rather than trusted from the static server-computed
  // runner.wprPrice/edge fields - see collectPicks for why.
  wprPrice: number | null
  edge: number
}

const LOOSEST_MIN_EDGE = Math.min(...TIERS.map((t) => t.minEdge))

/** The price basis actually used to compute this runner's stored edge
 * (see toprate_daily.py's compute_edge_score/wpr_backfill_historical_
 * projections.py: fixed_win_price, falling back to starting_price_sp then
 * price_top) - matched here so a pick's qualification, displayed market
 * price, and P&L all agree on the same number. */
function marketPrice(runner: Runner): number | null {
  return runner.fixedWinPrice ?? runner.startingPrice ?? runner.postRaceTopPrice
}

interface RunnerEdge {
  modelProb: number
  marketProb: number
  edge: number
}

/** Re-derives WPR's own edge (model_prob - market_prob) client-side from
 * EFFECTIVE ratings, mirroring wpr_projection.compute_edge_scores exactly
 * (same beta, same "renormalise over just the priced-and-scored subset"
 * rule) - the static server-computed runner.edge can't be trusted here
 * since it's blind to manual overrides entered after the server last ran.
 * Empty (no edge) if fewer than 2 runners have both an effective
 * projection and a usable market price. */
function computeEffectiveEdges(
  runners: Runner[],
  effectiveByRunId: Record<string, EffectiveRunner>,
  beta: number,
): Record<string, RunnerEdge> {
  const rows = runners
    .map((r) => ({
      runId: r.runId,
      proj: effectiveByRunId[r.runId]?.effectiveProjectedWpr ?? null,
      price: marketPrice(r),
    }))
    .filter(
      (r): r is { runId: string; proj: number; price: number } =>
        r.proj != null && r.price != null && r.price > 1,
    )

  const result: Record<string, RunnerEdge> = {}
  if (rows.length < 2) return result

  const maxProj = Math.max(...rows.map((r) => r.proj))
  const expScores = rows.map((r) => Math.exp(beta * (r.proj - maxProj)))
  const sumExp = expScores.reduce((s, v) => s + v, 0)
  const invPrices = rows.map((r) => 1 / r.price)
  const sumInv = invPrices.reduce((s, v) => s + v, 0)

  rows.forEach((r, i) => {
    const modelProb = expScores[i] / sumExp
    const marketProb = invPrices[i] / sumInv
    result[r.runId] = { modelProb, marketProb, edge: modelProb - marketProb }
  })
  return result
}

/** Every non-scratched runner on the given date that clears the LOOSEST
 * tier's edge threshold with a market price under the cap. Tiers are
 * cumulative (see TIERS above), so a single flat pick list is collected
 * here and each tab just filters it down to its own threshold - a pick
 * that qualifies for Value necessarily qualifies for Mid and High Volume
 * too. A whole RACE is skipped unless every runner still standing (not
 * scratched, real or manually toggled) has a WPR value - either the
 * model's own projection, or a manually-entered base override - since a
 * race missing a rating for even one runner isn't a fair market to grade
 * anyone else's edge against. Entering a manual base for the missing
 * runner is what flips the race back to eligible, per explicit user
 * requirement (Sep 2026). Both the fair price shown and the edge used to
 * qualify a pick are recomputed from these EFFECTIVE ratings (see
 * computeEffectiveRace/computeEffectiveEdges) rather than trusted from the
 * server's static runner.wprPrice/edge, so a manual override actually
 * changes which picks qualify. Included regardless of whether the race has
 * resulted yet - the caller decides whether to show a live shortlist or a
 * P&L review from that alone. */
function collectPicks(
  races: Race[],
  date: string,
  deltas: Record<string, number>,
  bases: Record<string, number>,
  scratched: Set<string>,
  priceBeta: number | null,
): Pick[] {
  const beta = priceBeta ?? DEFAULT_BETA
  const picks: Pick[] = []
  for (const race of races) {
    if (race.date !== date) continue

    const effectiveScratched = new Set(scratched)
    for (const r of race.runners) {
      if (r.dataScratched) effectiveScratched.add(r.runId)
    }

    const effectiveByRunId = computeEffectiveRace(race.runners, deltas, bases, priceBeta, effectiveScratched)
    const active = race.runners.filter((r) => !effectiveScratched.has(r.runId))
    const eligible =
      active.length > 0 && active.every((r) => effectiveByRunId[r.runId]?.effectiveProjectedWpr != null)
    if (!eligible) continue

    const edges = computeEffectiveEdges(active, effectiveByRunId, beta)
    for (const runner of active) {
      const edgeRow = edges[runner.runId]
      if (!edgeRow) continue
      if (edgeRow.edge < LOOSEST_MIN_EDGE) continue
      const price = marketPrice(runner)
      if (price == null || price > PRICE_CAP) continue
      picks.push({
        race,
        runner,
        price,
        wprPrice: effectiveByRunId[runner.runId]?.effectivePrice ?? null,
        edge: edgeRow.edge,
      })
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

export function SummaryTab({
  races,
  onSelectRace,
  showBush,
  onShowBushChange,
  deltas,
  bases,
  scratched,
  priceBeta,
}: SummaryTabProps) {
  const [date, setDate] = useState(() => todayIso())
  const [activeTierKey, setActiveTierKey] = useState<Tier['key']>(TIERS[0].key)
  const activeTier = TIERS.find((t) => t.key === activeTierKey)!

  const scoped = useMemo(() => {
    if (showBush) return races
    const bushKeys = bushMeetingKeys(races)
    return races.filter((r) => !bushKeys.has(meetingKey(r)))
  }, [races, showBush])

  const allPicks = useMemo(
    () => collectPicks(scoped, date, deltas, bases, scratched, priceBeta),
    [scoped, date, deltas, bases, scratched, priceBeta],
  )
  const byTier = useMemo(() => {
    const m = new Map<string, Pick[]>()
    const sorted = [...allPicks].sort((a, b) => raceTime(a.race) - raceTime(b.race))
    for (const tier of TIERS) m.set(tier.key, sorted.filter((p) => p.edge >= tier.minEdge))
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
                  const tier = strongestTier(pick.edge)
                  return (
                    <tr
                      key={runner.runId}
                      className="cursor-pointer border-b border-line last:border-0 even:bg-line-soft/40 hover:bg-bg"
                      onClick={() => onSelectRace(race.raceId, race.date, runner.runId)}
                    >
                      <td className="px-3 py-2 text-ink-mute">{fmtRaceTime(race)}</td>
                      <td className="px-3 py-2 text-ink-mute">
                        {race.venue} R{race.raceNumber}
                      </td>
                      <td className="px-3 py-2">
                        <div className="flex items-center gap-2">
                          {runner.silkUrl ? (
                            <img
                              src={runner.silkUrl}
                              alt=""
                              className="h-7 w-7 flex-none rounded-sm border border-line-soft object-contain"
                            />
                          ) : (
                            <span className="h-7 w-7 flex-none" />
                          )}
                          <div className="min-w-0">
                            <div className="flex items-center gap-1.5">
                              <span className="truncate font-medium text-ink">{runner.horse}</span>
                              <span
                                className={`flex-none rounded px-1 py-0.5 text-[10px] font-semibold uppercase tracking-wide ${tier.chipClass}`}
                              >
                                {tier.badgeLabel}
                              </span>
                            </div>
                            {(runner.jockey || runner.trainer) && (
                              <div className="truncate text-xs text-ink-faint">
                                {runner.jockey}
                                {runner.jockey && runner.trainer ? ' / ' : ''}
                                {runner.trainer}
                              </div>
                            )}
                          </div>
                        </div>
                      </td>
                      <td className="px-3 py-2 text-right font-mono text-ink">{fmtPrice(pick.wprPrice)}</td>
                      <td className="px-3 py-2 text-right font-mono text-ink-mute">{fmtPrice(pick.price)}</td>
                      <td className={`px-3 py-2 text-right font-mono font-semibold ${tier.edgeClass}`}>
                        +{(pick.edge * 100).toFixed(1)}%
                      </td>
                      <td className="px-3 py-2 text-right">
                        {r.resulted ? (
                          r.won ? (
                            <span className="inline-flex items-center rounded bg-emerald-bg px-1.5 py-0.5 text-xs font-semibold text-emerald-deep">
                              WON
                            </span>
                          ) : (
                            <span className="text-xs font-medium text-ink-faint">LOST</span>
                          )
                        ) : (
                          <span className="text-ink-faint">-</span>
                        )}
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
