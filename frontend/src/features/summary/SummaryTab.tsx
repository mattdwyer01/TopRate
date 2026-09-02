import { useMemo } from 'react'
import type { Race, Runner } from '../../types/domain'
import { bushMeetingKeys, meetingKey } from '../../lib/meetings'
import { fmtPrice } from '../../lib/format'
import { StatTile } from '../../components/StatTile'

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

const PRICE_CAP = 26

interface Pick {
  race: Race
  runner: Runner
  tier: (typeof TIERS)[number]
}

/** Every not-yet-run, non-scratched runner that clears a tier's edge
 * threshold with a market price under the cap - assigned to the single
 * HIGHEST tier it clears (a big edge shouldn't also clutter the lower
 * tiers). Mirrors the exact "edge" WPR already computes (WPR's own price
 * vs the market's, see wpr_projection.compute_edge_scores) - no separate
 * blend, no re-derivation here.
 *
 * Scoped to today-or-later races only, and requires a live projectedWpr -
 * a small, permanent fraction of races never get a result recorded at all
 * (abandoned meetings, missing results feeds) and so never lose their
 * finishPosition==null "not yet run" look no matter how old they get.
 * Some of those, from before WPR's own price replaced the old edge blend,
 * still carry a stale edge value computed back when they WERE genuinely
 * upcoming - requiring today-or-later AND a current projection filters
 * both that staleness and any equally old abandoned-meeting noise out,
 * without needing to touch the backend's own "only touch today" data
 * model to do it. */
function collectPicks(races: Race[]): Pick[] {
  const todayStr = new Date().toISOString().slice(0, 10)
  const picks: Pick[] = []
  for (const race of races) {
    if (race.date < todayStr) continue
    for (const runner of race.runners) {
      if (runner.dataScratched || runner.finishPosition != null) continue
      if (runner.projectedWpr == null) continue
      if (runner.edge == null || runner.fixedWinPrice == null) continue
      if (runner.fixedWinPrice > PRICE_CAP) continue
      const tier = TIERS.find((t) => runner.edge! >= t.minEdge)
      if (!tier) continue
      picks.push({ race, runner, tier })
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

export function SummaryTab({ races, onSelectRace, showBush, onShowBushChange }: SummaryTabProps) {
  const scoped = useMemo(() => {
    if (showBush) return races
    const bushKeys = bushMeetingKeys(races)
    return races.filter((r) => !bushKeys.has(meetingKey(r)))
  }, [races, showBush])

  const picks = useMemo(() => collectPicks(scoped), [scoped])
  const byTier = useMemo(() => {
    const m = new Map<string, Pick[]>()
    for (const tier of TIERS) m.set(tier.key, [])
    for (const p of picks) m.get(p.tier.key)!.push(p)
    for (const list of m.values()) list.sort((a, b) => raceTime(a.race) - raceTime(b.race))
    return m
  }, [picks])

  return (
    <div className="flex flex-col gap-5">
      <div className="flex items-center justify-between">
        <div>
          <h2 className="text-base font-semibold text-ink">Betting Options</h2>
          <p className="mt-0.5 text-sm text-ink-mute">
            Runners where WPR rates them shorter than the market by a validated margin, in today's
            and upcoming races. Not a bet log or P&amp;L tracker - a live shortlist only.
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

      <div className="grid grid-cols-1 gap-3 sm:grid-cols-3">
        {TIERS.map((tier) => (
          <StatTile
            key={tier.key}
            label={tier.label}
            value={String(byTier.get(tier.key)?.length ?? 0)}
            sublabel={tier.backtest}
            tone={(byTier.get(tier.key)?.length ?? 0) > 0 ? 'positive' : 'muted'}
          />
        ))}
      </div>

      {TIERS.map((tier) => {
        const list = byTier.get(tier.key) ?? []
        return (
          <section key={tier.key} className="flex flex-col gap-2">
            <h3 className="text-sm font-semibold text-ink">
              {tier.label}{' '}
              <span className="font-normal text-ink-faint">(edge &ge; {(tier.minEdge * 100).toFixed(0)}%)</span>
            </h3>
            {list.length === 0 ? (
              <p className="rounded-md border border-line bg-panel px-3 py-2 text-sm text-ink-faint">
                No qualifying runners right now.
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
                    </tr>
                  </thead>
                  <tbody>
                    {list.map(({ race, runner }) => (
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
                        <td className="px-3 py-2 text-right font-mono text-ink">
                          {fmtPrice(runner.wprPrice)}
                        </td>
                        <td className="px-3 py-2 text-right font-mono text-ink-mute">
                          {fmtPrice(runner.fixedWinPrice)}
                        </td>
                        <td className="px-3 py-2 text-right font-mono text-emerald">
                          +{((runner.edge ?? 0) * 100).toFixed(1)}%
                        </td>
                      </tr>
                    ))}
                  </tbody>
                </table>
              </div>
            )}
          </section>
        )
      })}
    </div>
  )
}
